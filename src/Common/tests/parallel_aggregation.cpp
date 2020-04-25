#include <iostream>
#include <iomanip>
#include <mutex>
#include <atomic>

//#define DBMS_HASH_MAP_DEBUG_RESIZES

#include <Interpreters/AggregationCommon.h>

#include <Common/HashTable/HashMap.h>
#include <Common/HashTable/TwoLevelHashMap.h>
//#include <Common/HashTable/HashTableWithSmallLocks.h>
//#include <Common/HashTable/HashTableMerge.h>

#include <IO/ReadBufferFromFile.h>
#include <Compression/CompressedReadBuffer.h>

#include <Common/Stopwatch.h>
#include <Common/ThreadPool.h>


using Key = UInt64;
using Value = UInt64;

using Source = std::vector<Key>;
using SourceWithHash = std::vector<std::pair<Key, size_t>>;

using Map = HashMap<Key, Value>;
using MapTwoLevel = TwoLevelHashMap<Key, Value>;
using MapTwoLevel512 = TwoLevelHashMap<Key, Value, DefaultHash<Key>, TwoLevelHashTableGrower<>, HashTableAllocator, HashMapTable, 9>;
using MapTwoLevel128 = TwoLevelHashMap<Key, Value, DefaultHash<Key>, TwoLevelHashTableGrower<>, HashTableAllocator, HashMapTable, 7>;
using MapTwoLevel1024 = TwoLevelHashMap<Key, Value, DefaultHash<Key>, TwoLevelHashTableGrower<>, HashTableAllocator, HashMapTable, 10>;
using MapTwoLevel2048 = TwoLevelHashMap<Key, Value, DefaultHash<Key>, TwoLevelHashTableGrower<>, HashTableAllocator, HashMapTable, 11>;
using MapTwoLevel4096 = TwoLevelHashMap<Key, Value, DefaultHash<Key>, TwoLevelHashTableGrower<>, HashTableAllocator, HashMapTable, 12>;

struct SmallLock
{
    std::atomic<int> locked {false};

    bool try_lock()
    {
        int expected = 0;
        return locked.compare_exchange_strong(expected, 1, std::memory_order_acquire);
    }

    void unlock()
    {
        locked.store(0, std::memory_order_release);
    }
};

struct SmallLockBool
{
    std::atomic<bool> locked {false};

    bool try_lock()
    {
        bool expected = false;
        return locked.compare_exchange_strong(expected, true, std::memory_order_acquire);
    }

    void unlock()
    {
        locked.store(false, std::memory_order_release);
    }
};

struct SmallFlag
{
    std::atomic_flag locked;

    SmallFlag() { locked.clear(); }

    bool try_lock()
    {
        return !locked.test_and_set(std::memory_order_acquire);
    }

    void unlock()
    {
        locked.clear();
    }
};

struct SmallLockExt
{
    std::atomic<int> locked = 0;

    bool is_ready()
    {
        return locked == 1;
    }

    void set_ready()
    {
        locked = 1;
    }

    void set_done()
    {
        locked = 0;
    }
};

struct __attribute__((__aligned__(64))) AlignedSmallLock : public SmallLock
{
    char dummy[64 - sizeof(SmallLock)];
};

struct __attribute__((__aligned__(64))) AlignedSmallFlag : public SmallFlag
{
    char dummy[64 - sizeof(SmallFlag)];
};

struct __attribute__((__aligned__(64))) AlignedSmallLockBool : public SmallLockBool
{
    char dummy[64 - sizeof(SmallLockBool)];
};

struct __attribute__((__aligned__(64))) AlignedSmallLockExt : public SmallLockExt
{
    char dummy[64 - sizeof(SmallLockExt)];
};


using Mutex = std::mutex;


/*using MapSmallLocks = HashTableWithSmallLocks<
    Key,
    HashTableCellWithLock<
        Key,
        HashMapCell<Key, Value, DefaultHash<Key>> >,
    DefaultHash<Key>,
    HashTableGrower<21>,
    HashTableAllocator>;*/

static size_t getThreadNum(size_t hash, __uint128_t num_threads)
{
    return static_cast<size_t>((static_cast<__uint128_t>(hash) * num_threads) >> 64);
}

static void aggregate1(Map & map, Source::const_iterator begin, Source::const_iterator end)
{
    for (auto it = begin; it != end; ++it)
        ++map[*it];
}

#if !__clang__
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wmaybe-uninitialized"
#endif

static void aggregate12(Map & map, Source::const_iterator begin, Source::const_iterator end)
{
    Map::LookupResult found = nullptr;
    auto prev_it = end;
    for (auto it = begin; it != end; ++it)
    {
        if (prev_it != end && *it == *prev_it)
        {
            assert(found != nullptr);
            ++found->getMapped();
            continue;
        }
        prev_it = it;

        bool inserted;
        map.emplace(*it, found, inserted);
        assert(found != nullptr);
        ++found->getMapped();
    }
}

static void aggregate13(Map & map, Source::const_iterator begin,Source::const_iterator end,
                        std::vector<size_t> & hashes, size_t min_value, size_t max_value)
{
    Map::LookupResult found = nullptr;
    auto prev_it = end;
    for (auto it = begin; it != end; ++it)
    {
        if (hashes[it - begin] < min_value || hashes[it - begin] > max_value)
            continue;
        if (prev_it != end && *it == *prev_it)
        {
            assert(found != nullptr);
            ++found->getMapped();
            continue;
        }
        prev_it = it;

        bool inserted;
        map.emplace(*it, found, inserted, hashes[it - begin]);
        assert(found != nullptr);
        ++found->getMapped();
    }
}

static void aggregate14(Map & map, Source & data, std::vector<size_t> & hashes,
                        std::vector<size_t>::const_iterator begin,
                        std::vector<size_t>::const_iterator end)
{
    Map::LookupResult found = nullptr;
    auto prev_it = end;
    for (auto it = begin; it != end; ++it)
    {
        if (prev_it != end && data[*it] == data[*prev_it])
        {
            assert(found != nullptr);
            ++found->getMapped();
            continue;
        }
        prev_it = it;

        bool inserted;
        map.emplace(data[*it], found, inserted, hashes[*it]);
        assert(found != nullptr);
        ++found->getMapped();
    }
}

static void aggregate15(Map & map, Source::const_iterator begin,Source::const_iterator end,
                        size_t min_value, size_t max_value)
{
    Map::LookupResult found = nullptr;
    auto prev_it = end;
    for (auto it = begin; it != end; ++it)
    {
        size_t hash = map.hash(*it);
        if (hash < min_value || hash > max_value)
            continue;
        if (prev_it != end && *it == *prev_it)
        {
            assert(found != nullptr);
            ++found->getMapped();
            continue;
        }
        prev_it = it;

        bool inserted;
        map.emplace(*it, found, inserted, hash);
        assert(found != nullptr);
        ++found->getMapped();
    }
}

static void aggregate151(Map & map, Source::const_iterator begin,Source::const_iterator end,
                         size_t num_threads, size_t bucket)
{
    Map::LookupResult found = nullptr;
    auto prev_it = end;

    __uint128_t num_threads_128 = num_threads;
    for (auto it = begin; it != end; ++it)
    {
        size_t hash = map.hash(*it);
        size_t cur_bucket = getThreadNum(hash, num_threads_128);
        if (cur_bucket != bucket)
            continue;
        if (prev_it != end && *it == *prev_it)
        {
            assert(found != nullptr);
            ++found->getMapped();
            continue;
        }
        prev_it = it;

        bool inserted;
        map.emplace(*it, found, inserted, hash);
        assert(found != nullptr);
        ++found->getMapped();
    }
}

static void aggregate16(Map & map,
                        Source::const_iterator begin,
                        Source::const_iterator end)
{
    Map::LookupResult found = nullptr;
    auto prev_it = end;
    for (auto it = begin; it != end; ++it)
    {
        if (prev_it != end && *it == *prev_it)
        {
            assert(found != nullptr);
            ++found->getMapped();
            continue;
        }
        prev_it = it;

        bool inserted;
        map.emplace(*it, found, inserted);
        assert(found != nullptr);
        ++found->getMapped();
    }
}

static void aggregate161(Map & map,
                         std::vector<Key*>::const_iterator begin,
                         std::vector<Key*>::const_iterator end)
{
    Map::LookupResult found = nullptr;
    auto prev_it = end;
    for (auto it = begin; it != end; ++it)
    {
        if (prev_it != end && **it == **prev_it)
        {
            assert(found != nullptr);
            ++found->getMapped();
            continue;
        }
        prev_it = it;

        bool inserted;
        map.emplace(**it, found, inserted);
        assert(found != nullptr);
        ++found->getMapped();
    }
}

static void aggregate2(MapTwoLevel & map, Source::const_iterator begin, Source::const_iterator end)
{
    for (auto it = begin; it != end; ++it)
        ++map[*it];
}

static void aggregate22(MapTwoLevel & map, Source::const_iterator begin, Source::const_iterator end)
{
    MapTwoLevel::LookupResult found = nullptr;
    auto prev_it = end;
    for (auto it = begin; it != end; ++it)
    {
        if (prev_it != end && *it == *prev_it)
        {
            assert(found != nullptr);
            ++found->getMapped();
            continue;
        }
        prev_it = it;

        bool inserted;
        map.emplace(*it, found, inserted);
        assert(found != nullptr);
        ++found->getMapped();
    }
}

#if !__clang__
#pragma GCC diagnostic pop
#endif

static void merge17(Map * maps, size_t begin, size_t end) {
    for (size_t i = begin + 1; i < end; ++i)
        for (auto it = maps[i].begin(); it != maps[i].end(); ++it)
            maps[begin][it->getKey()] += it->getMapped();
}

static void merge2(MapTwoLevel * maps, size_t num_threads, size_t bucket)
{
    for (size_t i = 1; i < num_threads; ++i)
        for (auto it = maps[i].impls[bucket].begin(); it != maps[i].impls[bucket].end(); ++it)
            maps[0].impls[bucket][it->getKey()] += it->getMapped();
}

static void merge411(MapTwoLevel & globalMap, Map * maps, size_t num_threads, size_t bucket)
{
    for (size_t i = 0; i < num_threads; ++i)
        for (auto it = maps[i].begin(); it != maps[i].end(); ++it)
            if (globalMap.getBucketFromHash(globalMap.hash(it->getKey())) == bucket)
                globalMap.impls[bucket][it->getKey()] += it->getMapped();
}

static void aggregate3(Map & local_map, Map & global_map, Mutex & mutex, Source::const_iterator begin, Source::const_iterator end)
{
    static constexpr size_t threshold = 65536;

    for (auto it = begin; it != end; ++it)
    {
        if (local_map.size() < threshold)
        {
            ++local_map[*it];
            continue;
        }

        auto found = local_map.find(*it);
        if (found)
            ++found->getMapped();
        else
        {
            if (mutex.try_lock())
            {
                ++global_map[*it];
                mutex.unlock();
            }
            else
                ++local_map[*it];
        }
    }
}

static void aggregate33(Map & local_map, Map & global_map, Mutex & mutex, Source::const_iterator begin, Source::const_iterator end)
{
    static constexpr size_t threshold = 65536;

    for (auto it = begin; it != end; ++it)
    {
        Map::LookupResult found;
        bool inserted;
        local_map.emplace(*it, found, inserted);
        ++found->getMapped();

        if (inserted && local_map.size() == threshold)
        {
            std::lock_guard<Mutex> lock(mutex);
            for (auto & value_type : local_map)
                global_map[value_type.getKey()] += value_type.getMapped();

            local_map.clear();
        }
    }
}

static void aggregate4(Map & local_map, MapTwoLevel & global_map, Mutex * mutexes, Source::const_iterator begin, Source::const_iterator end)
{
    static constexpr size_t threshold = 65536;
    static constexpr size_t block_size = 8192;

    auto it = begin;
    while (it != end)
    {
        auto block_end = std::min(end, it + block_size);

        if (local_map.size() < threshold)
        {
            for (; it != block_end; ++it)
                ++local_map[*it];
        }
        else
        {
            for (; it != block_end; ++it)
            {
                auto found = local_map.find(*it);

                if (found)
                    ++found->getMapped();
                else
                {
                    size_t hash_value = global_map.hash(*it);
                    size_t bucket = global_map.getBucketFromHash(hash_value);

                    if (mutexes[bucket].try_lock())
                    {
                        ++global_map.impls[bucket][*it];
                        mutexes[bucket].unlock();
                    }
                    else
                        ++local_map[*it];
                }
            }
        }
    }
}

static void aggregate41(Map & local_map, MapTwoLevel & global_map, AlignedSmallLock * mutexes, Source::const_iterator begin, Source::const_iterator end)
{
    static constexpr size_t threshold = 65536;
    static constexpr size_t block_size = 8192;

    auto it = begin;
    while (it != end)
    {
        auto block_end = std::min(end, it + block_size);

        if (local_map.size() < threshold)
        {
            for (; it != block_end; ++it)
                ++local_map[*it];
        }
        else
        {
            for (; it != block_end; ++it)
            {
                auto found = local_map.find(*it);

                if (found)
                    ++found->getMapped();
                else
                {
                    size_t hash_value = global_map.hash(*it);
                    size_t bucket = global_map.getBucketFromHash(hash_value);

                    if (mutexes[bucket].try_lock())
                    {
                        ++global_map.impls[bucket][*it];
                        mutexes[bucket].unlock();
                    }
                    else
                        ++local_map[*it];
                }
            }
        }
    }
}

static void aggregate412(Map & local_map, std::vector<std::vector<Key>> & buffer, std::vector<size_t> buffer_idx,
                         MapTwoLevel & global_map, AlignedSmallLock * mutexes, Source::const_iterator begin, Source::const_iterator end)
{
    static constexpr size_t threshold = 65536;
    static constexpr size_t block_size = 8192;

    auto it = begin;
    while (it != end)
    {
        auto block_end = std::min(end, it + block_size);

        if (local_map.size() < threshold)
        {
            for (; it != block_end; ++it)
                ++local_map[*it];
        }
        else
        {
            for (; it != block_end; ++it)
            {
                auto found = local_map.find(*it);

                if (found)
                    ++found->getMapped();
                else
                {
                    size_t hash_value = global_map.hash(*it);
                    size_t bucket = global_map.getBucketFromHash(hash_value);

                    if (mutexes[bucket].try_lock())
                    {
                        if (buffer_idx[bucket] < buffer[bucket].size())
                        {
                            for (size_t j = buffer_idx[bucket]; j < buffer[bucket].size(); ++j)
                                ++global_map.impls[bucket][buffer[bucket][j]];
                            buffer_idx[bucket] = buffer[bucket].size();
                        }
                        ++global_map.impls[bucket][*it];
                        mutexes[bucket].unlock();
                    }
                    else
                        buffer[bucket].push_back(*it);
                }
            }
        }
    }
    for (size_t i = 0; i < MapTwoLevel::NUM_BUCKETS; ++i)
        for (size_t j = buffer_idx[i]; j < buffer[i].size(); ++j)
            ++local_map[buffer[i][j]];
}

static void aggregate413(Map & local_map, std::vector<std::vector<Key>> & buffer, std::vector<size_t> buffer_idx,
                         MapTwoLevel & global_map, AlignedSmallLock * mutexes, Source::const_iterator begin, Source::const_iterator end)
{
    static constexpr size_t threshold = 16384;
    static constexpr size_t block_size = 4096;

    auto it = begin;
    while (it != end)
    {
        auto block_end = std::min(end, it + block_size);

        if (local_map.size() < threshold)
        {
            for (; it != block_end; ++it)
                ++local_map[*it];
        }
        else
        {
            for (; it != block_end; ++it)
            {
                auto found = local_map.find(*it);

                if (found)
                    ++found->getMapped();
                else
                {
                    size_t hash_value = global_map.hash(*it);
                    size_t bucket = global_map.getBucketFromHash(hash_value);

                    if (mutexes[bucket].try_lock())
                    {
                        if (buffer_idx[bucket] < buffer[bucket].size())
                        {
                            for (size_t j = buffer_idx[bucket]; j < buffer[bucket].size(); ++j)
                                ++global_map.impls[bucket][buffer[bucket][j]];
                            buffer_idx[bucket] = buffer[bucket].size();
                        }
                        ++global_map.impls[bucket][*it];
                        mutexes[bucket].unlock();
                    }
                    else
                        buffer[bucket].push_back(*it);
                }
            }
        }
    }
    for (size_t i = 0; i < MapTwoLevel::NUM_BUCKETS; ++i)
        for (size_t j = buffer_idx[i]; j < buffer[i].size(); ++j)
            ++local_map[buffer[i][j]];
}

static void aggregate414(Map & local_map, std::vector<std::vector<Key>> & buffer, std::vector<size_t> buffer_idx,
                         MapTwoLevel512 & global_map, AlignedSmallLock * mutexes, Source::const_iterator begin, Source::const_iterator end)
{
    static constexpr size_t threshold = 16384;
    static constexpr size_t block_size = 4096;

    auto it = begin;
    while (it != end)
    {
        auto block_end = std::min(end, it + block_size);

        if (local_map.size() < threshold)
        {
            for (; it != block_end; ++it)
                ++local_map[*it];
        }
        else
        {
            for (; it != block_end; ++it)
            {
                auto found = local_map.find(*it);

                if (found)
                    ++found->getMapped();
                else
                {
                    size_t hash_value = global_map.hash(*it);
                    size_t bucket = global_map.getBucketFromHash(hash_value);

                    if (mutexes[bucket].try_lock())
                    {
                        if (buffer_idx[bucket] < buffer[bucket].size())
                        {
                            for (size_t j = buffer_idx[bucket]; j < buffer[bucket].size(); ++j)
                                ++global_map.impls[bucket][buffer[bucket][j]];
                            buffer_idx[bucket] = buffer[bucket].size();
                        }
                        ++global_map.impls[bucket][*it];
                        mutexes[bucket].unlock();
                    }
                    else
                        buffer[bucket].push_back(*it);
                }
            }
        }
    }
    for (size_t i = 0; i < MapTwoLevel512::NUM_BUCKETS; ++i)
        for (size_t j = buffer_idx[i]; j < buffer[i].size(); ++j)
            ++local_map[buffer[i][j]];
}

static void aggregate415(Map & local_map, std::vector<std::vector<Key>> & buffer, std::vector<size_t> buffer_idx,
                         MapTwoLevel128 & global_map, AlignedSmallLock * mutexes, Source::const_iterator begin, Source::const_iterator end)
{
    static constexpr size_t threshold = 16384;
    static constexpr size_t block_size = 4096;

    auto it = begin;
    while (it != end)
    {
        auto block_end = std::min(end, it + block_size);

        if (local_map.size() < threshold)
        {
            for (; it != block_end; ++it)
                ++local_map[*it];
        }
        else
        {
            for (; it != block_end; ++it)
            {
                auto found = local_map.find(*it);

                if (found)
                    ++found->getMapped();
                else
                {
                    size_t hash_value = global_map.hash(*it);
                    size_t bucket = global_map.getBucketFromHash(hash_value);

                    if (mutexes[bucket].try_lock())
                    {
                        if (buffer_idx[bucket] < buffer[bucket].size())
                        {
                            for (size_t j = buffer_idx[bucket]; j < buffer[bucket].size(); ++j)
                                ++global_map.impls[bucket][buffer[bucket][j]];
                            buffer_idx[bucket] = buffer[bucket].size();
                        }
                        ++global_map.impls[bucket][*it];
                        mutexes[bucket].unlock();
                    }
                    else
                        buffer[bucket].push_back(*it);
                }
            }
        }
    }
    for (size_t i = 0; i < MapTwoLevel128::NUM_BUCKETS; ++i)
        for (size_t j = buffer_idx[i]; j < buffer[i].size(); ++j)
            ++local_map[buffer[i][j]];
}

static void aggregate416(Map & local_map, std::vector<std::vector<Key>> & buffer, std::vector<size_t> buffer_idx,
                         MapTwoLevel1024 & global_map, AlignedSmallLock * mutexes, Source::const_iterator begin, Source::const_iterator end)
{
    static constexpr size_t threshold = 16384;
    static constexpr size_t block_size = 4096;

    auto it = begin;
    while (it != end)
    {
        auto block_end = std::min(end, it + block_size);

        if (local_map.size() < threshold)
        {
            for (; it != block_end; ++it)
                ++local_map[*it];
        }
        else
        {
            for (; it != block_end; ++it)
            {
                auto found = local_map.find(*it);

                if (found)
                    ++found->getMapped();
                else
                {
                    size_t hash_value = global_map.hash(*it);
                    size_t bucket = global_map.getBucketFromHash(hash_value);

                    if (mutexes[bucket].try_lock())
                    {
                        if (buffer_idx[bucket] < buffer[bucket].size())
                        {
                            for (size_t j = buffer_idx[bucket]; j < buffer[bucket].size(); ++j)
                                ++global_map.impls[bucket][buffer[bucket][j]];
                            buffer_idx[bucket] = buffer[bucket].size();
                        }
                        ++global_map.impls[bucket][*it];
                        mutexes[bucket].unlock();
                    }
                    else
                        buffer[bucket].push_back(*it);
                }
            }
        }
    }
    for (size_t i = 0; i < MapTwoLevel1024::NUM_BUCKETS; ++i)
        for (size_t j = buffer_idx[i]; j < buffer[i].size(); ++j)
            ++local_map[buffer[i][j]];
}

static void aggregate417(Map & local_map, std::vector<std::vector<Key>> & buffer, std::vector<size_t> buffer_idx,
                         MapTwoLevel2048 & global_map, AlignedSmallLock * mutexes, Source::const_iterator begin, Source::const_iterator end)
{
    static constexpr size_t threshold = 16384;
    static constexpr size_t block_size = 4096;

    auto it = begin;
    while (it != end)
    {
        auto block_end = std::min(end, it + block_size);

        if (local_map.size() < threshold)
        {
            for (; it != block_end; ++it)
                ++local_map[*it];
        }
        else
        {
            for (; it != block_end; ++it)
            {
                auto found = local_map.find(*it);

                if (found)
                    ++found->getMapped();
                else
                {
                    size_t hash_value = global_map.hash(*it);
                    size_t bucket = global_map.getBucketFromHash(hash_value);

                    if (mutexes[bucket].try_lock())
                    {
                        if (buffer_idx[bucket] < buffer[bucket].size())
                        {
                            for (size_t j = buffer_idx[bucket]; j < buffer[bucket].size(); ++j)
                                ++global_map.impls[bucket][buffer[bucket][j]];
                            buffer_idx[bucket] = buffer[bucket].size();
                        }
                        ++global_map.impls[bucket][*it];
                        mutexes[bucket].unlock();
                    }
                    else
                        buffer[bucket].push_back(*it);
                }
            }
        }
    }
    for (size_t i = 0; i < MapTwoLevel2048::NUM_BUCKETS; ++i)
        for (size_t j = buffer_idx[i]; j < buffer[i].size(); ++j)
            ++local_map[buffer[i][j]];
}

static void aggregate418(Map & local_map, std::vector<std::vector<Key>> & buffer, std::vector<size_t> buffer_idx,
                         MapTwoLevel4096 & global_map, AlignedSmallLock * mutexes, Source::const_iterator begin, Source::const_iterator end)
{
    static constexpr size_t threshold = 16384;
    static constexpr size_t block_size = 4096;

    auto it = begin;
    while (it != end)
    {
        auto block_end = std::min(end, it + block_size);

        if (local_map.size() < threshold)
        {
            for (; it != block_end; ++it)
                ++local_map[*it];
        }
        else
        {
            for (; it != block_end; ++it)
            {
                auto found = local_map.find(*it);

                if (found)
                    ++found->getMapped();
                else
                {
                    size_t hash_value = global_map.hash(*it);
                    size_t bucket = global_map.getBucketFromHash(hash_value);

                    if (mutexes[bucket].try_lock())
                    {
                        if (buffer_idx[bucket] < buffer[bucket].size())
                        {
                            for (size_t j = buffer_idx[bucket]; j < buffer[bucket].size(); ++j)
                                ++global_map.impls[bucket][buffer[bucket][j]];
                            buffer_idx[bucket] = buffer[bucket].size();
                        }
                        ++global_map.impls[bucket][*it];
                        mutexes[bucket].unlock();
                    }
                    else
                        buffer[bucket].push_back(*it);
                }
            }
        }
    }
    for (size_t i = 0; i < MapTwoLevel4096::NUM_BUCKETS; ++i)
        for (size_t j = buffer_idx[i]; j < buffer[i].size(); ++j)
            ++local_map[buffer[i][j]];
}

static void aggregate4181(Map & local_map, std::vector<std::vector<Key>> & buffer, std::vector<size_t> & buffer_idx,
                         MapTwoLevel4096 & global_map, AlignedSmallLock * mutexes, Source::const_iterator begin, Source::const_iterator end)
{
    static constexpr size_t threshold = 4096;
    static constexpr size_t block_size = 1024;

    auto it = begin;
    while (it != end)
    {
        auto block_end = std::min(end, it + block_size);

        if (local_map.size() < threshold)
        {
            for (; it != block_end; ++it)
                ++local_map[*it];
        }
        else
        {
            for (; it != block_end; ++it)
            {
                auto found = local_map.find(*it);

                if (found)
                    ++found->getMapped();
                else
                {
                    size_t hash_value = global_map.hash(*it);
                    size_t bucket = global_map.getBucketFromHash(hash_value);

                    if (mutexes[bucket].try_lock())
                    {
                        if (buffer_idx[bucket] < buffer[bucket].size())
                        {
                            for (size_t j = buffer_idx[bucket]; j < buffer[bucket].size(); ++j)
                                ++global_map.impls[bucket][buffer[bucket][j]];
                            buffer_idx[bucket] = buffer[bucket].size();
                        }
                        ++global_map.impls[bucket][*it];
                        mutexes[bucket].unlock();
                    }
                    else
                        buffer[bucket].push_back(*it);
                }
            }
        }
    }
    for (size_t i = 0; i < MapTwoLevel4096::NUM_BUCKETS; ++i)
        for (size_t j = buffer_idx[i]; j < buffer[i].size(); ++j)
            ++local_map[buffer[i][j]];
}

static void aggregate42(Map & local_map, Map * global_maps, AlignedSmallLock * mutexes,
                        Source::const_iterator begin, Source::const_iterator end, size_t num_threads)
{
    static constexpr size_t threshold = 65536;
    static constexpr size_t block_size = 8192;

    auto it = begin;
    __uint128_t num_threads_128 = num_threads;
    while (it != end)
    {
        auto block_end = std::min(end, it + block_size);

        if (local_map.size() < threshold)
        {
            for (; it != block_end; ++it)
                ++local_map[*it];
        }
        else
        {
            for (; it != block_end; ++it)
            {
                auto hash = local_map.hash(*it);
                auto found = local_map.find(*it, hash);

                if (found)
                    ++found->getMapped();
                else
                {
                    size_t cur_bucket = getThreadNum(hash, num_threads_128);
                    if (mutexes[cur_bucket].try_lock())
                    {
                        ++global_maps[cur_bucket][*it];
                        mutexes[cur_bucket].unlock();
                    }
                    else
                        ++local_map[*it];
                }
            }
        }
    }
}

static void aggregate43(Map & local_map,
                        Map & global_map,
                        std::vector<std::vector<std::list<Key>>> & buffer,
                        std::vector<std::vector<std::pair<std::list<Key>::iterator, std::list<Key>::iterator>>> & buffer_ranges,
                        std::vector<std::vector<AlignedSmallLockExt>> & mutexes,
                        Source::const_iterator begin,
                        Source::const_iterator end,
                        size_t cur_thread,
                        size_t num_threads)
{
    static constexpr size_t threshold = 16384;
    static constexpr size_t block_size = 4096;

    __uint128_t num_threads_128 = num_threads;
    auto it = begin;
    while (it != end)
    {
        auto block_end = std::min(end, it + block_size);

        if (local_map.size() < threshold)
        {
            for (; it != block_end; ++it)
            {
                size_t hash_value = global_map.hash(*it);
                size_t bucket = getThreadNum(hash_value, num_threads_128);

                if (bucket == cur_thread)
                    ++global_map[*it];
                else
                    ++local_map[*it];
            }
        }
        else
        {
            for (; it != block_end; ++it)
            {
                size_t hash_value = global_map.hash(*it);
                size_t bucket = getThreadNum(hash_value, num_threads_128);

                if (bucket == cur_thread)
                {
                    ++global_map[*it];
                    continue;
                }

                auto found = local_map.find(*it);
                if (found)
                    ++found->getMapped();
                else
                    buffer[cur_thread][bucket].push_back(*it);
            }

            for (size_t i = 0; i < num_threads; ++i)
                if (i != cur_thread && !buffer[cur_thread][i].empty() &&
                    buffer_ranges[cur_thread][i].second != std::prev(buffer[cur_thread][i].end()) &&
                    !mutexes[cur_thread][i].is_ready())
                {
                    buffer_ranges[cur_thread][i] = {std::next(buffer_ranges[cur_thread][i].second), std::prev(buffer[cur_thread][i].end())};
                    mutexes[cur_thread][i].set_ready();
                }
        }

        for (size_t i = 0; i < num_threads; ++i)
        {
            if (i != cur_thread && mutexes[i][cur_thread].is_ready())
            {
                auto iter = buffer_ranges[i][cur_thread].first;
                auto iter_end = buffer_ranges[i][cur_thread].second;
                while (iter != iter_end)
                {
                    ++global_map[*iter];
                    ++iter;
                }
                ++global_map[*iter];
                mutexes[i][cur_thread].set_done();
            }
        }
    }
}

static void aggregate431(Map & local_map,
                         Map & global_map,
                         std::vector<std::vector<std::list<Key>>> & buffer,
                         std::vector<std::vector<std::pair<std::list<Key>::iterator, std::list<Key>::iterator>>> & buffer_ranges,
                         std::vector<std::vector<AlignedSmallLockExt>> & mutexes,
                         Source::const_iterator begin,
                         Source::const_iterator end,
                         size_t cur_thread,
                         size_t num_threads)
{
    static constexpr size_t threshold = 16384;
    static constexpr size_t block_size = 8192;

    __uint128_t num_threads_128 = num_threads;
    auto it = begin;
    while (it != end)
    {
        auto block_end = std::min(end, it + block_size);

        if (local_map.size() < threshold)
        {
            for (; it != block_end; ++it)
            {
                size_t hash_value = global_map.hash(*it);
                size_t bucket = getThreadNum(hash_value, num_threads_128);

                if (bucket == cur_thread)
                    ++global_map[*it];
                else
                    ++local_map[*it];
            }
        }
        else
        {
            for (; it != block_end; ++it)
            {
                size_t hash_value = global_map.hash(*it);
                size_t bucket = getThreadNum(hash_value, num_threads_128);

                if (bucket == cur_thread)
                {
                    ++global_map[*it];
                    continue;
                }

                auto found = local_map.find(*it);
                if (found)
                    ++found->getMapped();
                else
                    buffer[cur_thread][bucket].push_back(*it);
            }

            for (size_t i = 0; i < num_threads; ++i)
                if (i != cur_thread && !buffer[cur_thread][i].empty() &&
                    buffer_ranges[cur_thread][i].second != std::prev(buffer[cur_thread][i].end()) &&
                    !mutexes[cur_thread][i].is_ready())
                {
                    buffer_ranges[cur_thread][i] = {std::next(buffer_ranges[cur_thread][i].second), std::prev(buffer[cur_thread][i].end())};
                    mutexes[cur_thread][i].set_ready();
                }
        }

        for (size_t i = 0; i < num_threads; ++i)
        {
            if (i != cur_thread && mutexes[i][cur_thread].is_ready())
            {
                auto iter = buffer_ranges[i][cur_thread].first;
                auto iter_end = buffer_ranges[i][cur_thread].second;
                while (iter != iter_end)
                {
                    ++global_map[*iter];
                    ++iter;
                }
                ++global_map[*iter];
                mutexes[i][cur_thread].set_done();
            }
        }
    }
}

static void merge431(Map & global_map,
                     std::vector<std::vector<std::list<Key>>> & buffers,
                     std::vector<std::vector<std::pair<std::list<Key>::iterator, std::list<Key>::iterator>>> & buffer_ranges,
                     std::vector<std::vector<AlignedSmallLockExt>> & mutexes,
                     size_t cur_thread,
                     size_t num_threads)
{
    for (size_t i = 0; i < num_threads; ++i)
        if (i != cur_thread && !buffers[i][cur_thread].empty() &&
            (buffer_ranges[i][cur_thread].second != std::prev(buffers[i][cur_thread].end()) || mutexes[i][cur_thread].is_ready()))
        {
            auto it = mutexes[i][cur_thread].is_ready() ? buffer_ranges[i][cur_thread].first : std::next(buffer_ranges[i][cur_thread].second);
            while (it != buffers[i][cur_thread].end())
            {
                ++global_map[*it];
                ++it;
            }
        }
}

/*
void aggregate5(Map & local_map, MapSmallLocks & global_map, Source::const_iterator begin, Source::const_iterator end)
{
    static constexpr size_t threshold = 65536;

    for (auto it = begin; it != end; ++it)
    {
        Map::iterator found = local_map.find(*it);

        if (found != local_map.end())
            ++found->second;
        else if (local_map.size() < threshold)
            ++local_map[*it];    /// TODO You could do one lookup, not two.
        else
        {
            SmallScopedLock lock;
            MapSmallLocks::iterator insert_it;
            bool inserted;

            if (global_map.tryEmplace(*it, insert_it, inserted, lock))
                ++insert_it->second;
            else
                ++local_map[*it];
        }
    }
}*/


int main(int argc, char ** argv)
{
    size_t n = std::stol(argv[1]);
    size_t num_threads = std::stol(argv[2]);
    size_t method = argc <= 3 ? 0 : std::stol(argv[3]);

    std::cerr << std::fixed << std::setprecision(2);

    ThreadPool pool(num_threads);

    Source data(n);

    {
        Stopwatch watch;
        DB::ReadBufferFromFileDescriptor in1(STDIN_FILENO);
        DB::CompressedReadBuffer in2(in1);

        //in2.readStrict(reinterpret_cast<char*>(data.data()), sizeof(data[0]) * n);
        for (size_t i = 0; i < n; ++i) {
            DB::readBinary(data[i], in2);
        }

        watch.stop();
        std::cerr << std::fixed << std::setprecision(2)
            << "Vector. Size: " << n
            << ", elapsed: " << watch.elapsedSeconds()
            << " (" << n / watch.elapsedSeconds() << " elem/sec.)"
            << std::endl << std::endl;
    }

    if (!method || method == 1)
    {
        /** Option 1.
          * In different threads, we aggregate independently into different hash tables.
          * Then merge them together.
          */

        std::vector<Map> maps(num_threads);

        Stopwatch watch;

        for (size_t i = 0; i < num_threads; ++i)
            pool.scheduleOrThrowOnError([&, i] { aggregate1(
                std::ref(maps[i]),
                data.begin() + (data.size() * i) / num_threads,
                data.begin() + (data.size() * (i + 1)) / num_threads); });

        pool.wait();

        watch.stop();
        double time_aggregated = watch.elapsedSeconds();
        std::cerr
            << "Aggregated in " << time_aggregated
            << " (" << n / time_aggregated << " elem/sec.)"
            << std::endl;

        size_t size_before_merge = 0;
        std::cerr << "Sizes: ";
        for (size_t i = 0; i < num_threads; ++i)
        {
            std::cerr << (i == 0 ? "" : ", ") << maps[i].size();
            size_before_merge += maps[i].size();
        }
        std::cerr << std::endl;

        watch.restart();

        for (size_t i = 1; i < num_threads; ++i)
            for (auto it = maps[i].begin(); it != maps[i].end(); ++it)
                maps[0][it->getKey()] += it->getMapped();

        watch.stop();
        double time_merged = watch.elapsedSeconds();
        std::cerr
            << "Merged in " << time_merged
            << " (" << size_before_merge / time_merged << " elem/sec.)"
            << std::endl;

        double time_total = time_aggregated + time_merged;
        std::cerr
            << "Total in " << time_total
            << " (" << n / time_total << " elem/sec.)"
            << std::endl;
        std::cerr << "Size: " << maps[0].size() << std::endl << std::endl;
    }

    if (!method || method == 12)
    {
        /** The same, but with optimization for consecutive identical values.
          */

        std::vector<Map> maps(num_threads);

        Stopwatch watch;

        for (size_t i = 0; i < num_threads; ++i)
            pool.scheduleOrThrowOnError([&, i] { aggregate12(
                                    std::ref(maps[i]),
                                    data.begin() + (data.size() * i) / num_threads,
                                    data.begin() + (data.size() * (i + 1)) / num_threads); });

        pool.wait();

        watch.stop();
        double time_aggregated = watch.elapsedSeconds();
        std::cerr
        << "Aggregated in " << time_aggregated
        << " (" << n / time_aggregated << " elem/sec.)"
        << std::endl;

        size_t size_before_merge = 0;
        std::cerr << "Sizes: ";
        for (size_t i = 0; i < num_threads; ++i)
        {
            std::cerr << (i == 0 ? "" : ", ") << maps[i].size();
            size_before_merge += maps[i].size();
        }
        std::cerr << std::endl;

        watch.restart();

        for (size_t i = 1; i < num_threads; ++i)
            for (auto it = maps[i].begin(); it != maps[i].end(); ++it)
                maps[0][it->getKey()] += it->getMapped();

        watch.stop();

        double time_merged = watch.elapsedSeconds();
        std::cerr
        << "Merged in " << time_merged
        << " (" << size_before_merge / time_merged << " elem/sec.)"
        << std::endl;

        double time_total = time_aggregated + time_merged;
        std::cerr
        << "Total in " << time_total
        << " (" << n / time_total << " elem/sec.)"
        << std::endl;
        std::cerr << "Size: " << maps[0].size() << std::endl << std::endl;
    }

    if (!method || method == 11)
    {
        /** Option 11.
          * Same as option 1, but with merge, the order of the cycles is changed,
          *  which potentially can give better cache locality.
          *
          * In practice, there is no difference.
          */

        std::vector<Map> maps(num_threads);

        Stopwatch watch;

        for (size_t i = 0; i < num_threads; ++i)
            pool.scheduleOrThrowOnError([&, i] { aggregate1(
                std::ref(maps[i]),
                data.begin() + (data.size() * i) / num_threads,
                data.begin() + (data.size() * (i + 1)) / num_threads); });

        pool.wait();

        watch.stop();
        double time_aggregated = watch.elapsedSeconds();
        std::cerr
        << "Aggregated in " << time_aggregated
        << " (" << n / time_aggregated << " elem/sec.)"
        << std::endl;

        size_t size_before_merge = 0;
        std::cerr << "Sizes: ";
        for (size_t i = 0; i < num_threads; ++i)
        {
            std::cerr << (i == 0 ? "" : ", ") << maps[i].size();
            size_before_merge += maps[i].size();
        }
        std::cerr << std::endl;

        watch.restart();

        std::vector<Map::iterator> iterators(num_threads);
        for (size_t i = 1; i < num_threads; ++i)
            iterators[i] = maps[i].begin();

        while (true)
        {
            bool finish = true;
            for (size_t i = 1; i < num_threads; ++i)
            {
                if (iterators[i] == maps[i].end())
                    continue;

                finish = false;
                maps[0][iterators[i]->getKey()] += iterators[i]->getMapped();
                ++iterators[i];
            }

            if (finish)
                break;
        }

        watch.stop();
        double time_merged = watch.elapsedSeconds();
        std::cerr
        << "Merged in " << time_merged
        << " (" << size_before_merge / time_merged << " elem/sec.)"
        << std::endl;

        double time_total = time_aggregated + time_merged;
        std::cerr
        << "Total in " << time_total
        << " (" << n / time_total << " elem/sec.)"
        << std::endl;
        std::cerr << "Size: " << maps[0].size() << std::endl << std::endl;
    }

    if (!method || method == 13)
    {
        /** Option 13.
         * Precalculate hash values and divide them into n groups for each thread.
         * In different threads, we aggregate independently into different hash tables.
         * We should not to merge them because each table contains different keys.
         */

        std::vector<Map> maps(num_threads);

        Stopwatch watch;

        std::vector<size_t> hashes(n);
        hashes[0] = maps[0].hash(data[0]);
        size_t min_hash = hashes[0];
        size_t max_hash = hashes[0];
        for (size_t i = 1; i < n; ++i) {
            hashes[i] = maps[0].hash(data[i]);
            max_hash = std::max(max_hash, hashes[i]);
            min_hash = std::min(min_hash, hashes[i]);
        }

        for (size_t i = 0; i < num_threads; ++i)
        {
            pool.scheduleOrThrowOnError([&, i] {
                aggregate13(
                    std::ref(maps[i]),
                    data.begin(),
                    data.end(),
                    std::ref(hashes),
                    min_hash + (max_hash - min_hash) / num_threads * i,
                    i + 1 == num_threads ? max_hash : min_hash + (max_hash - min_hash) / num_threads * (i + 1) - 1);
            });
        }

        pool.wait();

        watch.stop();
        double time_aggregated = watch.elapsedSeconds();
        std::cerr
            << "Aggregated in " << time_aggregated
            << " (" << n / time_aggregated << " elem/sec.)"
            << std::endl;

        size_t size_before_merge = 0;
        std::cerr << "Sizes: ";
        for (size_t i = 0; i < num_threads; ++i)
        {
            std::cerr << (i == 0 ? "" : ", ") << maps[i].size();
            size_before_merge += maps[i].size();
        }
        std::cerr << std::endl;

        double time_total = time_aggregated;
        std::cerr
            << "Total in " << time_total
            << " (" << n / time_total << " elem/sec.)"
            << std::endl;
        std::cerr << "Size: " << size_before_merge << std::endl << std::endl;
    }

    if (!method || method == 14)
    {
        /** Option 14.
         * Same as option 13 but group values to different vectors (some more memory but less operations).
         * Zero cache locality so it works always slower than option 13.
         */

        std::vector<Map> maps(num_threads);

        Stopwatch watch;

        std::vector<size_t> hashes(n);
        hashes[0] = maps[0].hash(data[0]);
        size_t min_hash = hashes[0];
        size_t max_hash = hashes[0];
        for (size_t i = 1; i < n; ++i) {
            hashes[i] = maps[0].hash(data[i]);
            max_hash = std::max(max_hash, hashes[i]);
            min_hash = std::min(min_hash, hashes[i]);
        }

        std::vector<std::vector<size_t>> data_by_thread(num_threads);
        size_t block_size = (max_hash - min_hash) / num_threads;
        for (size_t i = 0; i < n; ++i) {
            data_by_thread[std::min(num_threads - 1, (hashes[i] - min_hash) / block_size)].push_back(i);
        }

        for (size_t i = 0; i < num_threads; ++i)
        {
            pool.scheduleOrThrowOnError([&, i] {
                aggregate14(
                    std::ref(maps[i]),
                    std::ref(data),
                    std::ref(hashes),
                    data_by_thread[i].begin(),
                    data_by_thread[i].end());
            });
        }

        pool.wait();

        watch.stop();
        double time_aggregated = watch.elapsedSeconds();
        std::cerr
            << "Aggregated in " << time_aggregated
            << " (" << n / time_aggregated << " elem/sec.)"
            << std::endl;

        size_t size_before_merge = 0;
        std::cerr << "Sizes: ";
        for (size_t i = 0; i < num_threads; ++i)
        {
            std::cerr << (i == 0 ? "" : ", ") << maps[i].size();
            size_before_merge += maps[i].size();
        }
        std::cerr << std::endl;

        double time_total = time_aggregated;
        std::cerr
            << "Total in " << time_total
            << " (" << n / time_total << " elem/sec.)"
            << std::endl;
        std::cerr << "Size: " << size_before_merge << std::endl << std::endl;
    }

    if (!method || method == 15)
    {
        /** Option 15.
         * Same as option 13 but works faster in all cases.
         */

        std::vector<Map> maps(num_threads);

        Stopwatch watch;

        size_t hash = maps[0].hash(data[0]);
        size_t min_hash = hash;
        size_t max_hash = min_hash;

        for (size_t i = 1; i < n; ++i) {
            hash = maps[0].hash(data[i]);
            max_hash = std::max(max_hash, hash);
            min_hash = std::min(min_hash, hash);
        }

        for (size_t i = 0; i < num_threads; ++i)
        {
            pool.scheduleOrThrowOnError([&, i] {
                aggregate15(
                    std::ref(maps[i]),
                    data.begin(),
                    data.end(),
                    min_hash + (max_hash - min_hash) / num_threads * i,
                    i + 1 == num_threads ? max_hash : min_hash + (max_hash - min_hash) / num_threads * (i + 1) - 1);
            });
        }

        pool.wait();

        watch.stop();
        double time_aggregated = watch.elapsedSeconds();
        std::cerr
            << "Aggregated in " << time_aggregated
            << " (" << n / time_aggregated << " elem/sec.)"
            << std::endl;

        size_t size_before_merge = 0;
        std::cerr << "Sizes: ";
        for (size_t i = 0; i < num_threads; ++i)
        {
            std::cerr << (i == 0 ? "" : ", ") << maps[i].size();
            size_before_merge += maps[i].size();
        }
        std::cerr << std::endl;

        double time_total = time_aggregated;
        std::cerr
            << "Total in " << time_total
            << " (" << n / time_total << " elem/sec.)"
            << std::endl;
        std::cerr << "Size: " << size_before_merge << std::endl << std::endl;
    }

    if (!method || method == 151)
    {
        /** Option 15.
         * Same as option 13 but works faster in all cases.
         */

        std::vector<Map> maps(num_threads);

        Stopwatch watch;

        for (size_t i = 0; i < num_threads; ++i)
        {
            pool.scheduleOrThrowOnError([&, i] {
                aggregate151(
                    std::ref(maps[i]),
                    data.begin(),
                    data.end(),
                    num_threads,
                    i);
            });
        }

        pool.wait();

        watch.stop();
        double time_aggregated = watch.elapsedSeconds();
        std::cerr
            << "Aggregated in " << time_aggregated
            << " (" << n / time_aggregated << " elem/sec.)"
            << std::endl;

        size_t size_before_merge = 0;
        std::cerr << "Sizes: ";
        for (size_t i = 0; i < num_threads; ++i)
        {
            std::cerr << (i == 0 ? "" : ", ") << maps[i].size();
            size_before_merge += maps[i].size();
        }
        std::cerr << std::endl;

        double time_total = time_aggregated;
        std::cerr
            << "Total in " << time_total
            << " (" << n / time_total << " elem/sec.)"
            << std::endl;
        std::cerr << "Size: " << size_before_merge << std::endl << std::endl;
    }

    if (!method || method == 16)
    {
        /** Option 16.
         */

        std::vector<Map> maps(num_threads);

        Stopwatch watch;

        std::vector<size_t> hashes(n);
        hashes[0] = maps[0].hash(data[0]);
        size_t min_hash = hashes[0];
        size_t max_hash = hashes[0];
        for (size_t i = 1; i < n; ++i) {
            hashes[i] = maps[0].hash(data[i]);
            max_hash = std::max(max_hash, hashes[i]);
            min_hash = std::min(min_hash, hashes[i]);
        }

        std::vector<Source> data_by_thread(num_threads);
        size_t block_size = (max_hash - min_hash) / num_threads;
        for (size_t i = 0; i < n; ++i) {
            data_by_thread[std::min(num_threads - 1, (hashes[i] - min_hash) / block_size)].push_back(data[i]);
        }

        for (size_t i = 0; i < num_threads; ++i)
        {
            pool.scheduleOrThrowOnError([&, i] {
                aggregate16(
                    std::ref(maps[i]),
                    data_by_thread[i].begin(),
                    data_by_thread[i].end());
            });
        }

        pool.wait();

        watch.stop();
        double time_aggregated = watch.elapsedSeconds();
        std::cerr
            << "Aggregated in " << time_aggregated
            << " (" << n / time_aggregated << " elem/sec.)"
            << std::endl;

        size_t size_before_merge = 0;
        std::cerr << "Sizes: ";
        for (size_t i = 0; i < num_threads; ++i)
        {
            std::cerr << (i == 0 ? "" : ", ") << maps[i].size();
            size_before_merge += maps[i].size();
        }
        std::cerr << std::endl;

        double time_total = time_aggregated;
        std::cerr
            << "Total in " << time_total
            << " (" << n / time_total << " elem/sec.)"
            << std::endl;
        std::cerr << "Size: " << size_before_merge << std::endl << std::endl;
    }

    if (!method || method == 161)
    {
        /** Option 16.
         */

        std::vector<Map> maps(num_threads);

        Stopwatch watch;

        std::vector<size_t> hashes(n);
        hashes[0] = maps[0].hash(data[0]);
        size_t min_hash = hashes[0];
        size_t max_hash = hashes[0];
        for (size_t i = 1; i < n; ++i) {
            hashes[i] = maps[0].hash(data[i]);
            max_hash = std::max(max_hash, hashes[i]);
            min_hash = std::min(min_hash, hashes[i]);
        }

        std::vector<std::vector<Key*>> data_by_thread(num_threads);
        //size_t block_size = (max_hash - min_hash) / num_threads;
        __uint128_t n_128 = num_threads;
        for (size_t i = 0; i < n; ++i) {
            data_by_thread[getThreadNum(hashes[i], n_128)].push_back(&data[i]);
        }

        for (size_t i = 0; i < num_threads; ++i)
        {
            pool.scheduleOrThrowOnError([&, i] {
                aggregate161(
                    std::ref(maps[i]),
                    data_by_thread[i].begin(),
                    data_by_thread[i].end());
            });
        }

        pool.wait();

        watch.stop();
        double time_aggregated = watch.elapsedSeconds();
        std::cerr
            << "Aggregated in " << time_aggregated
            << " (" << n / time_aggregated << " elem/sec.)"
            << std::endl;

        size_t size_before_merge = 0;
        std::cerr << "Sizes: ";
        for (size_t i = 0; i < num_threads; ++i)
        {
            std::cerr << (i == 0 ? "" : ", ") << maps[i].size();
            size_before_merge += maps[i].size();
        }
        std::cerr << std::endl;

        double time_total = time_aggregated;
        std::cerr
            << "Total in " << time_total
            << " (" << n / time_total << " elem/sec.)"
            << std::endl;
        std::cerr << "Size: " << size_before_merge << std::endl << std::endl;
    }

    if (!method || method == 17)
    {
        /** Option 17.
         */

        //const size_t threshold = 262144;
        const size_t threshold = n / num_threads;
        std::vector<Map> maps(num_threads * 2);

        Stopwatch watch;

        std::vector<size_t> hashes(n);
        std::vector<size_t> items_count(num_threads);
        std::vector<std::vector<size_t>> areas(num_threads, std::vector<size_t>(1));

        hashes[0] = maps[0].hash(data[0]);
        size_t min_hash = hashes[0];
        size_t max_hash = hashes[0];
        for (size_t i = 1; i < n; ++i) {
            hashes[i] = maps[0].hash(data[i]);
            max_hash = std::max(max_hash, hashes[i]);
            min_hash = std::min(min_hash, hashes[i]);
        }

        size_t block_size = (max_hash - min_hash) / num_threads;
        size_t bucket_num;
        for (size_t i = 0; i < n; ++i) {
            bucket_num = std::min(num_threads - 1, (hashes[i] - min_hash) / block_size);
            ++items_count[bucket_num];
            if (items_count[bucket_num] > threshold) {
                items_count[bucket_num] = 1;
                areas[bucket_num].push_back(i);
            }
        }

        size_t thread_ind = 0;
        for (size_t i = 0; i < num_threads; ++i)
            for (size_t j = 0; j < areas[i].size(); ++j)
            {
                pool.scheduleOrThrowOnError([&, i, j, thread_ind] {
                    aggregate15(
                        std::ref(maps[thread_ind]),
                        data.begin() + areas[i][j],
                        j + 1 == areas[i].size() ? data.end() : data.begin() + areas[i][j + 1],
                        min_hash + (max_hash - min_hash) / num_threads * i,
                        i + 1 == num_threads ? max_hash : min_hash + (max_hash - min_hash) / num_threads * (i + 1) - 1);
                });
                ++thread_ind;
            }
        pool.wait();

        watch.stop();
        double time_aggregated = watch.elapsedSeconds();
        std::cerr
            << "Aggregated in " << time_aggregated
            << " (" << n / time_aggregated << " elem/sec.)"
            << std::endl;

        size_t size_before_merge = 0;
        std::cerr << "Sizes: ";
        for (size_t i = 0; i < thread_ind; ++i)
        {
            std::cerr << (i == 0 ? "" : ", ") << maps[i].size();
            size_before_merge += maps[i].size();
        }
        std::cerr << std::endl;

        watch.restart();

        thread_ind = 0;
        std::vector<size_t> result_maps(num_threads);
        for (size_t i = 0; i < num_threads; ++i)
        {
            result_maps[i] = thread_ind;
            if (areas[i].size() > 1)
                pool.scheduleOrThrowOnError([&, i, thread_ind] { merge17(maps.data(), thread_ind, thread_ind + areas[i].size()); });
            thread_ind += areas[i].size();
        }

        pool.wait();

        watch.stop();
        double time_merged = watch.elapsedSeconds();
        std::cerr
            << "Merged in " << time_merged
            << " (" << size_before_merge / time_merged << " elem/sec.)"
            << std::endl;

        size_t size_after_merge = 0;
        std::cerr << "Sizes: ";
        for (size_t i = 0; i < num_threads; ++i)
        {
            std::cerr << (i == 0 ? "" : ", ") << maps[result_maps[i]].size();
            size_after_merge += maps[result_maps[i]].size();
        }
        std::cerr << std::endl;

        double time_total = time_aggregated + time_merged;
        std::cerr
            << "Total in " << time_total
            << " (" << n / time_total << " elem/sec.)"
            << std::endl;
        std::cerr << "Size: " << size_after_merge << std::endl << std::endl;
    }

    if (!method || method == 171)
    {
        /** Option 17.
         */

        //const size_t threshold = 262144;
        const size_t threshold = n / num_threads;
        std::vector<Map> maps(num_threads * 2);

        Stopwatch watch;

        std::vector<size_t> items_count(num_threads);
        std::vector<std::vector<size_t>> areas(num_threads, std::vector<size_t>(1));

        __uint128_t num_threads_128 = num_threads;
        for (size_t i = 0; i < n; ++i) {
            size_t hash = maps[0].hash(data[i]);
            size_t bucket_num = getThreadNum(hash, num_threads_128);
            ++items_count[bucket_num];
            if (items_count[bucket_num] > threshold) {
                items_count[bucket_num] = 1;
                areas[bucket_num].push_back(i);
            }
        }

        watch.stop();
        double time_prepared = watch.elapsedSeconds();
        std::cerr
            << "Prepared in " << time_prepared
            << " (" << n / time_prepared << " elem/sec.)"
            << std::endl;

        watch.restart();

        size_t thread_ind = 0;
        for (size_t i = 0; i < num_threads; ++i)
            for (size_t j = 0; j < areas[i].size(); ++j)
            {
                pool.scheduleOrThrowOnError([&, i, j, thread_ind] {
                    aggregate151(
                        std::ref(maps[thread_ind]),
                        data.begin() + areas[i][j],
                        j + 1 == areas[i].size() ? data.end() : data.begin() + areas[i][j + 1],
                        num_threads,
                        i);
                });
                ++thread_ind;
            }
        pool.wait();

        watch.stop();
        double time_aggregated = watch.elapsedSeconds();
        std::cerr
            << "Aggregated in " << time_aggregated
            << " (" << n / time_aggregated << " elem/sec.)"
            << std::endl;

        size_t size_before_merge = 0;
        std::cerr << "Sizes: ";
        for (size_t i = 0; i < thread_ind; ++i)
        {
            std::cerr << (i == 0 ? "" : ", ") << maps[i].size();
            size_before_merge += maps[i].size();
        }
        std::cerr << std::endl;

        watch.restart();

        thread_ind = 0;
        std::vector<size_t> result_maps(num_threads);
        for (size_t i = 0; i < num_threads; ++i)
        {
            result_maps[i] = thread_ind;
            if (areas[i].size() > 1)
                pool.scheduleOrThrowOnError([&, i, thread_ind] {
                    merge17(maps.data(), thread_ind, thread_ind + areas[i].size());
                });
            thread_ind += areas[i].size();
        }

        pool.wait();

        watch.stop();
        double time_merged = watch.elapsedSeconds();
        std::cerr
            << "Merged in " << time_merged
            << " (" << size_before_merge / time_merged << " elem/sec.)"
            << std::endl;

        size_t size_after_merge = 0;
        std::cerr << "Sizes: ";
        for (size_t i = 0; i < num_threads; ++i)
        {
            std::cerr << (i == 0 ? "" : ", ") << maps[result_maps[i]].size();
            size_after_merge += maps[result_maps[i]].size();
        }
        std::cerr << std::endl;

        double time_total = time_prepared + time_aggregated + time_merged;
        std::cerr
            << "Total in " << time_total
            << " (" << n / time_total << " elem/sec.)"
            << std::endl;
        std::cerr << "Size: " << size_after_merge << std::endl << std::endl;
    }

    if (!method || method == 172)
    {
        /** Option 17.
         */

        //const size_t threshold = 262144;
        const size_t threshold = 262144;
        std::vector<Map> maps(n / threshold + num_threads);

        Stopwatch watch;

        std::vector<size_t> items_count(num_threads);
        std::vector<std::vector<size_t>> areas(num_threads, std::vector<size_t>(1));

        __uint128_t num_threads_128 = num_threads;
        for (size_t i = 0; i < n; ++i) {
            size_t hash = maps[0].hash(data[i]);
            size_t bucket_num = getThreadNum(hash, num_threads_128);
            ++items_count[bucket_num];
            if (items_count[bucket_num] > threshold) {
                items_count[bucket_num] = 1;
                areas[bucket_num].push_back(i);
            }
        }

        size_t thread_ind = 0;
        for (size_t i = 0; i < num_threads; ++i)
            for (size_t j = 0; j < areas[i].size(); ++j)
            {
                pool.scheduleOrThrowOnError([&, i, j, thread_ind] {
                    aggregate151(
                        std::ref(maps[thread_ind]),
                        data.begin() + areas[i][j],
                        j + 1 == areas[i].size() ? data.end() : data.begin() + areas[i][j + 1],
                        num_threads,
                        i);
                });
                ++thread_ind;
            }
        pool.wait();

        watch.stop();
        double time_aggregated = watch.elapsedSeconds();
        std::cerr
            << "Aggregated in " << time_aggregated
            << " (" << n / time_aggregated << " elem/sec.)"
            << std::endl;

        size_t size_before_merge = 0;
        std::cerr << "Sizes: ";
        for (size_t i = 0; i < thread_ind; ++i)
        {
            std::cerr << (i == 0 ? "" : ", ") << maps[i].size();
            size_before_merge += maps[i].size();
        }
        std::cerr << std::endl;

        watch.restart();

        thread_ind = 0;
        std::vector<size_t> result_maps(num_threads);
        for (size_t i = 0; i < num_threads; ++i)
        {
            result_maps[i] = thread_ind;
            if (areas[i].size() > 1)
                pool.scheduleOrThrowOnError([&, i, thread_ind] {
                    merge17(maps.data(), thread_ind, thread_ind + areas[i].size());
                });
            thread_ind += areas[i].size();
        }

        pool.wait();

        watch.stop();
        double time_merged = watch.elapsedSeconds();
        std::cerr
            << "Merged in " << time_merged
            << " (" << size_before_merge / time_merged << " elem/sec.)"
            << std::endl;

        size_t size_after_merge = 0;
        std::cerr << "Sizes: ";
        for (size_t i = 0; i < num_threads; ++i)
        {
            std::cerr << (i == 0 ? "" : ", ") << maps[result_maps[i]].size();
            size_after_merge += maps[result_maps[i]].size();
        }
        std::cerr << std::endl;

        double time_total = time_aggregated + time_merged;
        std::cerr
            << "Total in " << time_total
            << " (" << n / time_total << " elem/sec.)"
            << std::endl;
        std::cerr << "Size: " << size_after_merge << std::endl << std::endl;
    }

    if (!method || method == 173)
    {
        /** Option 17.
         */

        //const size_t threshold = 262144;
        const size_t threshold = n / num_threads;
        std::vector<Map> maps(num_threads * 2);

        Stopwatch watch;

        std::vector<size_t> items_count(num_threads);
        std::vector<std::vector<size_t>> areas(num_threads, std::vector<size_t>(1));

        __uint128_t num_threads_128 = num_threads;
        for (size_t i = 0; i < n; ++i) {
            size_t hash = maps[0].hash(data[i]);
            size_t bucket_num = getThreadNum(hash, num_threads_128);
            ++items_count[bucket_num];
            if (items_count[bucket_num] > threshold) {
                items_count[bucket_num] = 1;
                areas[bucket_num].push_back(i);
            }
        }

        for (size_t i = 0; i < num_threads; ++i)
            if (areas[i].size() > 1)
                areas[i][areas[i].size() - 1] = areas[i][areas[i].size() - 2] + (threshold + items_count[i]) / 2 * (areas[i][areas[i].size() - 1] - areas[i][areas[i].size() - 2]) / threshold;

        watch.stop();
        double time_prepared = watch.elapsedSeconds();
        std::cerr
            << "Prepared in " << time_prepared
            << " (" << n / time_prepared << " elem/sec.)"
            << std::endl;

        watch.restart();

        size_t thread_ind = 0;
        for (size_t i = 0; i < num_threads; ++i)
            for (size_t j = 0; j < areas[i].size(); ++j)
            {
                pool.scheduleOrThrowOnError([&, i, j, thread_ind] {
                    aggregate151(
                        std::ref(maps[thread_ind]),
                        data.begin() + areas[i][j],
                        j + 1 == areas[i].size() ? data.end() : data.begin() + areas[i][j + 1],
                        num_threads,
                        i);
                });
                ++thread_ind;
            }
        pool.wait();

        watch.stop();
        double time_aggregated = watch.elapsedSeconds();
        std::cerr
            << "Aggregated in " << time_aggregated
            << " (" << n / time_aggregated << " elem/sec.)"
            << std::endl;

        size_t size_before_merge = 0;
        std::cerr << "Sizes: ";
        for (size_t i = 0; i < thread_ind; ++i)
        {
            std::cerr << (i == 0 ? "" : ", ") << maps[i].size();
            size_before_merge += maps[i].size();
        }
        std::cerr << std::endl;

        watch.restart();

        thread_ind = 0;
        std::vector<size_t> result_maps(num_threads);
        for (size_t i = 0; i < num_threads; ++i)
        {
            result_maps[i] = thread_ind;
            if (areas[i].size() > 1)
                pool.scheduleOrThrowOnError([&, i, thread_ind] {
                    merge17(maps.data(), thread_ind, thread_ind + areas[i].size());
                });
            thread_ind += areas[i].size();
        }

        pool.wait();

        watch.stop();
        double time_merged = watch.elapsedSeconds();
        std::cerr
            << "Merged in " << time_merged
            << " (" << size_before_merge / time_merged << " elem/sec.)"
            << std::endl;

        size_t size_after_merge = 0;
        std::cerr << "Sizes: ";
        for (size_t i = 0; i < num_threads; ++i)
        {
            std::cerr << (i == 0 ? "" : ", ") << maps[result_maps[i]].size();
            size_after_merge += maps[result_maps[i]].size();
        }
        std::cerr << std::endl;

        double time_total = time_prepared + time_aggregated + time_merged;
        std::cerr
            << "Total in " << time_total
            << " (" << n / time_total << " elem/sec.)"
            << std::endl;
        std::cerr << "Size: " << size_after_merge << std::endl << std::endl;
    }

    if (!method || method == 2)
    {
        /** Option 2.
          * In different threads, we aggregate independently into different two-level hash tables.
          * Then merge them together, parallelizing by the first level buckets.
          * When using hash tables of large sizes (10 million elements or more),
          *  and a large number of threads (8-32), the merge is a bottleneck,
          *  and has a performance advantage of 4 times.
          */

        std::vector<MapTwoLevel> maps(num_threads);

        Stopwatch watch;

        for (size_t i = 0; i < num_threads; ++i)
            pool.scheduleOrThrowOnError([&, i] { aggregate2(
                std::ref(maps[i]),
                data.begin() + (data.size() * i) / num_threads,
                data.begin() + (data.size() * (i + 1)) / num_threads); });

        pool.wait();

        watch.stop();
        double time_aggregated = watch.elapsedSeconds();
        std::cerr
            << "Aggregated in " << time_aggregated
            << " (" << n / time_aggregated << " elem/sec.)"
            << std::endl;

        size_t size_before_merge = 0;
        std::cerr << "Sizes: ";
        for (size_t i = 0; i < num_threads; ++i)
        {
            std::cerr << (i == 0 ? "" : ", ") << maps[i].size();
            size_before_merge += maps[i].size();
        }
        std::cerr << std::endl;

        watch.restart();

        for (size_t i = 0; i < MapTwoLevel::NUM_BUCKETS; ++i)
            pool.scheduleOrThrowOnError([&, i] { merge2(maps.data(), num_threads, i); });

        pool.wait();

        watch.stop();
        double time_merged = watch.elapsedSeconds();
        std::cerr
            << "Merged in " << time_merged
            << " (" << size_before_merge / time_merged << " elem/sec.)"
            << std::endl;

        double time_total = time_aggregated + time_merged;
        std::cerr
            << "Total in " << time_total
            << " (" << n / time_total << " elem/sec.)"
            << std::endl;

        std::cerr << "Size: " << maps[0].size() << std::endl << std::endl;
    }

    if (!method || method == 22)
    {
        std::vector<MapTwoLevel> maps(num_threads);

        Stopwatch watch;

        for (size_t i = 0; i < num_threads; ++i)
            pool.scheduleOrThrowOnError([&, i] { aggregate22(
                                    std::ref(maps[i]),
                                    data.begin() + (data.size() * i) / num_threads,
                                    data.begin() + (data.size() * (i + 1)) / num_threads); });

        pool.wait();

        watch.stop();
        double time_aggregated = watch.elapsedSeconds();
        std::cerr
        << "Aggregated in " << time_aggregated
        << " (" << n / time_aggregated << " elem/sec.)"
        << std::endl;

        size_t size_before_merge = 0;
        std::cerr << "Sizes: ";
        for (size_t i = 0; i < num_threads; ++i)
        {
            std::cerr << (i == 0 ? "" : ", ") << maps[i].size();
            size_before_merge += maps[i].size();
        }
        std::cerr << std::endl;

        watch.restart();

        for (size_t i = 0; i < MapTwoLevel::NUM_BUCKETS; ++i)
            pool.scheduleOrThrowOnError([&, i] { merge2(maps.data(), num_threads, i); });

        pool.wait();

        watch.stop();
        double time_merged = watch.elapsedSeconds();
        std::cerr
        << "Merged in " << time_merged
        << " (" << size_before_merge / time_merged << " elem/sec.)"
        << std::endl;

        double time_total = time_aggregated + time_merged;
        std::cerr
        << "Total in " << time_total
        << " (" << n / time_total << " elem/sec.)"
        << std::endl;

        std::cerr << "Size: " << maps[0].size() << std::endl << std::endl;
    }

    if (!method || method == 23)
    {
        /** Option 23.
          */
        //const size_t block_size = 524288;
        const size_t block_size = 32768;
        size_t maps_count = (n + block_size - 1) / block_size;
        std::vector<MapTwoLevel> maps(maps_count);

        Stopwatch watch;

        for (size_t i = 0; i < maps_count; ++i)
            pool.scheduleOrThrowOnError([&, i] { aggregate22(
                std::ref(maps[i]),
                data.begin() + (data.size() * i) / maps_count,
                data.begin() + (data.size() * (i + 1)) / maps_count); });

        pool.wait();

        watch.stop();
        double time_aggregated = watch.elapsedSeconds();
        std::cerr
            << "Aggregated in " << time_aggregated
            << " (" << n / time_aggregated << " elem/sec.)"
            << std::endl;

        size_t size_before_merge = 0;
        std::cerr << "Sizes: ";
        for (size_t i = 0; i < maps_count; ++i)
        {
            std::cerr << (i == 0 ? "" : ", ") << maps[i].size();
            size_before_merge += maps[i].size();
        }
        std::cerr << std::endl;

        watch.restart();

        for (size_t i = 0; i < MapTwoLevel::NUM_BUCKETS; ++i)
            pool.scheduleOrThrowOnError([&, i] { merge2(maps.data(), maps_count, i); });

        pool.wait();

        watch.stop();
        double time_merged = watch.elapsedSeconds();
        std::cerr
            << "Merged in " << time_merged
            << " (" << size_before_merge / time_merged << " elem/sec.)"
            << std::endl;

        double time_total = time_aggregated + time_merged;
        std::cerr
            << "Total in " << time_total
            << " (" << n / time_total << " elem/sec.)"
            << std::endl;

        std::cerr << "Size: " << maps[0].size() << std::endl << std::endl;
    }

    if (!method || method == 24)
    {
        /** Option 23.
          */
        //const size_t block_size = 524288;
        const size_t block_size = 131072;
        size_t maps_count = (n + block_size - 1) / block_size;
        std::vector<MapTwoLevel> maps(maps_count);

        Stopwatch watch;

        for (size_t i = 0; i < maps_count; ++i)
            pool.scheduleOrThrowOnError([&, i] { aggregate22(
                std::ref(maps[i]),
                data.begin() + (data.size() * i) / maps_count,
                data.begin() + (data.size() * (i + 1)) / maps_count); });

        pool.wait();

        watch.stop();
        double time_aggregated = watch.elapsedSeconds();
        std::cerr
            << "Aggregated in " << time_aggregated
            << " (" << n / time_aggregated << " elem/sec.)"
            << std::endl;

        size_t size_before_merge = 0;
        std::cerr << "Sizes: ";
        for (size_t i = 0; i < maps_count; ++i)
        {
            std::cerr << (i == 0 ? "" : ", ") << maps[i].size();
            size_before_merge += maps[i].size();
        }
        std::cerr << std::endl;

        watch.restart();

        for (size_t i = 0; i < MapTwoLevel::NUM_BUCKETS; ++i)
            pool.scheduleOrThrowOnError([&, i] { merge2(maps.data(), maps_count, i); });

        pool.wait();

        watch.stop();
        double time_merged = watch.elapsedSeconds();
        std::cerr
            << "Merged in " << time_merged
            << " (" << size_before_merge / time_merged << " elem/sec.)"
            << std::endl;

        double time_total = time_aggregated + time_merged;
        std::cerr
            << "Total in " << time_total
            << " (" << n / time_total << " elem/sec.)"
            << std::endl;

        std::cerr << "Size: " << maps[0].size() << std::endl << std::endl;
    }

    if (!method || method == 25)
    {
        /** Option 23.
          */
        //const size_t block_size = 524288;
        const size_t block_size = 524288;
        size_t maps_count = (n + block_size - 1) / block_size;
        std::vector<MapTwoLevel> maps(maps_count);

        Stopwatch watch;

        for (size_t i = 0; i < maps_count; ++i)
            pool.scheduleOrThrowOnError([&, i] { aggregate22(
                std::ref(maps[i]),
                data.begin() + (data.size() * i) / maps_count,
                data.begin() + (data.size() * (i + 1)) / maps_count); });

        pool.wait();

        watch.stop();
        double time_aggregated = watch.elapsedSeconds();
        std::cerr
            << "Aggregated in " << time_aggregated
            << " (" << n / time_aggregated << " elem/sec.)"
            << std::endl;

        size_t size_before_merge = 0;
        std::cerr << "Sizes: ";
        for (size_t i = 0; i < maps_count; ++i)
        {
            std::cerr << (i == 0 ? "" : ", ") << maps[i].size();
            size_before_merge += maps[i].size();
        }
        std::cerr << std::endl;

        watch.restart();

        for (size_t i = 0; i < MapTwoLevel::NUM_BUCKETS; ++i)
            pool.scheduleOrThrowOnError([&, i] { merge2(maps.data(), maps_count, i); });

        pool.wait();

        watch.stop();
        double time_merged = watch.elapsedSeconds();
        std::cerr
            << "Merged in " << time_merged
            << " (" << size_before_merge / time_merged << " elem/sec.)"
            << std::endl;

        double time_total = time_aggregated + time_merged;
        std::cerr
            << "Total in " << time_total
            << " (" << n / time_total << " elem/sec.)"
            << std::endl;

        std::cerr << "Size: " << maps[0].size() << std::endl << std::endl;
    }

    if (!method || method == 3)
    {
        /** Option 3.
          * In different threads, we aggregate independently into different hash tables,
          *  until their size becomes large enough.
          * If the size of the local hash table is large, and there is no element in it,
          *  then we insert it into one global hash table, protected by mutex,
          *  and if mutex failed to capture, then insert it into the local one.
          * Then merge all the local hash tables to the global one.
          * This method is bad - a lot of contention.
          */

        std::vector<Map> local_maps(num_threads);
        Map global_map;
        Mutex mutex;

        Stopwatch watch;

        for (size_t i = 0; i < num_threads; ++i)
            pool.scheduleOrThrowOnError([&, i] { aggregate3(
                std::ref(local_maps[i]),
                std::ref(global_map),
                std::ref(mutex),
                data.begin() + (data.size() * i) / num_threads,
                data.begin() + (data.size() * (i + 1)) / num_threads); });

        pool.wait();

        watch.stop();
        double time_aggregated = watch.elapsedSeconds();
        std::cerr
            << "Aggregated in " << time_aggregated
            << " (" << n / time_aggregated << " elem/sec.)"
            << std::endl;

        size_t size_before_merge = 0;
        std::cerr << "Sizes (local): ";
        for (size_t i = 0; i < num_threads; ++i)
        {
            std::cerr << (i == 0 ? "" : ", ") << local_maps[i].size();
            size_before_merge += local_maps[i].size();
        }
        std::cerr << std::endl;
        std::cerr << "Size (global): " << global_map.size() << std::endl;
        size_before_merge += global_map.size();

        watch.restart();

        for (size_t i = 0; i < num_threads; ++i)
            for (auto it = local_maps[i].begin(); it != local_maps[i].end(); ++it)
                global_map[it->getKey()] += it->getMapped();

        pool.wait();

        watch.stop();
        double time_merged = watch.elapsedSeconds();
        std::cerr
            << "Merged in " << time_merged
            << " (" << size_before_merge / time_merged << " elem/sec.)"
            << std::endl;

        double time_total = time_aggregated + time_merged;
        std::cerr
            << "Total in " << time_total
            << " (" << n / time_total << " elem/sec.)"
            << std::endl;

        std::cerr << "Size: " << global_map.size() << std::endl << std::endl;
    }

    if (!method || method == 33)
    {
        /** Option 33.
         * In different threads, we aggregate independently into different hash tables,
         *  until their size becomes large enough.
         * Then we insert the data to the global hash table, protected by mutex, and continue.
         */

        std::vector<Map> local_maps(num_threads);
        Map global_map;
        Mutex mutex;

        Stopwatch watch;

        for (size_t i = 0; i < num_threads; ++i)
            pool.scheduleOrThrowOnError([&, i] { aggregate33(
                std::ref(local_maps[i]),
                std::ref(global_map),
                std::ref(mutex),
                data.begin() + (data.size() * i) / num_threads,
                data.begin() + (data.size() * (i + 1)) / num_threads); });

        pool.wait();

        watch.stop();
        double time_aggregated = watch.elapsedSeconds();
        std::cerr
        << "Aggregated in " << time_aggregated
        << " (" << n / time_aggregated << " elem/sec.)"
        << std::endl;

        size_t size_before_merge = 0;
        std::cerr << "Sizes (local): ";
        for (size_t i = 0; i < num_threads; ++i)
        {
            std::cerr << (i == 0 ? "" : ", ") << local_maps[i].size();
            size_before_merge += local_maps[i].size();
        }
        std::cerr << std::endl;
        std::cerr << "Size (global): " << global_map.size() << std::endl;
        size_before_merge += global_map.size();

        watch.restart();

        for (size_t i = 0; i < num_threads; ++i)
            for (auto it = local_maps[i].begin(); it != local_maps[i].end(); ++it)
                global_map[it->getKey()] += it->getMapped();

        pool.wait();

        watch.stop();
        double time_merged = watch.elapsedSeconds();
        std::cerr
        << "Merged in " << time_merged
        << " (" << size_before_merge / time_merged << " elem/sec.)"
        << std::endl;

        double time_total = time_aggregated + time_merged;
        std::cerr
        << "Total in " << time_total
        << " (" << n / time_total << " elem/sec.)"
        << std::endl;

        std::cerr << "Size: " << global_map.size() << std::endl << std::endl;
    }

    if (!method || method == 4)
    {
        /** Option 4.
          * In different threads, we aggregate independently into different hash tables,
          *  until their size becomes large enough.
          * If the size of the local hash table is large, and there is no element in it,
          *  then insert it into one of 256 global hash tables, each of which is under its mutex.
          * Then merge all local hash tables into the global one.
          * This method is not so bad with a lot of threads, but worse than the second one.
          */

        std::vector<Map> local_maps(num_threads);
        MapTwoLevel global_map;
        std::vector<Mutex> mutexes(MapTwoLevel::NUM_BUCKETS);

        Stopwatch watch;

        for (size_t i = 0; i < num_threads; ++i)
            pool.scheduleOrThrowOnError([&, i] { aggregate4(
                std::ref(local_maps[i]),
                std::ref(global_map),
                mutexes.data(),
                data.begin() + (data.size() * i) / num_threads,
                data.begin() + (data.size() * (i + 1)) / num_threads); });

        pool.wait();

        watch.stop();
        double time_aggregated = watch.elapsedSeconds();
        std::cerr
            << "Aggregated in " << time_aggregated
            << " (" << n / time_aggregated << " elem/sec.)"
            << std::endl;

        size_t size_before_merge = 0;
        std::cerr << "Sizes (local): ";
        for (size_t i = 0; i < num_threads; ++i)
        {
            std::cerr << (i == 0 ? "" : ", ") << local_maps[i].size();
            size_before_merge += local_maps[i].size();
        }
        std::cerr << std::endl;

        size_t sum_size = global_map.size();
        std::cerr << "Size (global): " << sum_size << std::endl;
        size_before_merge += sum_size;

        watch.restart();

        for (size_t i = 0; i < num_threads; ++i)
            for (auto it = local_maps[i].begin(); it != local_maps[i].end(); ++it)
                global_map[it->getKey()] += it->getMapped();

        pool.wait();

        watch.stop();
        double time_merged = watch.elapsedSeconds();
        std::cerr
            << "Merged in " << time_merged
            << " (" << size_before_merge / time_merged << " elem/sec.)"
            << std::endl;

        double time_total = time_aggregated + time_merged;
        std::cerr
            << "Total in " << time_total
            << " (" << n / time_total << " elem/sec.)"
            << std::endl;

        std::cerr << "Size: " << global_map.size() << std::endl << std::endl;
    }

    if (!method || method == 41)
    {
        /** Option 4.
          * In different threads, we aggregate independently into different hash tables,
          *  until their size becomes large enough.
          * If the size of the local hash table is large, and there is no element in it,
          *  then insert it into one of 256 global hash tables, each of which is under its mutex.
          * Then merge all local hash tables into the global one.
          * This method is not so bad with a lot of threads, but worse than the second one.
          */

        std::vector<Map> local_maps(num_threads);
        MapTwoLevel global_map;
        std::vector<AlignedSmallLock> mutexes(MapTwoLevel::NUM_BUCKETS);

        Stopwatch watch;

        for (size_t i = 0; i < num_threads; ++i)
            pool.scheduleOrThrowOnError([&, i] { aggregate41(
                std::ref(local_maps[i]),
                std::ref(global_map),
                mutexes.data(),
                data.begin() + (data.size() * i) / num_threads,
                data.begin() + (data.size() * (i + 1)) / num_threads); });

        pool.wait();

        watch.stop();
        double time_aggregated = watch.elapsedSeconds();
        std::cerr
            << "Aggregated in " << time_aggregated
            << " (" << n / time_aggregated << " elem/sec.)"
            << std::endl;

        size_t size_before_merge = 0;
        std::cerr << "Sizes (local): ";
        for (size_t i = 0; i < num_threads; ++i)
        {
            std::cerr << (i == 0 ? "" : ", ") << local_maps[i].size();
            size_before_merge += local_maps[i].size();
        }
        std::cerr << std::endl;

        size_t sum_size = global_map.size();
        std::cerr << "Size (global): " << sum_size << std::endl;
        size_before_merge += sum_size;

        watch.restart();

        for (size_t i = 0; i < num_threads; ++i)
            for (auto it = local_maps[i].begin(); it != local_maps[i].end(); ++it)
                global_map[it->getKey()] += it->getMapped();

        pool.wait();

        watch.stop();
        double time_merged = watch.elapsedSeconds();
        std::cerr
            << "Merged in " << time_merged
            << " (" << size_before_merge / time_merged << " elem/sec.)"
            << std::endl;

        double time_total = time_aggregated + time_merged;
        std::cerr
            << "Total in " << time_total
            << " (" << n / time_total << " elem/sec.)"
            << std::endl;

        std::cerr << "Size: " << global_map.size() << std::endl << std::endl;
    }

    if (!method || method == 411)
    {
        /** Option 4.
          * In different threads, we aggregate independently into different hash tables,
          *  until their size becomes large enough.
          * If the size of the local hash table is large, and there is no element in it,
          *  then insert it into one of 256 global hash tables, each of which is under its mutex.
          * Then merge all local hash tables into the global one.
          * This method is not so bad with a lot of threads, but worse than the second one.
          */

        std::vector<Map> local_maps(num_threads);
        MapTwoLevel global_map;
        std::vector<AlignedSmallLock> mutexes(MapTwoLevel::NUM_BUCKETS);

        Stopwatch watch;

        for (size_t i = 0; i < num_threads; ++i)
            pool.scheduleOrThrowOnError([&, i] { aggregate41(
                std::ref(local_maps[i]),
                std::ref(global_map),
                mutexes.data(),
                data.begin() + (data.size() * i) / num_threads,
                data.begin() + (data.size() * (i + 1)) / num_threads); });

        pool.wait();

        watch.stop();
        double time_aggregated = watch.elapsedSeconds();
        std::cerr
            << "Aggregated in " << time_aggregated
            << " (" << n / time_aggregated << " elem/sec.)"
            << std::endl;

        size_t size_before_merge = 0;
        std::cerr << "Sizes (local): ";
        for (size_t i = 0; i < num_threads; ++i)
        {
            std::cerr << (i == 0 ? "" : ", ") << local_maps[i].size();
            size_before_merge += local_maps[i].size();
        }
        std::cerr << std::endl;

        size_t sum_size = global_map.size();
        std::cerr << "Size (global): " << sum_size << std::endl;
        size_before_merge += sum_size;

        watch.restart();

        for (size_t i = 0; i < MapTwoLevel::NUM_BUCKETS; ++i)
            pool.scheduleOrThrowOnError([&, i] { merge411(std::ref(global_map), local_maps.data(), num_threads, i); });

        pool.wait();

        watch.stop();
        double time_merged = watch.elapsedSeconds();
        std::cerr
            << "Merged in " << time_merged
            << " (" << size_before_merge / time_merged << " elem/sec.)"
            << std::endl;

        double time_total = time_aggregated + time_merged;
        std::cerr
            << "Total in " << time_total
            << " (" << n / time_total << " elem/sec.)"
            << std::endl;

        std::cerr << "Size: " << global_map.size() << std::endl << std::endl;
    }

    if (!method || method == 412)
    {
        /** Option 4.
          * In different threads, we aggregate independently into different hash tables,
          *  until their size becomes large enough.
          * If the size of the local hash table is large, and there is no element in it,
          *  then insert it into one of 256 global hash tables, each of which is under its mutex.
          * Then merge all local hash tables into the global one.
          * This method is not so bad with a lot of threads, but worse than the second one.
          */

        std::vector<Map> local_maps(num_threads);
        std::vector<std::vector<std::vector<Key>>> buffers(num_threads, std::vector<std::vector<Key>>(MapTwoLevel::NUM_BUCKETS));
        std::vector<std::vector<size_t>> buffer_idx(num_threads, std::vector<size_t>(MapTwoLevel::NUM_BUCKETS));
        MapTwoLevel global_map;
        std::vector<AlignedSmallLock> mutexes(MapTwoLevel::NUM_BUCKETS);

        Stopwatch watch;

        for (size_t i = 0; i < num_threads; ++i)
            pool.scheduleOrThrowOnError([&, i] { aggregate412(
                std::ref(local_maps[i]),
                std::ref(buffers[i]),
                std::ref(buffer_idx[i]),
                std::ref(global_map),
                mutexes.data(),
                data.begin() + (data.size() * i) / num_threads,
                data.begin() + (data.size() * (i + 1)) / num_threads); });

        pool.wait();

        watch.stop();
        double time_aggregated = watch.elapsedSeconds();
        std::cerr
            << "Aggregated in " << time_aggregated
            << " (" << n / time_aggregated << " elem/sec.)"
            << std::endl;

        size_t size_before_merge = 0;
        std::cerr << "Sizes (local): ";
        for (size_t i = 0; i < num_threads; ++i)
        {
            std::cerr << (i == 0 ? "" : ", ") << local_maps[i].size();
            size_before_merge += local_maps[i].size();
        }
        std::cerr << std::endl;

        size_t sum_size = global_map.size();
        std::cerr << "Size (global): " << sum_size << std::endl;
        size_before_merge += sum_size;

        watch.restart();

        for (size_t i = 0; i < num_threads; ++i)
            for (auto it = local_maps[i].begin(); it != local_maps[i].end(); ++it)
                global_map[it->getKey()] += it->getMapped();

        pool.wait();

        watch.stop();
        double time_merged = watch.elapsedSeconds();
        std::cerr
            << "Merged in " << time_merged
            << " (" << size_before_merge / time_merged << " elem/sec.)"
            << std::endl;

        double time_total = time_aggregated + time_merged;
        std::cerr
            << "Total in " << time_total
            << " (" << n / time_total << " elem/sec.)"
            << std::endl;

        std::cerr << "Size: " << global_map.size() << std::endl << std::endl;
    }

    if (!method || method == 413)
    {
        /** Option 4.
          * In different threads, we aggregate independently into different hash tables,
          *  until their size becomes large enough.
          * If the size of the local hash table is large, and there is no element in it,
          *  then insert it into one of 256 global hash tables, each of which is under its mutex.
          * Then merge all local hash tables into the global one.
          * This method is not so bad with a lot of threads, but worse than the second one.
          */

        std::vector<Map> local_maps(num_threads);
        std::vector<std::vector<std::vector<Key>>> buffers(num_threads, std::vector<std::vector<Key>>(MapTwoLevel::NUM_BUCKETS));
        std::vector<std::vector<size_t>> buffer_idx(num_threads, std::vector<size_t>(MapTwoLevel::NUM_BUCKETS));
        MapTwoLevel global_map;
        std::vector<AlignedSmallLock> mutexes(MapTwoLevel::NUM_BUCKETS);

        Stopwatch watch;

        for (size_t i = 0; i < num_threads; ++i)
            pool.scheduleOrThrowOnError([&, i] { aggregate413(
                std::ref(local_maps[i]),
                std::ref(buffers[i]),
                std::ref(buffer_idx[i]),
                std::ref(global_map),
                mutexes.data(),
                data.begin() + (data.size() * i) / num_threads,
                data.begin() + (data.size() * (i + 1)) / num_threads); });

        pool.wait();

        watch.stop();
        double time_aggregated = watch.elapsedSeconds();
        std::cerr
            << "Aggregated in " << time_aggregated
            << " (" << n / time_aggregated << " elem/sec.)"
            << std::endl;

        size_t size_before_merge = 0;
        std::cerr << "Sizes (local): ";
        for (size_t i = 0; i < num_threads; ++i)
        {
            std::cerr << (i == 0 ? "" : ", ") << local_maps[i].size();
            size_before_merge += local_maps[i].size();
        }
        std::cerr << std::endl;

        size_t sum_size = global_map.size();
        std::cerr << "Size (global): " << sum_size << std::endl;
        size_before_merge += sum_size;

        watch.restart();

        for (size_t i = 0; i < num_threads; ++i)
            for (auto it = local_maps[i].begin(); it != local_maps[i].end(); ++it)
                global_map[it->getKey()] += it->getMapped();

        pool.wait();

        watch.stop();
        double time_merged = watch.elapsedSeconds();
        std::cerr
            << "Merged in " << time_merged
            << " (" << size_before_merge / time_merged << " elem/sec.)"
            << std::endl;

        double time_total = time_aggregated + time_merged;
        std::cerr
            << "Total in " << time_total
            << " (" << n / time_total << " elem/sec.)"
            << std::endl;

        std::cerr << "Size: " << global_map.size() << std::endl << std::endl;
    }

    if (!method || method == 414)
    {
        /** Option 4.
          * In different threads, we aggregate independently into different hash tables,
          *  until their size becomes large enough.
          * If the size of the local hash table is large, and there is no element in it,
          *  then insert it into one of 256 global hash tables, each of which is under its mutex.
          * Then merge all local hash tables into the global one.
          * This method is not so bad with a lot of threads, but worse than the second one.
          */

        std::vector<Map> local_maps(num_threads);
        std::vector<std::vector<std::vector<Key>>> buffers(num_threads, std::vector<std::vector<Key>>(MapTwoLevel512::NUM_BUCKETS));
        std::vector<std::vector<size_t>> buffer_idx(num_threads, std::vector<size_t>(MapTwoLevel512::NUM_BUCKETS));
        MapTwoLevel512 global_map;
        std::vector<AlignedSmallLock> mutexes(MapTwoLevel512::NUM_BUCKETS);

        Stopwatch watch;

        for (size_t i = 0; i < num_threads; ++i)
            pool.scheduleOrThrowOnError([&, i] { aggregate414(
                std::ref(local_maps[i]),
                std::ref(buffers[i]),
                std::ref(buffer_idx[i]),
                std::ref(global_map),
                mutexes.data(),
                data.begin() + (data.size() * i) / num_threads,
                data.begin() + (data.size() * (i + 1)) / num_threads); });

        pool.wait();

        watch.stop();
        double time_aggregated = watch.elapsedSeconds();
        std::cerr
            << "Aggregated in " << time_aggregated
            << " (" << n / time_aggregated << " elem/sec.)"
            << std::endl;

        size_t size_before_merge = 0;
        std::cerr << "Sizes (local): ";
        for (size_t i = 0; i < num_threads; ++i)
        {
            std::cerr << (i == 0 ? "" : ", ") << local_maps[i].size();
            size_before_merge += local_maps[i].size();
        }
        std::cerr << std::endl;

        size_t sum_size = global_map.size();
        std::cerr << "Size (global): " << sum_size << std::endl;
        size_before_merge += sum_size;

        watch.restart();

        for (size_t i = 0; i < num_threads; ++i)
            for (auto it = local_maps[i].begin(); it != local_maps[i].end(); ++it)
                global_map[it->getKey()] += it->getMapped();

        pool.wait();

        watch.stop();
        double time_merged = watch.elapsedSeconds();
        std::cerr
            << "Merged in " << time_merged
            << " (" << size_before_merge / time_merged << " elem/sec.)"
            << std::endl;

        double time_total = time_aggregated + time_merged;
        std::cerr
            << "Total in " << time_total
            << " (" << n / time_total << " elem/sec.)"
            << std::endl;

        std::cerr << "Size: " << global_map.size() << std::endl << std::endl;
    }

    if (!method || method == 415)
    {
        /** Option 4.
          * In different threads, we aggregate independently into different hash tables,
          *  until their size becomes large enough.
          * If the size of the local hash table is large, and there is no element in it,
          *  then insert it into one of 256 global hash tables, each of which is under its mutex.
          * Then merge all local hash tables into the global one.
          * This method is not so bad with a lot of threads, but worse than the second one.
          */

        std::vector<Map> local_maps(num_threads);
        std::vector<std::vector<std::vector<Key>>> buffers(num_threads, std::vector<std::vector<Key>>(MapTwoLevel128::NUM_BUCKETS));
        std::vector<std::vector<size_t>> buffer_idx(num_threads, std::vector<size_t>(MapTwoLevel128::NUM_BUCKETS));
        MapTwoLevel128 global_map;
        std::vector<AlignedSmallLock> mutexes(MapTwoLevel128::NUM_BUCKETS);

        Stopwatch watch;

        for (size_t i = 0; i < num_threads; ++i)
            pool.scheduleOrThrowOnError([&, i] { aggregate415(
                std::ref(local_maps[i]),
                std::ref(buffers[i]),
                std::ref(buffer_idx[i]),
                std::ref(global_map),
                mutexes.data(),
                data.begin() + (data.size() * i) / num_threads,
                data.begin() + (data.size() * (i + 1)) / num_threads); });

        pool.wait();

        watch.stop();
        double time_aggregated = watch.elapsedSeconds();
        std::cerr
            << "Aggregated in " << time_aggregated
            << " (" << n / time_aggregated << " elem/sec.)"
            << std::endl;

        size_t size_before_merge = 0;
        std::cerr << "Sizes (local): ";
        for (size_t i = 0; i < num_threads; ++i)
        {
            std::cerr << (i == 0 ? "" : ", ") << local_maps[i].size();
            size_before_merge += local_maps[i].size();
        }
        std::cerr << std::endl;

        size_t sum_size = global_map.size();
        std::cerr << "Size (global): " << sum_size << std::endl;
        size_before_merge += sum_size;

        watch.restart();

        for (size_t i = 0; i < num_threads; ++i)
            for (auto it = local_maps[i].begin(); it != local_maps[i].end(); ++it)
                global_map[it->getKey()] += it->getMapped();

        pool.wait();

        watch.stop();
        double time_merged = watch.elapsedSeconds();
        std::cerr
            << "Merged in " << time_merged
            << " (" << size_before_merge / time_merged << " elem/sec.)"
            << std::endl;

        double time_total = time_aggregated + time_merged;
        std::cerr
            << "Total in " << time_total
            << " (" << n / time_total << " elem/sec.)"
            << std::endl;

        std::cerr << "Size: " << global_map.size() << std::endl << std::endl;
    }

    if (!method || method == 416)
    {
        /** Option 4.
          * In different threads, we aggregate independently into different hash tables,
          *  until their size becomes large enough.
          * If the size of the local hash table is large, and there is no element in it,
          *  then insert it into one of 256 global hash tables, each of which is under its mutex.
          * Then merge all local hash tables into the global one.
          * This method is not so bad with a lot of threads, but worse than the second one.
          */

        std::vector<Map> local_maps(num_threads);
        std::vector<std::vector<std::vector<Key>>> buffers(num_threads, std::vector<std::vector<Key>>(MapTwoLevel1024::NUM_BUCKETS));
        std::vector<std::vector<size_t>> buffer_idx(num_threads, std::vector<size_t>(MapTwoLevel1024::NUM_BUCKETS));
        MapTwoLevel1024 global_map;
        std::vector<AlignedSmallLock> mutexes(MapTwoLevel1024::NUM_BUCKETS);

        Stopwatch watch;

        for (size_t i = 0; i < num_threads; ++i)
            pool.scheduleOrThrowOnError([&, i] { aggregate416(
                std::ref(local_maps[i]),
                std::ref(buffers[i]),
                std::ref(buffer_idx[i]),
                std::ref(global_map),
                mutexes.data(),
                data.begin() + (data.size() * i) / num_threads,
                data.begin() + (data.size() * (i + 1)) / num_threads); });

        pool.wait();

        watch.stop();
        double time_aggregated = watch.elapsedSeconds();
        std::cerr
            << "Aggregated in " << time_aggregated
            << " (" << n / time_aggregated << " elem/sec.)"
            << std::endl;

        size_t size_before_merge = 0;
        std::cerr << "Sizes (local): ";
        for (size_t i = 0; i < num_threads; ++i)
        {
            std::cerr << (i == 0 ? "" : ", ") << local_maps[i].size();
            size_before_merge += local_maps[i].size();
        }
        std::cerr << std::endl;

        size_t sum_size = global_map.size();
        std::cerr << "Size (global): " << sum_size << std::endl;
        size_before_merge += sum_size;

        watch.restart();

        for (size_t i = 0; i < num_threads; ++i)
            for (auto it = local_maps[i].begin(); it != local_maps[i].end(); ++it)
                global_map[it->getKey()] += it->getMapped();

        pool.wait();

        watch.stop();
        double time_merged = watch.elapsedSeconds();
        std::cerr
            << "Merged in " << time_merged
            << " (" << size_before_merge / time_merged << " elem/sec.)"
            << std::endl;

        double time_total = time_aggregated + time_merged;
        std::cerr
            << "Total in " << time_total
            << " (" << n / time_total << " elem/sec.)"
            << std::endl;

        std::cerr << "Size: " << global_map.size() << std::endl << std::endl;
    }

    if (!method || method == 417)
    {
        /** Option 4.
          * In different threads, we aggregate independently into different hash tables,
          *  until their size becomes large enough.
          * If the size of the local hash table is large, and there is no element in it,
          *  then insert it into one of 256 global hash tables, each of which is under its mutex.
          * Then merge all local hash tables into the global one.
          * This method is not so bad with a lot of threads, but worse than the second one.
          */

        std::vector<Map> local_maps(num_threads);
        std::vector<std::vector<std::vector<Key>>> buffers(num_threads, std::vector<std::vector<Key>>(MapTwoLevel2048::NUM_BUCKETS));
        std::vector<std::vector<size_t>> buffer_idx(num_threads, std::vector<size_t>(MapTwoLevel2048::NUM_BUCKETS));
        MapTwoLevel2048 global_map;
        std::vector<AlignedSmallLock> mutexes(MapTwoLevel2048::NUM_BUCKETS);

        Stopwatch watch;

        for (size_t i = 0; i < num_threads; ++i)
            pool.scheduleOrThrowOnError([&, i] { aggregate417(
                std::ref(local_maps[i]),
                std::ref(buffers[i]),
                std::ref(buffer_idx[i]),
                std::ref(global_map),
                mutexes.data(),
                data.begin() + (data.size() * i) / num_threads,
                data.begin() + (data.size() * (i + 1)) / num_threads); });

        pool.wait();

        watch.stop();
        double time_aggregated = watch.elapsedSeconds();
        std::cerr
            << "Aggregated in " << time_aggregated
            << " (" << n / time_aggregated << " elem/sec.)"
            << std::endl;

        size_t size_before_merge = 0;
        std::cerr << "Sizes (local): ";
        for (size_t i = 0; i < num_threads; ++i)
        {
            std::cerr << (i == 0 ? "" : ", ") << local_maps[i].size();
            size_before_merge += local_maps[i].size();
        }
        std::cerr << std::endl;

        size_t sum_size = global_map.size();
        std::cerr << "Size (global): " << sum_size << std::endl;
        size_before_merge += sum_size;

        watch.restart();

        for (size_t i = 0; i < num_threads; ++i)
            for (auto it = local_maps[i].begin(); it != local_maps[i].end(); ++it)
                global_map[it->getKey()] += it->getMapped();

        pool.wait();

        watch.stop();
        double time_merged = watch.elapsedSeconds();
        std::cerr
            << "Merged in " << time_merged
            << " (" << size_before_merge / time_merged << " elem/sec.)"
            << std::endl;

        double time_total = time_aggregated + time_merged;
        std::cerr
            << "Total in " << time_total
            << " (" << n / time_total << " elem/sec.)"
            << std::endl;

        std::cerr << "Size: " << global_map.size() << std::endl << std::endl;
    }

    if (!method || method == 418)
    {
        /** Option 4.
          * In different threads, we aggregate independently into different hash tables,
          *  until their size becomes large enough.
          * If the size of the local hash table is large, and there is no element in it,
          *  then insert it into one of 256 global hash tables, each of which is under its mutex.
          * Then merge all local hash tables into the global one.
          * This method is not so bad with a lot of threads, but worse than the second one.
          */

        std::vector<Map> local_maps(num_threads);
        std::vector<std::vector<std::vector<Key>>> buffers(num_threads, std::vector<std::vector<Key>>(MapTwoLevel4096::NUM_BUCKETS));
        std::vector<std::vector<size_t>> buffer_idx(num_threads, std::vector<size_t>(MapTwoLevel4096::NUM_BUCKETS));
        MapTwoLevel4096 global_map;
        std::vector<AlignedSmallLock> mutexes(MapTwoLevel4096::NUM_BUCKETS);

        Stopwatch watch;

        for (size_t i = 0; i < num_threads; ++i)
            pool.scheduleOrThrowOnError([&, i] { aggregate418(
                std::ref(local_maps[i]),
                std::ref(buffers[i]),
                std::ref(buffer_idx[i]),
                std::ref(global_map),
                mutexes.data(),
                data.begin() + (data.size() * i) / num_threads,
                data.begin() + (data.size() * (i + 1)) / num_threads); });

        pool.wait();

        watch.stop();
        double time_aggregated = watch.elapsedSeconds();
        std::cerr
            << "Aggregated in " << time_aggregated
            << " (" << n / time_aggregated << " elem/sec.)"
            << std::endl;

        size_t size_before_merge = 0;
        std::cerr << "Sizes (local): ";
        for (size_t i = 0; i < num_threads; ++i)
        {
            std::cerr << (i == 0 ? "" : ", ") << local_maps[i].size();
            size_before_merge += local_maps[i].size();
        }
        std::cerr << std::endl;

        size_t sum_size = global_map.size();
        std::cerr << "Size (global): " << sum_size << std::endl;
        size_before_merge += sum_size;

        watch.restart();

        for (size_t i = 0; i < num_threads; ++i)
            for (auto it = local_maps[i].begin(); it != local_maps[i].end(); ++it)
                global_map[it->getKey()] += it->getMapped();

        pool.wait();

        watch.stop();
        double time_merged = watch.elapsedSeconds();
        std::cerr
            << "Merged in " << time_merged
            << " (" << size_before_merge / time_merged << " elem/sec.)"
            << std::endl;

        double time_total = time_aggregated + time_merged;
        std::cerr
            << "Total in " << time_total
            << " (" << n / time_total << " elem/sec.)"
            << std::endl;

        std::cerr << "Size: " << global_map.size() << std::endl << std::endl;
    }

    if (!method || method == 4181)
    {
        /** Option 4.
          * In different threads, we aggregate independently into different hash tables,
          *  until their size becomes large enough.
          * If the size of the local hash table is large, and there is no element in it,
          *  then insert it into one of 256 global hash tables, each of which is under its mutex.
          * Then merge all local hash tables into the global one.
          * This method is not so bad with a lot of threads, but worse than the second one.
          */

        std::vector<Map> local_maps(num_threads);
        std::vector<std::vector<std::vector<Key>>> buffers(num_threads, std::vector<std::vector<Key>>(MapTwoLevel4096::NUM_BUCKETS));
        std::vector<std::vector<size_t>> buffer_idx(num_threads, std::vector<size_t>(MapTwoLevel4096::NUM_BUCKETS));
        MapTwoLevel4096 global_map;
        std::vector<AlignedSmallLock> mutexes(MapTwoLevel4096::NUM_BUCKETS);

        Stopwatch watch;

        for (size_t i = 0; i < num_threads; ++i)
            pool.scheduleOrThrowOnError([&, i] { aggregate4181(
                std::ref(local_maps[i]),
                std::ref(buffers[i]),
                std::ref(buffer_idx[i]),
                std::ref(global_map),
                mutexes.data(),
                data.begin() + (data.size() * i) / num_threads,
                data.begin() + (data.size() * (i + 1)) / num_threads); });

        pool.wait();

        watch.stop();
        double time_aggregated = watch.elapsedSeconds();
        std::cerr
            << "Aggregated in " << time_aggregated
            << " (" << n / time_aggregated << " elem/sec.)"
            << std::endl;

        size_t size_before_merge = 0;
        std::cerr << "Sizes (local): ";
        for (size_t i = 0; i < num_threads; ++i)
        {
            std::cerr << (i == 0 ? "" : ", ") << local_maps[i].size();
            size_before_merge += local_maps[i].size();
        }
        std::cerr << std::endl;

        size_t sum_size = global_map.size();
        std::cerr << "Size (global): " << sum_size << std::endl;
        size_before_merge += sum_size;

        watch.restart();

        for (size_t i = 0; i < num_threads; ++i)
            for (auto it = local_maps[i].begin(); it != local_maps[i].end(); ++it)
                global_map[it->getKey()] += it->getMapped();

        pool.wait();

        watch.stop();
        double time_merged = watch.elapsedSeconds();
        std::cerr
            << "Merged in " << time_merged
            << " (" << size_before_merge / time_merged << " elem/sec.)"
            << std::endl;

        double time_total = time_aggregated + time_merged;
        std::cerr
            << "Total in " << time_total
            << " (" << n / time_total << " elem/sec.)"
            << std::endl;

        std::cerr << "Size: " << global_map.size() << std::endl << std::endl;
    }

    if (!method || method == 42)
    {
        /** Option 4.
          * In different threads, we aggregate independently into different hash tables,
          *  until their size becomes large enough.
          * If the size of the local hash table is large, and there is no element in it,
          *  then insert it into one of 256 global hash tables, each of which is under its mutex.
          * Then merge all local hash tables into the global one.
          * This method is not so bad with a lot of threads, but worse than the second one.
          */

        std::vector<Map> local_maps(num_threads);
        std::vector<Map> global_maps(num_threads);
        std::vector<AlignedSmallLock> mutexes(num_threads);

        Stopwatch watch;

        for (size_t i = 0; i < num_threads; ++i)
            pool.scheduleOrThrowOnError([&, i] { aggregate42(
                std::ref(local_maps[i]),
                global_maps.data(),
                mutexes.data(),
                data.begin() + (data.size() * i) / num_threads,
                data.begin() + (data.size() * (i + 1)) / num_threads,
                num_threads); });

        pool.wait();

        watch.stop();
        double time_aggregated = watch.elapsedSeconds();
        std::cerr
            << "Aggregated in " << time_aggregated
            << " (" << n / time_aggregated << " elem/sec.)"
            << std::endl;

        size_t size_before_merge = 0;
        std::cerr << "Sizes (local): ";
        for (size_t i = 0; i < num_threads; ++i)
        {
            std::cerr << (i == 0 ? "" : ", ") << local_maps[i].size();
            size_before_merge += local_maps[i].size();
        }
        std::cerr << std::endl;

        size_t sum_size = 0;
        for (size_t i = 0; i < num_threads; ++i)
            sum_size += global_maps[i].size();
        std::cerr << "Size (global): " << sum_size << std::endl;

        watch.restart();

        __uint128_t num_threads_128 = num_threads;
        for (size_t i = 0; i < num_threads; ++i)
            for (auto it = local_maps[i].begin(); it != local_maps[i].end(); ++it)
            {
                size_t bucket_num = getThreadNum(it.getHash(), num_threads_128);
                global_maps[bucket_num][it->getKey()] += it->getMapped();
            }

        pool.wait();

        watch.stop();
        double time_merged = watch.elapsedSeconds();
        std::cerr
            << "Merged in " << time_merged
            << " (" << size_before_merge / time_merged << " elem/sec.)"
            << std::endl;

        double time_total = time_aggregated + time_merged;
        std::cerr
            << "Total in " << time_total
            << " (" << n / time_total << " elem/sec.)"
            << std::endl;

        sum_size = 0;
        for (size_t i = 0; i < num_threads; ++i)
            sum_size += global_maps[i].size();
        std::cerr << "Size: " << sum_size << std::endl << std::endl;
    }

    if (!method || method == 43)
    {
        /** Option 4.
          * In different threads, we aggregate independently into different hash tables,
          *  until their size becomes large enough.
          * If the size of the local hash table is large, and there is no element in it,
          *  then insert it into one of 256 global hash tables, each of which is under its mutex.
          * Then merge all local hash tables into the global one.
          * This method is not so bad with a lot of threads, but worse than the second one.
          */

        std::vector<Map> local_maps(num_threads);
        std::vector<Map> global_maps(num_threads);
        std::vector<std::vector<std::list<Key>>> buffers(num_threads, std::vector<std::list<Key>>(num_threads));
        std::vector<std::vector<std::pair<std::list<Key>::iterator, std::list<Key>::iterator>>> buffer_ranges(
            num_threads, std::vector<std::pair<std::list<Key>::iterator, std::list<Key>::iterator>>(num_threads));
        for (size_t i = 0; i < num_threads; ++i)
            for (size_t j = 0; j < num_threads; ++j)
                buffer_ranges[i][j] = {buffers[i][j].end(), buffers[i][j].end()};
        std::vector<std::vector<AlignedSmallLockExt>> mutexes(num_threads);
        for (size_t i = 0; i < num_threads; ++i)
            mutexes[i] = std::vector<AlignedSmallLockExt>(num_threads);

        Stopwatch watch;

        for (size_t i = 0; i < num_threads; ++i)
            pool.scheduleOrThrowOnError([&, i] { aggregate43(
                std::ref(local_maps[i]),
                std::ref(global_maps[i]),
                std::ref(buffers),
                std::ref(buffer_ranges),
                std::ref(mutexes),
                data.begin() + (data.size() * i) / num_threads,
                data.begin() + (data.size() * (i + 1)) / num_threads,
                i,
                num_threads); });

        pool.wait();

        watch.stop();
        double time_aggregated = watch.elapsedSeconds();
        std::cerr
            << "Aggregated in " << time_aggregated
            << " (" << n / time_aggregated << " elem/sec.)"
            << std::endl;

        size_t size_before_merge = 0;
        std::cerr << "Sizes (local): ";
        for (size_t i = 0; i < num_threads; ++i)
        {
            std::cerr << (i == 0 ? "" : ", ") << local_maps[i].size();
            size_before_merge += local_maps[i].size();
        }
        std::cerr << std::endl;

        std::cerr << "Sizes (global): ";
        size_t sum_size = 0;
        for (size_t i = 0; i < num_threads; ++i)
        {
            std::cerr << (i == 0 ? "" : ", ") << global_maps[i].size();
            sum_size += global_maps[i].size();
        }
        std::cerr << std::endl;
        std::cerr << "Size (global): " << sum_size << std::endl;
        size_before_merge += sum_size;

        watch.restart();

        __uint128_t num_threads_128 = num_threads;
        for (size_t i = 0; i < num_threads; ++i)
            for (auto it = local_maps[i].begin(); it != local_maps[i].end(); ++it)
            {
                size_t bucket_num = getThreadNum(it.getHash(), num_threads_128);
                global_maps[bucket_num][it->getKey()] += it->getMapped();
            }

        for (size_t i = 0; i < num_threads; ++i)
            for (size_t j = 0; j < num_threads; ++j)
                if (i != j && !buffers[i][j].empty() && (buffer_ranges[i][j].second != std::prev(buffers[i][j].end())
                    || mutexes[i][j].is_ready()))
                {
                    auto it = mutexes[i][j].is_ready() ? buffer_ranges[i][j].first : std::next(buffer_ranges[i][j].second);
                    while (it != buffers[i][j].end())
                    {
                        ++global_maps[j][*it];
                        ++it;
                    }
                }

        watch.stop();

        double time_merged = watch.elapsedSeconds();
        std::cerr
            << "Merged in " << time_merged
            << " (" << size_before_merge / time_merged << " elem/sec.)"
            << std::endl;

        double time_total = time_aggregated + time_merged;
        std::cerr
            << "Total in " << time_total
            << " (" << n / time_total << " elem/sec.)"
            << std::endl;

        sum_size = 0;
        for (size_t i = 0; i < num_threads; ++i)
            sum_size += global_maps[i].size();
        std::cerr << "Size: " << sum_size << std::endl << std::endl;
    }

    if (!method || method == 431)
    {
        /** Option 4.
          * In different threads, we aggregate independently into different hash tables,
          *  until their size becomes large enough.
          * If the size of the local hash table is large, and there is no element in it,
          *  then insert it into one of 256 global hash tables, each of which is under its mutex.
          * Then merge all local hash tables into the global one.
          * This method is not so bad with a lot of threads, but worse than the second one.
          */

        std::vector<Map> local_maps(num_threads);
        std::vector<Map> global_maps(num_threads);
        std::vector<std::vector<std::list<Key>>> buffers(num_threads, std::vector<std::list<Key>>(num_threads));
        std::vector<std::vector<std::pair<std::list<Key>::iterator, std::list<Key>::iterator>>> buffer_ranges(
            num_threads, std::vector<std::pair<std::list<Key>::iterator, std::list<Key>::iterator>>(num_threads));
        for (size_t i = 0; i < num_threads; ++i)
            for (size_t j = 0; j < num_threads; ++j)
                buffer_ranges[i][j] = {buffers[i][j].end(), buffers[i][j].end()};
        std::vector<std::vector<AlignedSmallLockExt>> mutexes(num_threads);
        for (size_t i = 0; i < num_threads; ++i)
            mutexes[i] = std::vector<AlignedSmallLockExt>(num_threads);

        Stopwatch watch;

        for (size_t i = 0; i < num_threads; ++i)
            pool.scheduleOrThrowOnError([&, i] { aggregate431(
                std::ref(local_maps[i]),
                std::ref(global_maps[i]),
                std::ref(buffers),
                std::ref(buffer_ranges),
                std::ref(mutexes),
                data.begin() + (data.size() * i) / num_threads,
                data.begin() + (data.size() * (i + 1)) / num_threads,
                i,
                num_threads); });

        pool.wait();

        watch.stop();
        double time_aggregated = watch.elapsedSeconds();
        std::cerr
            << "Aggregated in " << time_aggregated
            << " (" << n / time_aggregated << " elem/sec.)"
            << std::endl;

        size_t size_before_merge = 0;
        std::cerr << "Sizes (local): ";
        for (size_t i = 0; i < num_threads; ++i)
        {
            std::cerr << (i == 0 ? "" : ", ") << local_maps[i].size();
            size_before_merge += local_maps[i].size();
        }
        std::cerr << std::endl;

        std::cerr << "Sizes (global): ";
        size_t sum_size = 0;
        for (size_t i = 0; i < num_threads; ++i)
        {
            std::cerr << (i == 0 ? "" : ", ") << global_maps[i].size();
            sum_size += global_maps[i].size();
        }
        std::cerr << std::endl;
        std::cerr << "Size (global): " << sum_size << std::endl;
        size_before_merge += sum_size;

        watch.restart();

        __uint128_t num_threads_128 = num_threads;
        for (size_t i = 0; i < num_threads; ++i)
            for (auto it = local_maps[i].begin(); it != local_maps[i].end(); ++it)
            {
                size_t bucket_num = getThreadNum(it.getHash(), num_threads_128);
                global_maps[bucket_num][it->getKey()] += it->getMapped();
            }

        for (size_t i = 0; i < num_threads; ++i)
            pool.scheduleOrThrowOnError([&, i] { merge431(
                 std::ref(global_maps[i]),
                 std::ref(buffers),
                 std::ref(buffer_ranges),
                 std::ref(mutexes),
                 i,
                 num_threads); });

        pool.wait();

        watch.stop();

        double time_merged = watch.elapsedSeconds();
        std::cerr
            << "Merged in " << time_merged
            << " (" << size_before_merge / time_merged << " elem/sec.)"
            << std::endl;

        double time_total = time_aggregated + time_merged;
        std::cerr
            << "Total in " << time_total
            << " (" << n / time_total << " elem/sec.)"
            << std::endl;

        sum_size = 0;
        for (size_t i = 0; i < num_threads; ++i)
            sum_size += global_maps[i].size();
        std::cerr << "Size: " << sum_size << std::endl << std::endl;
    }

    if (!method || method == 7)
    {
        /** Option 7.
         * The simplest baseline. One hash table with one thread and optimization for consecutive identical values.
         * Just to compare.
         */

        Map global_map;

        Stopwatch watch;

        aggregate12(global_map, data.begin(), data.end());

        watch.stop();
        double time_total = watch.elapsedSeconds();
        std::cerr
            << "Aggregated in " << time_total
            << " (" << n / time_total << " elem/sec.)"
            << std::endl;

        std::cerr
            << "Total in " << time_total
            << " (" << n / time_total << " elem/sec.)"
            << std::endl;

        std::cerr << "Size: " << global_map.size() << std::endl << std::endl;
    }

/*    if (!method || method == 5)
    {
    */  /** Option 5.
          * In different threads, we aggregate independently into different hash tables,
          *  until their size becomes large enough.
          * If the size of the local hash table is large and there is no element in it,
          *  then insert it into one global hash table containing small latches in each cell,
          *  and if the latch can not be captured, then insert it into the local one.
          * Then merge all local hash tables into the global one.
          */
/*
        Map local_maps[num_threads];
        MapSmallLocks global_map;

        Stopwatch watch;

        for (size_t i = 0; i < num_threads; ++i)
            pool.scheduleOrThrowOnError([&] { aggregate5(
                std::ref(local_maps[i]),
                std::ref(global_map),
                data.begin() + (data.size() * i) / num_threads,
                data.begin() + (data.size() * (i + 1)) / num_threads); });

        pool.wait();

        watch.stop();
        double time_aggregated = watch.elapsedSeconds();
        std::cerr
            << "Aggregated in " << time_aggregated
            << " (" << n / time_aggregated << " elem/sec.)"
            << std::endl;

        size_t size_before_merge = 0;
        std::cerr << "Sizes (local): ";
        for (size_t i = 0; i < num_threads; ++i)
        {
            std::cerr << (i == 0 ? "" : ", ") << local_maps[i].size();
            size_before_merge += local_maps[i].size();
        }
        std::cerr << std::endl;
        std::cerr << "Size (global): " << global_map.size() << std::endl;
        size_before_merge += global_map.size();

        watch.restart();

        for (size_t i = 0; i < num_threads; ++i)
            for (auto it = local_maps[i].begin(); it != local_maps[i].end(); ++it)
                global_map.insert(std::make_pair(it->first, 0)).first->second += it->second;

        pool.wait();

        watch.stop();
        double time_merged = watch.elapsedSeconds();
        std::cerr
            << "Merged in " << time_merged
            << " (" << size_before_merge / time_merged << " elem/sec.)"
            << std::endl;

        double time_total = time_aggregated + time_merged;
        std::cerr
            << "Total in " << time_total
            << " (" << n / time_total << " elem/sec.)"
            << std::endl;

        std::cerr << "Size: " << global_map.size() << std::endl << std::endl;
    }*/

    /*if (!method || method == 6)
    {
        *//** Option 6.
          * In different threads, we aggregate independently into different hash tables.
          * Then "merge" them, passing them in the same order of the keys.
          * Quite a slow option.
          */
/*
        std::vector<Map> maps(num_threads);

        Stopwatch watch;

        for (size_t i = 0; i < num_threads; ++i)
            pool.scheduleOrThrowOnError([&] { aggregate1(
                std::ref(maps[i]),
                data.begin() + (data.size() * i) / num_threads,
                data.begin() + (data.size() * (i + 1)) / num_threads); });

        pool.wait();

        watch.stop();
        double time_aggregated = watch.elapsedSeconds();
        std::cerr
            << "Aggregated in " << time_aggregated
            << " (" << n / time_aggregated << " elem/sec.)"
            << std::endl;

        size_t size_before_merge = 0;
        std::cerr << "Sizes: ";
        for (size_t i = 0; i < num_threads; ++i)
        {
            std::cerr << (i == 0 ? "" : ", ") << maps[i].size();
            size_before_merge += maps[i].size();
        }
        std::cerr << std::endl;

        watch.restart();

        using Maps = std::vector<Map *>;
        Maps maps_to_merge(num_threads);
        for (size_t i = 0; i < num_threads; ++i)
            maps_to_merge[i] = &maps[i];

        size_t size = 0;

        for (size_t i = 0; i < 100; ++i)
        processMergedHashTables(maps_to_merge,
            [] (Map::value_type & dst, const Map::value_type & src) { dst.second += src.second; },
            [&] (const Map::value_type & dst) { ++size; });

        watch.stop();
        double time_merged = watch.elapsedSeconds();
        std::cerr
            << "Merged in " << time_merged
            << " (" << size_before_merge / time_merged << " elem/sec.)"
            << std::endl;

        double time_total = time_aggregated + time_merged;
        std::cerr
            << "Total in " << time_total
            << " (" << n / time_total << " elem/sec.)"
            << std::endl;
        std::cerr << "Size: " << size << std::endl << std::endl;
    }*/

    return 0;
}

