#pragma once
#include <Processors/IProcessor.h>
#include <Interpreters/SubqueryForSet.h>
#include <Common/Stopwatch.h>

namespace DB
{

/// This processor creates sets during execution.
/// Don't return any data. Sets are created when Finish status is returned.
/// In general, several work() methods need to be called to finish.
/// TODO: several independent processors can be created for each subquery. Make subquery a piece of pipeline.
class CreatingSetsTransform : public IProcessor
{
public:
    CreatingSetsTransform(
        Block out_header,
        const SubqueriesForSets & subqueries_for_sets_,
        const SizeLimits & network_transfer_limits);

    String getName() const override { return "CreatingSetsTransform"; }
    Status prepare() override;
    void work() override;

protected:
    bool finished = false;

private:
    SubqueriesForSets subqueries_for_sets;
    SubqueriesForSets::iterator cur_subquery;

    bool started_cur_subquery = false;
    BlockOutputStreamPtr table_out;
    UInt64 elapsed_nanoseconds = 0;

    bool done_with_set = true;
    bool done_with_join = true;
    bool done_with_table = true;

    SizeLimits network_transfer_limits;

    size_t rows_to_transfer = 0;
    size_t bytes_to_transfer = 0;

    using Logger = Poco::Logger;
    Logger * log = &Logger::get("CreatingSetsBlockInputStream");

    void startSubquery(SubqueryForSet & subquery);
    void finishSubquery(SubqueryForSet & subquery);
};

}
