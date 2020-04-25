#!/bin/bash

for file in RegionID UserID WatchID RefererHash ; do
 for size in 30000 100000 300000 1000000 10000000 100000000 200000000; do
   echo
   BEST_METHOD=0
   BEST_RESULT=9999999.9

   for method in `#1 12` `#11` `#13 14 15` `#151` `#16 161` `#17` `#171` `#172 173` `#2` 22 `#23 24 25` `#3 33` `#4` `#41 411` `#412 413 414` `#415` 416 `#417` 418 4181 `#42` `#43` 431 `#7`; do
    echo -ne $file size=$size method=$method '';
    for threads in 16 24 32; do
      for i in {0..1}; do
              ./build/src/Common/tests/parallel_aggregation $size $threads $method < /home/palasonic/ClickHouse/${file}.bin 2>&1 |
        grep 'Total in' | grep -oE 'Total in [0-9\.]+';
      done;
    done | mawk -W interactive 'BEGIN{x=1000.0} { if ($3 < x) { x = $3 }; printf("-") } END { print x }' |
       tee /tmp/parallel_aggregation_res;

    CUR_RESULT=$(cat /tmp/parallel_aggregation_res | tr -d '-')
    if (( $(echo "$CUR_RESULT < $BEST_RESULT" | bc -l) )); then
     BEST_METHOD=$method
     BEST_RESULT=$CUR_RESULT
    fi;
    done;
   echo Best: $BEST_METHOD - $BEST_RESULT
 done;
 printf %60s |tr " " "-"
done;

