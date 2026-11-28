#!/bin/bash
# usage: run3.sh <key> <file to check> "<modules to lake-build if the check is clean>"
k=$1; f=$2; m=$3
bash proofs/scratch/a64/g59/chk.sh $f | tee afklogs/run3-$k.txt
grep -q "^EXIT 0" afklogs/run3-$k.txt && SEED=/data/fl4/lake/FL4-int18 bash proofs/scratch/a64/g33b.sh "$m" $k
exit 0
