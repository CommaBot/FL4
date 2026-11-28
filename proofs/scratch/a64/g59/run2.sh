#!/bin/bash
# usage: run2.sh <key> "<modules to lake-build first>" <files to check...>
k=$1; m=$2; shift 2
[ -n "$m" ] && SEED=/data/fl4/lake/FL4-int18 bash proofs/scratch/a64/g33b.sh "$m" $k
bash proofs/scratch/a64/g59/chk.sh "$@"
