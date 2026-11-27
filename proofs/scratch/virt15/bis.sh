#!/bin/bash
# usage: bis.sh files... : check scratch files in order, stop at the first that errors or is killed
for x in "$@"; do
  out=$(MAXKB=${MAXKB:-8000000} TO=${TO:-300} F=$x N=40 bash proofs/scratch/virt12/run.sh 2>&1); echo "$out"
  echo "$out" | grep -q 'KILL\|scratch exit [^0]\|errors [1-9]' && { echo "STOP at $x"; exit 1; }
done
