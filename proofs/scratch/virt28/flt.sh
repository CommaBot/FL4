#!/bin/bash
# run.sh with output filtered to error headers + a few lines of each, plus lake build summaries
bash proofs/scratch/virt28/run.sh "$@" 2>&1 | awk '/^=== /{print; next} /^(Build|error|✖|⚠ )/{print; next} /: error/{print; c=6; next} c>0{print; c--}'
for M in "$@"; do f=proofs/.lake/build/lib/lean/$(echo $M | tr . /).olean; ls -la $f 2>&1 | awk '{print $5, $6, $7, $8, $9}'; done
