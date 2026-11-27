#!/bin/bash
# collapse: run tydump (x86, A64) against the mirror's built .lake; TAG names the output.
TAG=${TAG:-t}; mkdir -p colback/$TAG afklogs
export ELAN_HOME=/data/fl4/elan PATH=/data/fl4/leanq-root/bin:/data/fl4/elan/bin:$PATH
cd proofs
for f in tydump tydumpA64; do lake env lean scratch/collapse/$f.lean > ../afklogs/$f.out 2>&1; echo "$f rc=$?"; grep -E 'TYDUMPED|error' ../afklogs/$f.out | head -5; gzip -c $f.tsv > ../colback/$TAG/$f.tsv.gz; rm -f $f.tsv; done
