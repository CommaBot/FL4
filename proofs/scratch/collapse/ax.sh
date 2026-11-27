#!/bin/bash
# collapse: tydump + full axiom sweeps (x86, A64) on the mirror's built .lake. TAG names the output dir.
TAG=${TAG:-t}; mkdir -p colback/$TAG afklogs
export ELAN_HOME=/data/fl4/elan PATH=/data/fl4/leanq-root/bin:/data/fl4/elan/bin:$PATH
cd proofs
for f in axall axallA64 tydump tydumpA64; do
  ( time lake env lean scratch/collapse/$f.lean > ../afklogs/$f.out 2>&1 ) 2> ../afklogs/$f.time; echo "$f rc=$?"
  grep -E 'AXALL|TYDUMPED|error' ../afklogs/$f.out | cut -c1-600 | head -6; grep real ../afklogs/$f.time
  [ -f $f.tsv ] && { gzip -c $f.tsv > ../colback/$TAG/$f.tsv.gz; rm -f $f.tsv; }
  cp ../afklogs/$f.out ../colback/$TAG/
done
