#!/bin/bash
# collapse: x86 tydump of the *before* tree, using int26's built mirror FL4-int26 read-only (tree = main afdfbe275).
# Run from this mirror's repo root; output colback/before/tydump.tsv.gz.
W=/root/.monoid/remote/sessions/de7adef11839efd864675761d4db585096cfaf4f28add8c1607f02966671d599/work
mkdir -p colback/before; OUT=$PWD/colback/before/tydump.tsv; SRC=$PWD/proofs/scratch/collapse/tydump.lean
export ELAN_HOME=/data/fl4/elan PATH=/data/fl4/leanq-root/bin:/data/fl4/elan/bin:$PATH
( cd $W/FL4-int26 && git log --oneline -1 2>/dev/null; cd proofs && TYOUT=$OUT lake env lean $SRC ) > afklogs/before.out 2>&1; echo "before rc=$?"
grep -E 'TYDUMPED|error' afklogs/before.out | head; gzip -f $OUT; ls -la colback/before
