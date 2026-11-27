#!/bin/bash
# collapse: seed the mirror (no-op module build), then dump the x86 and A64 constant graphs.
mkdir -p afklogs colback
MODE=mod MODS=Fl4Core SEED=/data/fl4/lake/FL4-int26 bash /data/fl4/afk-build.sh > afklogs/seed.out 2>&1; grep -E '^(SEEDED|SEEDFAIL|OLEANS|BUILD|ERRORS)' afklogs/seed.out
export ELAN_HOME=/data/fl4/elan PATH=/data/fl4/leanq-root/bin:/data/fl4/elan/bin:$PATH
cd proofs
for f in depdump depdumpA64; do ( time lake env lean scratch/collapse/$f.lean > ../afklogs/$f.out 2>&1 ) 2>> ../afklogs/time.txt; echo "$f rc=$?"; grep -E 'DUMPED|error|Maximum resident|Elapsed' ../afklogs/$f.out | head; done
gzip -c depdump.tsv > ../colback/depdump.tsv.gz; gzip -c depdumpA64.tsv > ../colback/depdumpA64.tsv.gz; rm -f depdump.tsv depdumpA64.tsv
ls -la ../colback
