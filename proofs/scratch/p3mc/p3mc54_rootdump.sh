#!/bin/bash
# p3mc gen 54: root build + AX, then (if green) the collapse depdump of the merged tree into p3mcback/.
mkdir -p afklogs p3mcback
MODE=mod MODS=Fl4Proofs AX=${AX:-proofs/scratch/p3mc/p3mc54_ax.lean} SEED=${SEED:-/data/fl4/lake/FL4-int26} bash /data/fl4/afk-build.sh > afklogs/p54-root.out 2>&1; echo BUILD_EXIT $?
grep -E '^(SEEDED|SEEDFAIL|BUILD|ERRORS|SORRY|JOBS|OLEANS|AX)' afklogs/p54-root.out
grep -E 'Build completed|error: build failed' afklogs/b-mod.log | tail -2
grep -E '^error' afklogs/b-mod.log | head -30
cp afklogs/p54-root.out afklogs/b-mod.log p3mcback/ 2>/dev/null
grep -q 'Build completed successfully' afklogs/b-mod.log || exit 0
[ -n "$NODUMP" ] && exit 0
export ELAN_HOME=/data/fl4/elan PATH=/data/fl4/leanq-root/bin:/data/fl4/elan/bin:$PATH
cd proofs && ( time lake env lean scratch/collapse/depdump.lean > ../afklogs/depdump.out 2>&1 ) 2>> ../afklogs/time.txt; echo "depdump rc=$?"
grep -E 'DUMPED|error' ../afklogs/depdump.out | head; gzip -c depdump.tsv > ../p3mcback/depdump.tsv.gz; rm -f depdump.tsv; ls -la ../p3mcback
