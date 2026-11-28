#!/bin/bash
# p3mc gen 55: root build (MODS=Fl4Proofs) + AX, then depdump / tydump / axall of the built tree into p3mcback/$TAG.
TAG=${TAG:-d}; mkdir -p afklogs p3mcback/$TAG
MODE=mod MODS=${MODS:-Fl4Proofs} AX=${AX:-proofs/scratch/p3mc/p3mc54_ax.lean} SEED=${SEED:-/data/fl4/lake/FL4-int26} bash /data/fl4/afk-build.sh > afklogs/p55-root.out 2>&1; echo BUILD_EXIT $?
grep -E '^(SEEDED|SEEDFAIL|BUILD|ERRORS|SORRY|JOBS|OLEANS|AX)' afklogs/p55-root.out
grep -E 'Build completed|error: build failed' afklogs/b-mod.log | tail -2
grep -E '^error' afklogs/b-mod.log | head -40
cp afklogs/p55-root.out p3mcback/$TAG/ 2>/dev/null
grep -q 'Build completed successfully' afklogs/b-mod.log || exit 0
[ -n "$NODUMP" ] && exit 0
export ELAN_HOME=/data/fl4/elan PATH=/data/fl4/leanq-root/bin:/data/fl4/elan/bin:$PATH
cd proofs
for f in ${DUMPS:-depdump tydump axall}; do
  ( time lake env lean scratch/collapse/$f.lean > ../afklogs/$f.out 2>&1 ) 2> ../afklogs/$f.time; echo "$f rc=$?"
  grep -E 'DUMPED|AXALL|error' ../afklogs/$f.out | cut -c1-600 | head -6; grep real ../afklogs/$f.time
  [ -f $f.tsv ] && { gzip -c $f.tsv > ../p3mcback/$TAG/$f.tsv.gz; rm -f $f.tsv; }
  cp ../afklogs/$f.out ../p3mcback/$TAG/
done
ls -la ../p3mcback/$TAG
