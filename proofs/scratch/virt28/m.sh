#!/bin/bash
# usage: MODS="Fl4Proofs.P3.X ..." bash proofs/scratch/virt28/m.sh : seeded MODE=mod build, then the errors of the Virt* files.
MODE=mod MODS="$MODS" SEED=/data/fl4/lake/FL4-virt bash /data/fl4/afk-build.sh 2>&1 | grep -v "^error\|^-\|^Some" | tail -8
echo "=== errors"
grep -c "^error: Fl4Proofs/P3/" afklogs/b-mod.log
awk '/^error: Fl4Proofs\/P3\//{p=1;c=0} /^(warning|info|⚠|✔|✖|Some)/{p=0} p{if(c<22)print; c++}' afklogs/b-mod.log | head -${N:-300}
