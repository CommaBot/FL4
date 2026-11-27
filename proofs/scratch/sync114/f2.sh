#!/bin/bash
# s114-f2: full root build with the axiom sweep, then the AArch64 build. Run after f1 (P0 regenerated) in the same mirror.
mkdir -p afklogs s114/back2; rm -f s114/f2.tgz
cp proofs/scratch/int21/rssrun.sh s114/rssrun.sh 2>/dev/null
MODE=build NAX=100000 AX=proofs/scratch/sync114/s114_ax.lean SEED=${SEED:-FL4-int22} bash s114/rssrun.sh > afklogs/s114-build.out 2>&1; echo BUILD_EXIT $?
grep -E '^(BUILD|ERRORS|SORRY|JOBS|OLEANS|AX)' afklogs/s114-build.out
grep -E 'Build completed|error: build failed' afklogs/b-build.log | tail -2
grep -n '^error' -A30 afklogs/b-build.log | cut -c1-260 | head -200
MODE=a64 SEED=${SEED:-FL4-int22} bash /data/fl4/afk-build.sh > afklogs/s114-a64.out 2>&1; echo A64_EXIT $?
grep -E '^(BUILD|ERRORS|SORRY|JOBS)' afklogs/s114-a64.out
grep -E 'Build completed|error: build failed' afklogs/b-a64.log | tail -2
grep -n '^error' -A20 afklogs/b-a64.log | cut -c1-260 | head -80
cp afklogs/s114-build.out afklogs/s114-a64.out afklogs/b-build.log afklogs/b-a64.log afklogs/rss-build.txt s114/back2/ 2>/dev/null
tar czf s114/f2.tgz s114/back2
