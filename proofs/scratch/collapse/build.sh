#!/bin/bash
# collapse: x86 root build (with per-module RSS) then A64 root build, on afkprover; optional AX=… for the x86 sweep.
# Run from the mirror's repo root. Output summary on stdout, logs under afklogs/, copies under colback/$TAG.
TAG=${TAG:-b}; mkdir -p afklogs colback/$TAG; S=${SEED:-/data/fl4/lake/FL4-int26}
T0=$(date +%s)
MODE=build NAX=${NAX:-100000} AX=$AX SEED=$S bash proofs/scratch/int26/rssrun.sh > afklogs/col-build.out 2>&1; echo BUILD_EXIT $?
grep -E '^(SEEDED|SEEDFAIL|BUILD|ERRORS|SORRY|JOBS|OLEANS|AX|RSS_OVER)' afklogs/col-build.out
grep -E 'Build completed|error: build failed' afklogs/b-build.log | tail -2
T1=$(date +%s)
MODE=a64 SEED=$S bash /data/fl4/afk-build.sh > afklogs/col-a64.out 2>&1; echo A64_EXIT $?
grep -E "^(BUILD|ERRORS|SORRY|JOBS)" afklogs/col-a64.out; tail -1 afklogs/b-a64.log
echo WALL x86=$((T1-T0)) a64=$(( $(date +%s)-T1 ))
echo OLEANS_NOW $(find proofs/.lake/build/lib/lean -name '*.olean' | wc -l)
head -5 afklogs/rss-build.txt
cp afklogs/col-*.out afklogs/b-build.log afklogs/b-a64.log afklogs/rss-build.txt colback/$TAG/ 2>/dev/null
grep -E '^error' afklogs/b-build.log afklogs/b-a64.log | head -40
