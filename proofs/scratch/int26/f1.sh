#!/bin/bash
# int26-f1 (afkprover): full x86 root build + axiom sweep axint26, then MODE=a64, then the A64 sweep a64/a64_ax2.lean.
# Run from the repo root of the mirror. SEED defaults to afkprover's fully built par/sync114 .lake.
mkdir -p afklogs int26back; S=${SEED:-/data/fl4/lake/FL4-sync114}
MODE=build NAX=100000 AX=proofs/scratch/int26/axint26.lean SEED=$S bash proofs/scratch/int26/rssrun.sh > afklogs/int26-build.out 2>&1; echo BUILD_EXIT $?
grep -E '^(SEEDED|SEEDFAIL|BUILD|ERRORS|SORRY|JOBS|OLEANS|AX)' afklogs/int26-build.out
grep -E 'Build completed|error: build failed' afklogs/b-build.log | tail -2
MODE=a64 SEED=$S bash /data/fl4/afk-build.sh > afklogs/int26-a64.out 2>&1; echo A64_EXIT $?
grep -E '^(BUILD|ERRORS|SORRY|JOBS)' afklogs/int26-a64.out
grep -E 'Build completed|error: build failed' afklogs/b-a64.log | tail -2
bash proofs/scratch/int26/axrun.sh scratch/a64/a64_ax2.lean afklogs/int26-axa64.out
cp afklogs/int26-*.out afklogs/b-build.log afklogs/b-a64.log afklogs/rss-build.txt int26back/ 2>/dev/null
tar czf int26back.tgz int26back
