#!/bin/bash
# int26-f3 (afkprover): incremental x86 root build + axiom sweep axint26 after stage 2 (p3J, virt 28, mmuAD 41-42a), then MODE=a64 (up-to-date check).
# Run from the repo root of the mirror. SEED defaults to afkprover's fully built par/sync114 .lake.
mkdir -p afklogs int26back3; S=${SEED:-/data/fl4/lake/FL4-sync114}
MODE=build NAX=100000 AX=proofs/scratch/int26/axint26.lean SEED=$S bash proofs/scratch/int26/rssrun.sh > afklogs/int26-build.out 2>&1; echo BUILD_EXIT $?
grep -E '^(SEEDED|SEEDFAIL|BUILD|ERRORS|SORRY|JOBS|OLEANS|AX)' afklogs/int26-build.out
grep -E 'Build completed|error: build failed' afklogs/b-build.log | tail -2
MODE=a64 SEED=$S bash /data/fl4/afk-build.sh > afklogs/int26-a64.out 2>&1; echo A64_EXIT $?; grep -E "^(BUILD|ERRORS|SORRY|JOBS)" afklogs/int26-a64.out; tail -1 afklogs/b-a64.log
cp afklogs/int26-*.out afklogs/b-build.log afklogs/b-a64.log afklogs/rss-build.txt int26back3/ 2>/dev/null
tar czf int26back3.tgz int26back3
