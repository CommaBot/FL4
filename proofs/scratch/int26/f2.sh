#!/bin/bash
# int26-f2 (afkprover): incremental x86 root build + axiom sweep axint26 after the BootStore fix (A64 unaffected; built in f1).
# Run from the repo root of the mirror. SEED defaults to afkprover's fully built par/sync114 .lake.
mkdir -p afklogs int26back2; S=${SEED:-/data/fl4/lake/FL4-sync114}
MODE=build NAX=100000 AX=proofs/scratch/int26/axint26.lean SEED=$S bash proofs/scratch/int26/rssrun.sh > afklogs/int26-build.out 2>&1; echo BUILD_EXIT $?
grep -E '^(SEEDED|SEEDFAIL|BUILD|ERRORS|SORRY|JOBS|OLEANS|AX)' afklogs/int26-build.out
grep -E 'Build completed|error: build failed' afklogs/b-build.log | tail -2
cp afklogs/int26-*.out afklogs/b-build.log afklogs/b-a64.log afklogs/rss-build.txt int26back2/ 2>/dev/null
tar czf int26back2.tgz int26back2
