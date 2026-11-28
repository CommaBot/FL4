#!/bin/bash
# int27-f1 (afkprover): stage 1 (mmuAD 31c42e2e5, p3J f23736c37, p3mc 4eaff1e02 on main 5baf782fc).
# x86 root build + axint27 sweep, MODE=a64, then the whole-environment sweeps collapse/axall.lean and axallA64.lean.
# Run from the repo root of the mirror. SEED: absolute path of a built .lake.
mkdir -p afklogs int27back; S=${SEED:-/data/fl4/lake/FL4-p3mc}
MODE=build NAX=100000 AX=proofs/scratch/int27/axint27.lean SEED=$S bash proofs/scratch/int27/rssrun.sh > afklogs/int27-build.out 2>&1; echo BUILD_EXIT $?
grep -E '^(SEEDED|SEEDFAIL|BUILD|ERRORS|SORRY|JOBS|OLEANS|AX)' afklogs/int27-build.out
grep -E 'Build completed|error: build failed' afklogs/b-build.log | tail -2
MODE=a64 SEED=$S bash /data/fl4/afk-build.sh > afklogs/int27-a64.out 2>&1; echo A64_EXIT $?
grep -E '^(BUILD|ERRORS|SORRY|JOBS)' afklogs/int27-a64.out
grep -E 'Build completed|error: build failed' afklogs/b-a64.log | tail -2
for f in axall axallA64; do bash proofs/scratch/int27/axrun.sh scratch/collapse/$f.lean afklogs/int27-$f.out; grep -E 'AXALL|error' afklogs/int27-$f.out | cut -c1-400 | head -4; done
cp afklogs/int27-*.out afklogs/b-build.log afklogs/b-a64.log afklogs/rss-build.txt int27back/ 2>/dev/null
tar czf int27back.tgz int27back
