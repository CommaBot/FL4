#!/bin/bash
# int27-f2 (afkprover): stage 2 (+ a64 5f6ad4a42). x86 root build + axint27 (4217 #print), MODE=a64, then the
# whole-environment sweeps collapse/axall.lean / axallA64.lean and a64's own scratch/a64/a64_ax2.lean.
# Run from the repo root of the mirror. SEED: absolute path of a built .lake (stage 1's mirror).
mkdir -p afklogs int27back2; S=${SEED:-/data/fl4/lake/FL4-int27}
MODE=build NAX=100000 AX=proofs/scratch/int27/axint27.lean SEED=$S bash proofs/scratch/int27/rssrun.sh > afklogs/int27-build.out 2>&1; echo BUILD_EXIT $?
grep -E '^(SEEDED|SEEDFAIL|BUILD|ERRORS|SORRY|JOBS|OLEANS|AX)' afklogs/int27-build.out
grep -E 'Build completed|error: build failed' afklogs/b-build.log | tail -2
MODE=a64 SEED=$S bash /data/fl4/afk-build.sh > afklogs/int27-a64.out 2>&1; echo A64_EXIT $?
grep -E '^(BUILD|ERRORS|SORRY|JOBS)' afklogs/int27-a64.out
grep -E 'Build completed|error: build failed' afklogs/b-a64.log | tail -2
for f in collapse/axall collapse/axallA64 a64/a64_ax2; do b=$(basename $f); bash proofs/scratch/int27/axrun.sh scratch/$f.lean afklogs/int27-$b.out; grep -E 'AXALL|error' afklogs/int27-$b.out | cut -c1-400 | head -4; done
cp afklogs/int27-*.out afklogs/b-build.log afklogs/b-a64.log afklogs/rss-build.txt int27back2/ 2>/dev/null
tar czf int27back2.tgz int27back2
