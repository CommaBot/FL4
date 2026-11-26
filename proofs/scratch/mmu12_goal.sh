#!/bin/bash
# mmu12: build, print the summary, each error's first line and the goal (after the turnstile).
MODE=mod MODS="$1" SEED=FL4-int21 AX=proofs/scratch/mmu12_ax.lean bash /data/fl4/afk-build.sh > afklogs/mmu12-run.out 2>&1
grep -E "^(BUILD|ERRORS|SORRY|JOBS|OLEANS|AX)" afklogs/mmu12-run.out
grep -E "Build completed|error: build failed" afklogs/b-mod.log | tail -2
grep -n "^error" -A3 afklogs/b-mod.log | head -60
awk '/^error/{e=1; print "=== " $0; next} e && /⊢/{g=1} e && g{print; n++} n>'"${2:-40}"'{g=0;n=0;e=0}' afklogs/b-mod.log | head -${3:-400}
grep -n "axioms\|depends on" afklogs/mmu12-run.out afklogs/*ax* 2>/dev/null | head -60
