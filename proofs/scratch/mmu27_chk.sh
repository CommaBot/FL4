#!/bin/bash
# mmu27: build the given modules; print the summary, errors (with goals) and axioms.
MODE=mod MODS="$1" SEED=FL4-int22 AX=proofs/scratch/mmu27_ax.lean bash /data/fl4/afk-build.sh > afklogs/mmu27-run.out 2>&1
grep -E "^(BUILD|ERRORS|SORRY|JOBS|OLEANS|AX)" afklogs/mmu27-run.out
grep -E "Build completed|error: build failed" afklogs/b-mod.log | tail -2
grep -n "^error" afklogs/b-mod.log | cut -c1-300 | head -40
awk '/^error/{e=1; print "=== " substr($0,1,200); next} e && /⊢/{g=1} e && g{print substr($0,1,250); n++} n>'"${2:-12}"'{g=0;n=0;e=0}' afklogs/b-mod.log | head -${3:-200}
grep -n "axioms\|depends on" afklogs/mmu27-run.out afklogs/*ax* 2>/dev/null | head -60
