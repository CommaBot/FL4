#!/bin/bash
# mmu11: build the given modules and print only the summary, errors and axioms.
MODE=mod MODS="$1" SEED=FL4-int21 AX=proofs/scratch/mmu11_ax.lean bash /data/fl4/afk-build.sh > afklogs/mmu11-run.out 2>&1
grep -E "^(BUILD|ERRORS|SORRY|JOBS|OLEANS|AX)" afklogs/mmu11-run.out
grep -E "Build completed|error: build failed" afklogs/b-mod.log | tail -2
grep -n "^error" afklogs/b-mod.log | head -30
grep -n "^error" -A25 afklogs/b-mod.log | grep -v "^.*warning" | head -${2:-200}
grep -n "axioms\|depends on" afklogs/mmu11-run.out afklogs/*ax* 2>/dev/null | head -60
