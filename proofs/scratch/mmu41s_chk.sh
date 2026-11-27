#!/bin/bash
# mmu41: build the given modules; print the summary, errors (with context) and axioms.
MODE=mod MODS="$1" SEED=${SEED:-FL4-int22} AX=${AXF:-proofs/scratch/mmu41_ax.lean} bash /data/fl4/afk-build.sh > afklogs/mmu41-run.out 2>&1
grep -E "^(BUILD|ERRORS|SORRY|JOBS|OLEANS|AX)" afklogs/mmu41-run.out
grep -E "Build completed|error: build failed" afklogs/b-mod.log | tail -2
grep "^error" afklogs/b-mod.log | cut -c1-160 | head -30
echo ====
grep -n "^error" -A${2:-25} afklogs/b-mod.log | cut -c1-260 | head -${3:-200}
grep -n "axioms\|depends on" afklogs/mmu41-run.out afklogs/*ax* 2>/dev/null | head -60
mkdir -p afkback; grep -n "^error" -A40 afklogs/b-mod.log | cut -c1-220 > afkback/err.txt; cp afklogs/mmu41-run.out afkback/run.txt
