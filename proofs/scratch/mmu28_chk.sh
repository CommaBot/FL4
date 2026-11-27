#!/bin/bash
# mmu28: build the given modules; print the summary, errors (with context) and axioms.
MODE=mod MODS="$1" SEED=FL4-int22 AX=proofs/scratch/mmu28_ax.lean bash /data/fl4/afk-build.sh > afklogs/mmu28-run.out 2>&1
grep -E "^(BUILD|ERRORS|SORRY|JOBS|OLEANS|AX)" afklogs/mmu28-run.out
grep -E "Build completed|error: build failed" afklogs/b-mod.log | tail -2
grep -n "^error" -A${2:-25} afklogs/b-mod.log | cut -c1-260 | head -${3:-200}
grep -n "axioms\|depends on" afklogs/mmu28-run.out afklogs/*ax* 2>/dev/null | head -60
