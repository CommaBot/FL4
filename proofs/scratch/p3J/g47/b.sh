#!/bin/bash
# usage: K=tag MODS="..." [AX=...] bash proofs/scratch/p3J/g46/b.sh   (from repo root)
if [ -n "$AX" ]; then export NAX=${NAX:-400} AX; fi
MODE=mod MODS="$MODS" SEED=/data/fl4/lake/FL4-int18 bash /data/fl4/afk-build.sh > afklogs/$K.out 2>&1
grep -E "^(BUILD|ERRORS|SORRY|JOBS|AX_EXIT)" afklogs/$K.out | head
grep -n -A30 "^error: Fl4" afklogs/b-mod.log | head -${N:-200}
if [ -n "$AX" ]; then grep -vE "depends on axioms: \[propext, Classical.choice, Quot.sound\]$" afklogs/$K.out | grep -E "axioms|MISSING|unknown" | head -40; fi
if [ -n "$AX" ]; then echo "AXPRINTED $(grep -c 'depends on axioms\|does not depend on any axioms' afklogs/$K.out) STD $(grep -c 'depends on axioms: \[propext, Classical.choice, Quot.sound\]$' afklogs/$K.out)"; grep -n "does not depend\|MISSING\|error" afklogs/$K.out | head -20; fi
