#!/bin/sh
# usage (repo root): sh proofs/scratch/hpzg6_mod.sh <Module> ... — MODE=mod build, errors only (AX= passes through)
MODE=mod SEED=${SEED:-FL4-int16} MODS="$*" bash /data/fl4/afk-build.sh >/dev/null 2>&1
grep "^BUILD\|^ERRORS\|^SORRY\|^JOBS\|^AX" afklogs/b-mod.log | head -20
grep -o "Built Fl4Proofs.P2.\(ProgGenCd\|InvProgSrc\|InvPrune\|InvOnce\|InvLPG\)[A-Za-z0-9]* ([0-9.]*s)" afklogs/b-mod.log | head -40
grep -A${NL:-16} "^error" afklogs/b-mod.log | grep -v "^warning\|^Hint\|deprecated" | head -${N:-200}
