#!/bin/sh
# usage (repo root): sh proofs/scratch/hpzg3_mod.sh <Module> ... — MODE=mod build, errors only
MODE=mod SEED=FL4-int14 MODS="$*" bash /data/fl4/afk-build.sh >/dev/null 2>&1
grep "^BUILD\|^ERRORS\|Built Fl4Proofs.P2.\(IoOnce\|OnceWalk\|StOnce\|IrqOnce\|SlOnce\|TmOnce\|ProgGenWire\)" afklogs/b-mod.log | head -20
grep -A${NL:-16} "^error" afklogs/b-mod.log | grep -v "^warning\|^Hint\|deprecated\|^  [a-z]̵" | head -${N:-200}
