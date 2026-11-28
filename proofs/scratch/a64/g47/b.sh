#!/bin/bash
# usage: b.sh "<MODS>" tag : module build, then error lines with context
SEED=/data/fl4/lake/FL4-int18 bash proofs/scratch/a64/g33b.sh "$1" "$2"
grep -n '^error' afklogs/b-mod.log | cut -c1-300 | head -30
awk '/^error: Fl4/{c=45} /^warning: /{c=0} c>0{print; c--}' afklogs/b-mod.log | cut -c1-300 | head -400
