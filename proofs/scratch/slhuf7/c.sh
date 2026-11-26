#!/bin/sh
# sh proofs/scratch/slhuf7/c.sh <file rel. to proofs>...: single-file checks, errors only
sh proofs/scratch/slhuf7/chk.sh "$@" > afklogs/chk.txt 2>&1
grep "^rc=\|^== \|KILLED" afklogs/chk.txt
grep -A${NL:-14} "error" afklogs/chk.txt | grep -v "warning\|deprecated\|Hint\|^  \[apply\]\|linter\|̵" | head -${N:-150}
