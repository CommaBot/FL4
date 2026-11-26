#!/bin/sh
# usage (repo root): sh proofs/scratch/hpzg3_chk.sh <file rel. to proofs> ...  — checks each in turn (watchdog of hpzg2_chk.sh)
for f in "$@"; do
  o=$(echo "$f" | tr '/' '_').out
  sh proofs/scratch/hpzg2_chk.sh "$f" "../$o"
  echo "== $f errors: $(grep -c 'error' "$o")"; grep -v "^warning" "$o" | head -${N:-120}
done
