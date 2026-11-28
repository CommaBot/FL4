#!/bin/bash
# usage (from the worktree root): bash proofs/scratch/a64/g59/chk.sh <file relative to proofs/> ...
# single-file check with `lake env lean` over the mirror's built .lake (no lake build).
D=/data/fl4; FR=$D/leanq-root
export ELAN_HOME=$D/elan PATH=$FR/bin:$D/elan/bin:$PATH; unset LEAN_NUM_THREADS
mkdir -p afklogs
cd proofs
for f in "$@"; do
  o=../afklogs/chk-$(basename $f .lean).log
  echo "== $f"
  /usr/bin/time -f "secs=%e maxRSSk=%M" timeout 2400 lake env lean "$f" > $o 2>&1
  echo "EXIT $?"
  awk '/: error/{c=40} /: warning/{c=0} c>0{print; c--}' $o | cut -c1-300 | head -400
  tail -1 $o
done
