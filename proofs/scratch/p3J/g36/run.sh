#!/bin/bash
# usage (from proofs/): bash scratch/p3J/g36/run.sh F1.lean [F2.lean ...]  — lake env lean each file in parallel,
# timeout T (default 590 s), RSS watchdog RSSK KiB on the exact lean PID; outputs to scratch/p3J/g36/out/
export PATH=/data/fl4/elan/bin:$PATH
O=scratch/p3J/g36/out; mkdir -p $O
echo "OLEANS $(find .lake/build/lib/lean -name '*.olean' | wc -l)"
pids=()
for f in "$@"; do
  b=$(basename $f .lean)
  ( timeout ${T:-590} lake env lean $f > $O/$b.out 2>&1; echo "EXIT $?" >> $O/$b.out ) &
  pids+=($!)
done
while :; do
  alive=0
  for w in "${pids[@]}"; do kill -0 $w 2>/dev/null && alive=1; done
  [ $alive = 0 ] && break
  for f in "$@"; do for p in $(pgrep -f "lean $f\$"); do r=$(ps -o rss= -p $p 2>/dev/null); if [ -n "$r" ] && [ $r -gt ${RSSK:-16000000} ]; then echo "RSS KILL $f $r"; kill $p; fi; done; done
  sleep 3
done
for f in "$@"; do b=$(basename $f .lean); echo "== $f"; grep -v "^$" $O/$b.out | head -c ${C:-12000}; done
