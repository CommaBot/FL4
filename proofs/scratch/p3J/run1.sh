#!/bin/bash
# usage: bash scratch/p3J/run1.sh file.lean [secs]  (from proofs/); RSS watchdog 14 GB on the lean PID
f=$1; T=${2:-400}
( timeout $T lake env lean $f > /tmp/p3J_$(basename $f).out 2>&1; echo "EXIT $?" >> /tmp/p3J_$(basename $f).out ) &
W=$!
while kill -0 $W 2>/dev/null; do
  for p in $(pgrep -f "bin/lean $f"); do r=$(ps -o rss= -p $p 2>/dev/null); if [ -n "$r" ] && [ $r -gt 14000000 ]; then echo "RSS KILL $r"; kill $p; fi; done
  sleep 3
done
echo "== $f"; grep -v "^$" /tmp/p3J_$(basename $f).out | head -150
