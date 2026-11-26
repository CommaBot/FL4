#!/bin/bash
# usage (from proofs/): bash scratch/p3J/chain.sh Mod1 Mod2 ...  — compile each P3 module in order with lake env lean -o,
# copy its olean into the build dir, stop at the first failure; RSS watchdog on the lean PID (RSSK KiB).
export PATH=/data/fl4/elan/bin:$PATH
D=.lake/build/lib/lean/Fl4Proofs/P3
for m in "$@"; do
  f=Fl4Proofs/P3/$m.lean
  ( timeout ${T:-1500} lake env lean -o /tmp/p3J_$m.olean -i /tmp/p3J_$m.ilean $f > /tmp/p3J_$m.out 2>&1; echo "EXIT $?" >> /tmp/p3J_$m.out ) &
  W=$!
  while kill -0 $W 2>/dev/null; do
    for p in $(pgrep -f "lean -o /tmp/p3J_$m.olean"); do r=$(ps -o rss= -p $p 2>/dev/null); if [ -n "$r" ] && [ $r -gt ${RSSK:-14000000} ]; then echo "RSS KILL $m $r"; kill $p; fi; done
    sleep 3
  done
  echo "== $m"; grep -v "^$" /tmp/p3J_$m.out | grep -A12 ": error" | head -c ${C:-9000}
  if ! grep -q "EXIT 0" /tmp/p3J_$m.out || grep -q "error" /tmp/p3J_$m.out; then echo "STOP at $m"; exit 1; fi
  cp /tmp/p3J_$m.olean $D/$m.olean; cp /tmp/p3J_$m.ilean $D/$m.ilean
done
echo CHAIN OK
