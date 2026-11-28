#!/bin/bash
# single-file check(s) with an RSS watchdog on the exact lean PID (kill above 12 GB); args: files relative to proofs/
eval "$(sed -n '1,12p' /data/fl4/afk-build.sh | grep -E '^(D|FR|export ELAN)')"
cd proofs
for f in "$@"; do
o=../afklogs/t-$(basename $f .lean).out
( lake env lean $f > $o 2>&1; echo "EXIT $?" >> $o ) &
BG=$!
sleep 3
while kill -0 $BG 2>/dev/null; do
  for P in $(pgrep -x lean); do
    [ "$(tr '\0' ' ' < /proc/$P/cmdline 2>/dev/null | grep -c -- "$f")" = 1 ] || continue
    R=$(awk '/VmRSS/{print $2}' /proc/$P/status 2>/dev/null)
    if [ -n "$R" ] && [ "$R" -gt 12000000 ]; then kill $P; echo "KILLED RSS $R" >> $o; fi
  done
  sleep 1
done
wait $BG
echo "=== $f"; head -c 15000 $o
done
