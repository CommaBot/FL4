#!/bin/bash
# single-file check with an RSS watchdog on the exact lean PID (kill above 12 GB)
eval "$(sed -n '1,12p' /data/fl4/afk-build.sh | grep -E '^(D|FR|export ELAN)')"
echo LAKE $(which lake)
cd proofs
f=$1
( lake env lean $f > ../afklogs/t1.out 2>&1; echo "EXIT $?" >> ../afklogs/t1.out ) &
sleep 3
for i in $(seq 1 200); do
  P=$(pgrep -f "lean $f" | head -1)
  [ -z "$P" ] && break
  R=$(ps -o rss= -p $P 2>/dev/null | tr -d ' ')
  if [ -n "$R" ] && [ "$R" -gt 12000000 ]; then kill $P; echo "KILLED RSS $R" >> ../afklogs/t1.out; fi
  sleep 1
done
wait
head -c 20000 ../afklogs/t1.out
