#!/bin/bash
# usage: run1.sh <file.lean> <tag>  : single-file lean check with RSS watchdog (16 GiB), logs afklogs/g31-<tag>.out
mkdir -p afklogs
ls -la proofs/.lake > afklogs/g31-$2.out 2>&1
cd proofs
D=/data/fl4; sed -n 1,12p $D/afk-build.sh >> ../afklogs/g31-$2.out
FR=$(grep -o "FR=[^ ;]*" $D/afk-build.sh | head -1 | cut -d= -f2); eval FR=$FR; [ -x "$FR/bin/lake" ] || FR=$D/leanq-root
export ELAN_HOME=$D/elan PATH=$FR/bin:$D/elan/bin:$PATH; unset LEAN_NUM_THREADS
echo "FR=$FR $(which lake)" >> ../afklogs/g31-$2.out
( timeout 1500 lake env lean "$1" >> ../afklogs/g31-$2.out 2>&1; echo "EXIT $?" >> ../afklogs/g31-$2.out ) &
W=$!
while kill -0 $W 2>/dev/null; do
  for p in $(pgrep -f "lean $1" ); do
    r=$(awk '/VmRSS/{print $2}' /proc/$p/status 2>/dev/null)
    if [ -n "$r" ] && [ "$r" -gt 16000000 ]; then echo "RSS KILL $p $r" >> ../afklogs/g31-$2.out; kill $p; fi
  done
  sleep 5
done
wait $W
