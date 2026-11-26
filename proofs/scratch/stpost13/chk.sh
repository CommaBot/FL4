# usage (from proofs/): sh scratch/stpost13/chk.sh File.lean ; RSS watchdog (8 GB, exact PID), full log to ../afklogs/c.log
export ELAN_HOME=/data/fl4/elan PATH=/data/fl4/leanq-root/bin:/data/fl4/elan/bin:$PATH
LIM=${LIM:-8000000}; mkdir -p ../afklogs; log=../afklogs/c.log; t0=$(date +%s)
lake env lean "$1" > $log 2>&1 &
P=$!; MAX=0
while kill -0 $P 2>/dev/null; do
  for c in $P $(pgrep -P $P) $(for q in $(pgrep -P $P); do pgrep -P $q; done); do
    r=$(awk '/VmRSS/{print $2}' /proc/$c/status 2>/dev/null); r=${r:-0}
    [ "$r" -gt "$MAX" ] && MAX=$r
    if [ "$r" -gt $LIM ]; then echo "KILL_RSS pid=$c rss=$r"; kill $c; fi
  done; sleep 1
done
wait $P; rc=$?
echo "== $1 rc=$rc SECS $(( $(date +%s) - t0 )) MAXRSS_KB $MAX ERRORS $(grep -c ': error' $log)"
grep ': error' $log | cut -c1-220 | head -40
grep -i 'sorry\|declaration uses' $log | head
