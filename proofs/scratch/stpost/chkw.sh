# usage: sh scratch/stpost/chkw.sh File1.lean [...]  (from proofs/); single-file check with an RSS watchdog
# (kills the exact lean PID if its RSS exceeds 16 GB; never by name).
export ELAN_HOME=/data/fl4/elan PATH=/data/fl4/leanq-root/bin:/data/fl4/elan/bin:$PATH
echo OLEANS $(find -L .lake/build/lib -name '*.olean' 2>/dev/null | wc -l)
LIM=16000000
for f in "$@"; do
  t0=$(date +%s)
  log=/tmp/stpost9-chk-$$.log
  lake env lean "$f" > $log 2>&1 &
  P=$!
  MAX=0
  while kill -0 $P 2>/dev/null; do
    for c in $P $(pgrep -P $P) $(for q in $(pgrep -P $P); do pgrep -P $q; done); do
      r=$(awk '/VmRSS/{print $2}' /proc/$c/status 2>/dev/null)
      r=${r:-0}
      [ "$r" -gt "$MAX" ] && MAX=$r
      if [ "$r" -gt $LIM ]; then echo "KILL_RSS pid=$c rss=$r"; kill $c; fi
    done
    sleep 1
  done
  wait $P; rc=$?
  echo "== $f rc=$rc SECS $(( $(date +%s) - t0 )) MAXRSS_KB $MAX ERRORS $(grep -c ': error' $log)"
  grep -A${CTX:-30} ': error' $log | cut -c1-300 | head -${MAXL:-200}
  grep -i 'sorry\|axiom' $log | head -20
  rm -f $log
done
