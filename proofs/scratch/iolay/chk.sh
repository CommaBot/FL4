# single-file checks with an RSS watchdog on the exact lean PID (kill above LIM MB; no ulimit -v)
export ELAN_HOME=/data/fl4/elan PATH=/data/fl4/leanq-root/bin:/data/fl4/elan/bin:$PATH
LIM=${LIM:-16000}
cd proofs
echo "OLEANS $(find .lake/ -name '*.olean' | wc -l)"
for f in $FILES; do
  s=$(date +%s)
  out=../chk-$(basename $f).out
  setsid lake env lean $f > $out 2>&1 &
  P=$!; peak=0
  while kill -0 $P 2>/dev/null; do
    for q in $(pgrep -x lean); do
      c=$(readlink /proc/$q/cwd); [ "$c" = "$PWD" ] || continue
      r=$(awk '/VmRSS/{print int($2/1024)}' /proc/$q/status 2>/dev/null); [ -n "$r" ] || continue
      [ $r -gt $peak ] && peak=$r
      if [ $r -gt $LIM ]; then kill -KILL $q; echo "KILLED lean $q over $LIM MB"; fi
    done
    sleep 1
  done
  wait $P; r=$?
  echo "FILE $f EXIT $r secs=$(( $(date +%s)-s )) peakRssM=$peak"
  grep -E "error|sorry" $out | head -30
  grep -A12 "error" $out | head -150
  grep -A1 "depends on axioms\|does not depend" $out | head -60
done
