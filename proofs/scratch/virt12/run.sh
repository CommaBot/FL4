#!/bin/bash
# usage: run.sh <Module> ... : for each module, `lake env lean` its file (RSS watchdog), stop on errors, else `lake build` it.
export ELAN_HOME=/data/fl4/elan PATH=/data/fl4/leanq-root/bin:/data/fl4/elan/bin:$PATH
cd proofs
for M in "$@"; do
  f=$(echo $M | tr . /).lean
  echo "=== $M"
  start=$(date +%s)
  timeout ${TO:-1200} lake env lean "$f" > /tmp/virt12.log 2>&1 &
  P=$!; peak=0
  while kill -0 $P 2>/dev/null; do
    for q in $(pgrep -f "lean $f"); do
      r=$(awk '/VmRSS/{print $2}' /proc/$q/status 2>/dev/null); r=${r:-0}
      [ $r -gt $peak ] && peak=$r
      if [ $r -gt ${MAXKB:-16000000} ]; then echo "KILL rss $r"; kill -9 $q; fi
    done
    sleep 1
  done
  wait $P; ec=$?
  awk -v N=${N:-30} '/^[^ ]*:[0-9]+:[0-9]+: (error|warning|info)/{p=0} /^[^ ]*:[0-9]+:[0-9]+: (error|info)/{p=1;c=0} p{if(c<N)print; c++}' /tmp/virt12.log
  ne=$(grep -c ': error' /tmp/virt12.log)
  echo "=== exit $ec errors $ne in $(( $(date +%s) - start ))s peakRSS ${peak}KB"
  [ "$ec" = 0 ] && [ "$ne" = 0 ] || exit 1
  timeout 900 lake build $M 2>&1 | tail -2
done
