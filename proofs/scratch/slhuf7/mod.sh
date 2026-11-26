#!/bin/sh
# usage (repo root): [AX=…] sh proofs/scratch/slhuf7/mod.sh <Module(full name)> ... — MODE=mod build (SEED=FL4-int14)
# with an RSS watchdog: any lean process of this mirror above 12 GB is killed by pid; summary per module.
here=$(pwd); mkdir -p afklogs; out=afklogs/rss-raw.txt; : > $out
( while :; do
    for p in $(pgrep -x lean); do
      c=$(readlink /proc/$p/cwd 2>/dev/null)
      case "$c" in "$here"*)
        r=$(awk '/VmRSS/{print $2}' /proc/$p/status 2>/dev/null)
        f=$(tr '\0' '\n' < /proc/$p/cmdline 2>/dev/null | grep '\.lean$' | head -1)
        [ -n "$r" ] && echo "$r $f" >> $out
        [ -n "$r" ] && [ "$r" -gt 12000000 ] && { kill -9 $p; echo "WATCHDOG_KILLED $r $f" >> $out; };;
      esac
    done
    sleep 2
  done ) &
mon=$!
MODE=mod SEED=${SEED:-FL4-int14} MODS="$*" bash /data/fl4/afk-build.sh > afklogs/out.txt 2>&1; rc=$?
kill $mon 2>/dev/null
grep WATCHDOG $out
sort -k2,2 -k1,1n $out | awk '{m[$2]=$1} END{for(k in m) printf "%d %s\n", m[k]/1024, k}' | sort -rn | head -8
grep "^BUILD\|^ERRORS\|^SORRY\|^JOBS\|^AX\|OLEANS\|Build completed" afklogs/out.txt afklogs/b-mod.log | head -20
grep -A${NL:-20} "^error" afklogs/b-mod.log | grep -v "^warning\|deprecated" | head -${N:-250}
[ -n "$AX" ] && { echo "AXLINES $(grep -c "axioms" afklogs/out.txt)"; tr "\n" " " < afklogs/out.txt | grep -o "depends on axioms: \[[^]]*\]" | sort | uniq -c; grep -o "does not depend on any axioms" afklogs/out.txt | uniq -c; }
exit $rc
