#!/bin/bash
# p3P gen 2: run afk-build.sh with an RSS watchdog on this mirror's lean processes (limit $LIM_MB).
LIM_MB=${LIM_MB:-24000}; R=$PWD
( while sleep 15; do for p in $(pgrep -x lean); do c=$(readlink /proc/$p/cwd); case "$c" in $R/*|$R) r=$(awk '/VmRSS/{print int($2/1024)}' /proc/$p/status 2>/dev/null); [ -n "$r" ] && [ "$r" -gt $LIM_MB ] && { echo "WATCHDOG kill $p rss=${r}M" >> $R/guard.txt; kill $p; };; esac; done; done ) &
W=$!
bash /data/fl4/afk-build.sh
kill $W 2>/dev/null
cat $R/guard.txt 2>/dev/null
