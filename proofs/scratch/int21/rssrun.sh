# Run afk-build.sh with a per-module RSS sampler for this mirror's lean processes (reads /proc only, kills nothing).
# Usage (repo root): MODE=… [MODS=…] sh proofs/scratch/int14/rssrun.sh ; summary in afklogs/rss-$MODE.txt
here=$(pwd); mkdir -p afklogs; out=afklogs/rss-raw-$MODE.txt; : > $out
( while :; do
    for p in $(pgrep -x lean); do
      c=$(readlink /proc/$p/cwd 2>/dev/null)
      case "$c" in "$here"*)
        r=$(awk '/VmRSS/{print $2}' /proc/$p/status 2>/dev/null)
        f=$(tr '\0' '\n' < /proc/$p/cmdline 2>/dev/null | grep '\.lean$' | head -1)
        [ -n "$r" ] && echo "$r $f" >> $out;;
      esac
    done
    sleep 2
  done ) &
mon=$!
bash /data/fl4/afk-build.sh; rc=$?
kill $mon 2>/dev/null
sort -k2,2 -k1,1n $out | awk '{m[$2]=$1} END{for(k in m) printf "%d %s\n", m[k]/1024, k}' | sort -rn > afklogs/rss-$MODE.txt
echo "RSS top (MB):"; head -15 afklogs/rss-$MODE.txt
awk '$1>8192{print "RSS_OVER_8G", $0}' afklogs/rss-$MODE.txt
exit $rc
