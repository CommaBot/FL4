#!/bin/sh
# single-file check (repo root): sh proofs/scratch/slhuf7/chk.sh <file rel. to proofs> ... ; RSS watchdog 8 GB, 120 s each
for f in "$@"; do
  o=$(echo "$f" | tr '/' '_').out
  ( export ELAN_HOME=/data/fl4/elan PATH=/data/fl4/leanq-root/bin:/data/fl4/elan/bin:$PATH
    cd proofs || exit 1
    export LEAN_PATH=$(lake env printenv LEAN_PATH)
    LEANB=$(elan which lean); S=$(date +%s)
    "$LEANB" "$f" > "../$o" 2>&1 & P=$!; M=0
    while kill -0 $P 2>/dev/null; do
      r=$(ps -o rss= -p $P 2>/dev/null); r=${r:-0}; [ "$r" -gt "$M" ] && M=$r
      if [ "$r" -gt 8500000 ] || [ $(( $(date +%s)-S )) -gt ${TL:-120} ]; then kill -9 $P; echo "KILLED rss=$r"; fi
      sleep 1
    done
    wait $P; echo "rc=$? t=$(( $(date +%s)-S )) maxrssKB=$M" )
  echo "== $f errors: $(grep -c 'error' "$o")"; grep -v "^warning" "$o" | head -${N:-150}
done
