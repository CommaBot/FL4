#!/bin/sh
# single-file check with an RSS watchdog (8 GB) and a 300 s limit: sh proofs/scratch/hpzg2_chk.sh <file rel. to proofs> <out>
export ELAN_HOME=/data/fl4/elan PATH=/data/fl4/leanq-root/bin:/data/fl4/elan/bin:$PATH
cd proofs || exit 1
export LEAN_PATH=$(lake env printenv LEAN_PATH)
LEANB=$(elan which lean)
S=$(date +%s)
"$LEANB" "$1" > "$2" 2>&1 &
P=$!
M=0
while kill -0 $P 2>/dev/null; do
  r=$(ps -o rss= -p $P 2>/dev/null); r=${r:-0}
  [ "$r" -gt "$M" ] && M=$r
  if [ "$r" -gt 8000000 ] || [ $(( $(date +%s)-S )) -gt 300 ]; then kill -9 $P; echo "KILLED rss=$r"; fi
  sleep 2
done
wait $P; rc=$?
echo "rc=$rc t=$(( $(date +%s)-S )) maxrssKB=$M"
