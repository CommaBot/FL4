#!/bin/bash
# usage: run1.sh <file relative to proofs> ...   (prints error blocks, first N lines each)
export ELAN_HOME=/data/fl4/elan PATH=/data/fl4/leanq-root/bin:/data/fl4/elan/bin:$PATH
cd proofs
N=${N:-40}
for f in "$@"; do
  echo "=== $f"
  start=$(date +%s)
  timeout 1500 lake env lean "$f" > /tmp/virt3.log 2>&1
  ec=$?
  awk -v N=$N '/^[^ ]*:[0-9]+:[0-9]+: (error|warning)/{p=0} /^[^ ]*:[0-9]+:[0-9]+: error/{p=1;c=0} p{if(c<N)print; c++}' /tmp/virt3.log
  grep -c ": error" /tmp/virt3.log
  echo "=== exit $ec in $(( $(date +%s) - start ))s"
done
