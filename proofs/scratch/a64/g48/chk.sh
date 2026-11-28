#!/bin/bash
# usage (from repo root): bash proofs/scratch/a64/g48/chk.sh <file.lean relative to proofs> : single-file check
export ELAN_HOME=/data/fl4/elan PATH=/data/fl4/elan/bin:$PATH
cd proofs
( /usr/bin/time -f "secs=%e maxrssKB=%M" timeout ${TO:-1500} lake env lean "$1" ) > ../afklogs/chk.out 2>&1
echo "EXIT $? ERRORS $(grep -c ': error' ../afklogs/chk.out)"
grep -n ': error' ../afklogs/chk.out | cut -c1-250 | head -40
echo =====
awk '/: error/{c=30} /: warning/{c=0} c>0{print; c--}' ../afklogs/chk.out | cut -c1-300 | head -${NL:-120}
tail -2 ../afklogs/chk.out
