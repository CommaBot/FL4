#!/bin/bash
# slhuf gen 14 (afkprover): gen_const_specs + gen_p0 (x86_64 only), as sync19's s19/p0.sh. .lake as afk-build.sh.
D=/data/fl4; FR=$D/leanq-root
export ELAN_HOME=$D/elan PATH=$FR/bin:$D/elan/bin:$PATH; unset LEAN_NUM_THREADS
R=$PWD; L=$R/afklogs; mkdir -p $L
for p in $(pgrep -x lake); do [ "$(readlink /proc/$p/cwd)" = "$R/proofs" ] && { echo LAKE_RUNNING $p; exit 8; }; done
cd proofs
LK=$D/lake/$(basename $R); mkdir -p $LK
[ "$(readlink .lake)" = $LK ] || { rm -rf .lake; ln -s $LK .lake; }
[ "$(readlink .deps/aeneas)" = $D/aeneas/backends/lean ] || { rm -rf .deps/aeneas; mkdir -p .deps; ln -s $D/aeneas/backends/lean .deps/aeneas; }
[ "$(lake env printenv LEAN)" = "$FR/bin/lean" ] || { echo NOT_FAKE_ROOT; exit 3; }
echo OLEANS $(find .lake/build -name '*.olean' | wc -l)
cd $R
python3 xtask/scripts/gen_const_specs.py proofs > $L/gc-x86_64.log 2>&1; r=$?; echo GC $r; tail -3 $L/gc-x86_64.log; [ $r = 0 ] || { tail -60 $L/gc-x86_64.log; exit 6; }
FL4_P0_LOG=$L/p0last-x86_64.log python3 xtask/scripts/gen_p0.py proofs > $L/gp-x86_64.log 2>&1; r=$?; echo GP $r; tail -6 $L/gp-x86_64.log | cut -c1-300
python3 -c "import json;s=json.load(open('proofs/Fl4Proofs/P0/status.json'));print('STATUS',s['functions'],s['proved'],len(s['manual']));print(json.dumps(s.get('sorry'),indent=1)[:4000])"
grep -n -A30 '^error' $L/p0last-x86_64.log | head -100
mkdir -p proofs/scratch/slhuf14; tar czf proofs/scratch/slhuf14/p0.tgz proofs/Fl4Proofs/P0 proofs/Fl4Core afklogs/gp-x86_64.log afklogs/gc-x86_64.log afklogs/p0last-x86_64.log
