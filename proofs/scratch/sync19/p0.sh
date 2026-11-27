#!/bin/bash
# sync19 (afkprover): gen_const_specs + gen_p0 for ARCHS in this mirror. .lake as afk-build.sh (symlink to /data/fl4/lake/<mirror>).
# Copied to proofs/scratch/sync19 after use; run from the repo root as `bash s19/<script>` (paths below are s19/-relative).
M=/root/.monoid/remote/sessions/de7adef11839efd864675761d4db585096cfaf4f28add8c1607f02966671d599/work
D=/data/fl4; FR=$D/leanq-root
export ELAN_HOME=$D/elan PATH=$FR/bin:$D/elan/bin:$PATH; unset LEAN_NUM_THREADS
R=$PWD; L=$R/afklogs; mkdir -p $L s19/p0back
for p in $(pgrep -x lake); do [ "$(readlink /proc/$p/cwd)" = "$R/proofs" ] && { echo LAKE_RUNNING $p; exit 8; }; done
cd proofs
LK=$D/lake/$(basename $R); mkdir -p $LK
[ "$(readlink .lake)" = $LK ] || { rm -rf .lake; ln -s $LK .lake; }
[ "$(readlink .deps/aeneas)" = $D/aeneas/backends/lean ] || { rm -rf .deps/aeneas; mkdir -p .deps; ln -s $D/aeneas/backends/lean .deps/aeneas; }
if [ ! -d .lake/build ] && [ ! -d .lake/packages ]; then cp -a --reflink=auto $D/lake/${SEED:-FL4-int18}/. $LK/ && echo SEEDED || { echo SEEDFAIL; exit 4; }; fi
[ "$(lake env printenv LEAN)" = "$FR/bin/lean" ] || { echo NOT_FAKE_ROOT; exit 3; }
echo OLEANS $(find .lake/build -name '*.olean' | wc -l)
cd $R
for A in ${ARCHS:-x86_64 aarch64}; do
  if [ $A = aarch64 ]; then XA="--arch aarch64"; PL=Fl4ProofsA64; else XA=""; PL=Fl4Proofs; fi
  if [ -z "$NOGC" ]; then python3 xtask/scripts/gen_const_specs.py proofs $XA > $L/gc-$A.log 2>&1; r=$?; echo GC $A $r; tail -3 $L/gc-$A.log; [ $r = 0 ] || { tail -60 $L/gc-$A.log; exit 6; }; fi
  FL4_P0_LOG=$L/p0last-$A.log python3 xtask/scripts/gen_p0.py proofs $XA $GPX > $L/gp-$A.log 2>&1; r=$?; echo GP $A $r; tail -6 $L/gp-$A.log | cut -c1-300
  python3 -c "import json;s=json.load(open('proofs/$PL/P0/status.json'));print('STATUS',s['functions'],s['proved'],len(s['manual']));print(json.dumps(s.get('sorry'),indent=1)[:4000])"
  grep -n -A30 '^error' $L/p0last-$A.log | grep -v ': U64$\|: Bool$\|: Type\|: S$\|: A$' | head -${NL:-150}
done
git status --short | head -40
tar czf s19/p0.tgz proofs/Fl4Proofs/P0 proofs/Fl4ProofsA64/P0 afklogs/gp-*.log afklogs/gc-*.log afklogs/p0last-*.log
