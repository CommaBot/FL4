#!/bin/bash
# slhuf gen 14: x86_64 extraction on tokyo (as sync19's s19/ex.sh); no lake. Result tarball proofs/scratch/slhuf14/ex.tgz.
export PATH=$HOME/.elan/bin:$HOME/.cargo/bin:/opt/homebrew/bin:$PATH
M=/Users/admin/.stillfail/remote/sessions/de7adef11839efd864675761d4db585096cfaf4f28add8c1607f02966671d599/work
X=$M/fl4-deps/aeneas; D=$M/fl4-deps/deps; L=$PWD/proofs/scratch/slhuf14/exlogs; mkdir -p $L
mkdir -p $D/aeneas/bin $D/aeneas/charon/bin
ln -sfn $X/backends $D/aeneas/backends; ln -sfn $X/libs $D/aeneas/libs
ln -sf $X/aeneas $D/aeneas/bin/aeneas
for f in charon charon-driver; do ln -sf $X/$f $D/aeneas/charon/bin/$f; done
AV=$(df -k ~ | tail -1 | awk '{print $4}'); echo DISK_KB $AV; [ "$AV" -lt 15728640 ] && { echo LOWDISK; exit 9; }
DYLD_LIBRARY_PATH=$D/aeneas/libs FL4_DEPS=$D nice -n 5 cargo xtask extract > $L/ex-x86_64.log 2>&1; r=$?; echo EXTRACT x86_64 $r
tr "\r" "\n" < $L/ex-x86_64.log | grep -v '^\s*$' | tail -8; grep -n -i 'error\|FAIL' $L/ex-x86_64.log | head -20
git status --short | head -30; git diff --stat | tail -8
tar czf proofs/scratch/slhuf14/ex.tgz proofs/Fl4Core proofs/scratch/slhuf14/exlogs
shasum proofs/Fl4Core/*.lean
