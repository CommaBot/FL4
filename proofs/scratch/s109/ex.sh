#!/bin/bash
# s109: extraction (x86_64 + aarch64) on tokyo; no lake. Result tarball s109/ex.tgz. Run from the repo root as `bash s109/ex.sh` (copy here to s109/).
# Copied to proofs/scratch/s109 after use; run from the repo root as `bash s109/<script>` (paths below are s109/-relative).
export PATH=$HOME/.elan/bin:$HOME/.cargo/bin:/opt/homebrew/bin:$PATH
M=/Users/admin/.stillfail/remote/sessions/de7adef11839efd864675761d4db585096cfaf4f28add8c1607f02966671d599/work; [ -x $M/fl4-deps/aeneas/aeneas ] || M=$(dirname $(ls -d /Users/admin/.stillfail/remote/sessions/*/work/fl4-deps/aeneas/aeneas 2>/dev/null | head -1) 2>/dev/null)/../..; echo M=$M; ls $M/fl4-deps/aeneas | head -3
X=$M/fl4-deps/aeneas; D=$M/fl4-deps/deps; L=$PWD/s109/exlogs; mkdir -p $L
mkdir -p $D/aeneas/bin $D/aeneas/charon/bin
ln -sfn $X/backends $D/aeneas/backends; ln -sfn $X/libs $D/aeneas/libs
ln -sf $X/aeneas $D/aeneas/bin/aeneas
for f in charon charon-driver; do ln -sf $X/$f $D/aeneas/charon/bin/$f; done
AV=$(df -k ~ | tail -1 | awk '{print $4}'); echo DISK_KB $AV; [ "$AV" -lt 15728640 ] && { echo LOWDISK; exit 9; }
ls -la $D/aeneas/charon/bin/ | head -3 || { echo NODEPS; exit 5; }
for A in x86_64 aarch64; do
  XA=; [ $A = aarch64 ] && XA="--arch aarch64"
  DYLD_LIBRARY_PATH=$D/aeneas/libs FL4_DEPS=$D nice -n 5 cargo xtask extract $XA > $L/ex-$A.log 2>&1; r=$?; echo EXTRACT $A $r
  tr "\r" "\n" < $L/ex-$A.log | grep -v '^\s*$' | tail -8; grep -n -i 'error\|FAIL' $L/ex-$A.log | head -20
done
git status --short | head -30; git diff --stat | tail -8
tar czf s109/ex.tgz proofs/Fl4Core proofs/Fl4CoreA64 s109/exlogs
shasum proofs/Fl4Core/*.lean proofs/Fl4CoreA64/*.lean
