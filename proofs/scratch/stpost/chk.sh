# usage: sh scratch/stpost/chk.sh File1.lean [File2.lean ...]  (from proofs/)
export ELAN_HOME=/data/fl4/elan PATH=/data/fl4/leanq-root/bin:/data/fl4/elan/bin:$PATH
echo OLEANS $(find .lake/build/lib -name '*.olean' 2>/dev/null | wc -l)
for f in "$@"; do
  t0=$(date +%s)
  timeout 900 lake env lean "$f" > /tmp/stpost-chk.log 2>&1
  echo "== $f rc=$? SECS $(( $(date +%s) - t0 )) ERRORS $(grep -c ': error' /tmp/stpost-chk.log)"
  grep -A${CTX:-30} ': error' /tmp/stpost-chk.log | cut -c1-300 | head -${MAXL:-200}
done
