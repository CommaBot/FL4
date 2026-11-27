# axrun.sh FILE OUT: run one axiom-check file (path relative to proofs/) with the mirror's built .lake,
# full output to OUT (relative to the repo root). Run in the repo root.
export ELAN_HOME=/data/fl4/elan PATH=/data/fl4/leanq-root/bin:/data/fl4/elan/bin:$PATH
mkdir -p "$(dirname "$2")"
( cd proofs && lake env lean "$1" ) > "$2" 2>&1; rc=$?
echo "AXRUN $1 rc=$rc lines=$(wc -l < "$2")"
exit $rc
