# usage: rootchk.sh <rev...> : compares the working root import set with the union of revs
f=proofs/Fl4Proofs.lean
T=${TMPDIR:-/private/tmp/claude-502}; mkdir -p $T
grep '^import ' $f | sort > $T/rc_w.$$
: > $T/rc_u.$$
for r in "$@"; do git show $r:$f | grep '^import ' >> $T/rc_u.$$; done
sort -u $T/rc_u.$$ -o $T/rc_u.$$
echo "work=$(wc -l < $T/rc_w.$$) uniq=$(sort -u $T/rc_w.$$|wc -l) union=$(wc -l < $T/rc_u.$$)"
diff <(sort -u $T/rc_w.$$) $T/rc_u.$$ && echo ROOT_EQ_UNION
rm -f $T/rc_w.$$ $T/rc_u.$$
