# usage: rootchk.sh <rev...> : compares the working root import set with the union of revs
f=proofs/Fl4Proofs.lean
grep '^import ' $f | sort > /tmp/rc_w.$$
: > /tmp/rc_u.$$
for r in "$@"; do git show $r:$f | grep '^import ' >> /tmp/rc_u.$$; done
sort -u /tmp/rc_u.$$ -o /tmp/rc_u.$$
echo "work=$(wc -l < /tmp/rc_w.$$) uniq=$(sort -u /tmp/rc_w.$$|wc -l) union=$(wc -l < /tmp/rc_u.$$)"
diff <(sort -u /tmp/rc_w.$$) /tmp/rc_u.$$ && echo ROOT_EQ_UNION
rm -f /tmp/rc_w.$$ /tmp/rc_u.$$
