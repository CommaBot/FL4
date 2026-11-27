import re,sys
out=[]
for f in sys.argv[1:]:
    ns=[]
    for line in open(f):
        m=re.match(r'^namespace (\S+)',line)
        if m: ns.append(m.group(1)); continue
        m=re.match(r'^end (\S+)\s*$',line)
        if m and ns and ns[-1]==m.group(1): ns.pop(); continue
        m=re.match(r'^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*(theorem|lemma|def|abbrev|structure)\s+(\S+)',line)
        if m:
            n=m.group(2)
            if n.startswith('_root_.'): full=n[7:]
            else: full='.'.join(ns+[n])
            out.append(full)
print('\n'.join(out))
