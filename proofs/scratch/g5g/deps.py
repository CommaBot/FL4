import re,glob,sys
D='../../Fl4Spec/'
defs={}
for f in sorted(glob.glob(D+'**/*.lean',recursive=True)):
    ss=open(f).read()
    for p in re.split(r'\n(?=(?:private |noncomputable |partial |@\[[^\]]*\] )*(?:def|abbrev|theorem|structure|inductive|instance|class|mutual|end|section|namespace|variable|open|/-|--) )|\n(?=/-)',ss):
        m=re.match(r'(?:private |noncomputable |partial |@\[[^\]]*\] )*(def|abbrev) (\S+)',p)
        if m and m.group(2) not in defs: defs[m.group(2)]=p
callee={k:set(w for w in re.findall(r"(?<![\w.])([a-z][A-Za-z0-9_']*)",v) if w in defs and w!=k) for k,v in defs.items()}
rev={}
for k,v in callee.items():
    for c in v: rev.setdefault(c,set()).add(k)
bad=set(sys.argv[1].split(','))
seen=set(bad);todo=list(bad)
while todo:
    n=todo.pop()
    for c in rev.get(n,()):
        if c not in seen: seen.add(c);todo.append(c)
names=set()
for i in range(1,7):
    names|=set(re.findall(r'theorem idk_(\w+)',open('../../Fl4Proofs/P3/SpecInvSgI%d.lean'%i).read()))
print(' '.join(sorted(seen&names)))
print('not in family:',' '.join(sorted(seen-names))[:3000],file=sys.stderr)
