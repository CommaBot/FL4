# axcount.py LOG: count `#print axioms` outputs in a job log (joins wrapped lines).
import re,sys,collections
t=open(sys.argv[1],errors='replace').read()
t=t[t.rfind('\nAX '):] if '\nAX ' in t else t
t=re.sub(r'\n(?=\s)',' ',t)
dep=re.findall(r"(?m)^'(.+?)' depends on axioms: \[([^\]]*)\]",t)
nod=re.findall(r"(?m)^'(.+?)' does not depend on any axioms",t)
c=collections.Counter(', '.join(sorted(x.strip() for x in a.split(','))) for _,a in dep)
print('depends',len(dep),'none',len(nod))
for k,v in c.most_common(): print(v,k)
ok={'propext','Classical.choice','Quot.sound'}
bad=[(n,a) for n,a in dep if not set(x.strip() for x in a.split(','))<=ok]
print('BAD',len(bad),bad[:5])
r=[n for n,a in dep if n.split('.')[-1].startswith('kernel_entry_reach')]
print('reach',len(r),len(set(r)),'all3',sum(1 for n,a in dep if n.split('.')[-1].startswith('kernel_entry_reach') and set(x.strip() for x in a.split(','))==ok))
err=re.findall(r'^.*error.*$',t,re.M); print('errlines',len(err),err[:3])
