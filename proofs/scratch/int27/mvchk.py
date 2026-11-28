# mvchk.py A B NAMES... : repo-wide (proofs/Fl4Proofs) header of each name in A and B (first occurrence); SAME / DIFF / GONE
import re,sys,subprocess
A,B=sys.argv[1],sys.argv[2]; names=open(sys.argv[3]).read().split()
pat=re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:private |protected |noncomputable )*(theorem|def|structure|abbrev|lemma|instance|class) (\S+)',re.M)
def scan(rev):
  out={}
  fs=subprocess.check_output(['git','ls-tree','-r','--name-only',rev,'proofs/Fl4Proofs'],text=True).split()
  for f in fs:
    if not f.endswith('.lean'): continue
    t=subprocess.check_output(['git','show',f'{rev}:{f}'],text=True)
    ms=list(pat.finditer(t))
    for i,m in enumerate(ms):
      n=m.group(2); n=re.sub(r'^_root_\.Fl4Proofs\.P3\.','',n)
      if n not in want: continue
      body=t[m.start():(ms[i+1].start() if i+1<len(ms) else len(t))]
      if m.group(1)=='structure':
        ls=body.split('\n'); o=[ls[0]]
        for l in ls[1:]:
          if l and not l[0].isspace(): break
          o.append(l)
        h='\n'.join(o)
      else:
        j=min([k for k in (body.find(':='),body.find('\n  where'),body.find(' where\n')) if k>=0] or [len(body)]); h=body[:j]
      out.setdefault(n,[]).append((f,' '.join(h.replace('_root_.Fl4Proofs.P3.','').split())))
  return out
want=set(names)
a=scan(A); b=scan(B)
for n in names:
  if n not in b: print('GONE',n,[x[0] for x in a.get(n,[])]); continue
  ha=set(x[1] for x in a.get(n,[])); hb=set(x[1] for x in b[n])
  print(('SAME' if ha==hb else 'DIFF'),n,a.get(n,[('?',)])[0][0],'->',b[n][0][0])
