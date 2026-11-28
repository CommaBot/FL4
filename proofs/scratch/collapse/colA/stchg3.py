# stchg.py with structures/defs cut at their own block (next column-0 line), so trailing deleted
# declarations, docstrings or sections after a structure do not show as a change of it.
import re,sys,subprocess
A,B=sys.argv[1],sys.argv[2]
paths=sys.argv[3:] or ['proofs/Fl4Proofs']
files=subprocess.check_output(['git','diff','--name-only','--diff-filter=M',A,B,'--']+paths,text=True).split()
pat=re.compile(r'^(?:private |protected |noncomputable )*(theorem|def|structure|abbrev|lemma|instance|class) (\S+)',re.M)
def decls(rev,f):
  t=subprocess.check_output(['git','show',f'{rev}:{f}'],text=True)
  out={}
  ms=list(pat.finditer(t))
  for i,m in enumerate(ms):
    end=ms[i+1].start() if i+1<len(ms) else len(t)
    body=t[m.start():end]
    if m.group(1)=='structure':
      ls=body.split('\n'); k=1
      while k<len(ls) and (ls[k].startswith(' ') or ls[k]==''): k+=1
      hdr='\n'.join(ls[:k])
    else:
      j=min([k for k in (body.find(':='),body.find('\n  where'),body.find(' where\n')) if k>=0] or [len(body)])
      hdr=body[:j]
    out[m.group(2)]=' '.join(hdr.split())
  return out
for f in files:
  if f.endswith('Fl4Proofs.lean'): continue
  a=decls(A,f); b=decls(B,f)
  for k in sorted(set(a)|set(b)):
    if k not in b: print('REMOVED',f,k)
    elif k not in a: print('ADDED',f,k)
    elif a[k]!=b[k]: print('CHANGED',f,k)
