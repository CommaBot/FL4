# list decls (theorem/def/structure/abbrev/lemma) whose header text up to ':=' / 'where' differs between two trees, for files present in both
import re,sys,subprocess
A,B=sys.argv[1],sys.argv[2]
files=subprocess.check_output(['git','diff','--name-only','--diff-filter=M',A,B,'--','proofs/Fl4Proofs'],text=True).split()
pat=re.compile(r'^(?:private |protected |noncomputable )*(theorem|def|structure|abbrev|lemma|instance|class) (\S+)',re.M)
def decls(rev,f):
  t=subprocess.check_output(['git','show',f'{rev}:{f}'],text=True)
  out={}
  ms=list(pat.finditer(t))
  for i,m in enumerate(ms):
    end=ms[i+1].start() if i+1<len(ms) else len(t)
    body=t[m.start():end]
    if m.group(1)=='structure': hdr=body
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
    elif k not in a: pass
    elif a[k]!=b[k]: print('CHANGED',f,k)
