# hdr.py A B FILE NAME: print the declaration's header (structure: up to first non-indented line) in A and B, and a word diff
import re,sys,subprocess,difflib
A,B,f,n=sys.argv[1:5]
pat=re.compile(r'^(?:private |protected |noncomputable )*(theorem|def|structure|abbrev|lemma|instance|class) (\S+)',re.M)
def get(rev):
  t=subprocess.check_output(['git','show',f'{rev}:{f}'],text=True)
  for m in pat.finditer(t):
    if m.group(2)!=n: continue
    body=t[m.start():]
    if m.group(1)=='structure':
      ls=body.split('\n'); out=[ls[0]]
      for l in ls[1:]:
        if l and not l[0].isspace(): break
        out.append(l)
      return '\n'.join(out).rstrip()
    j=min([k for k in (body.find(':='),body.find('\n  where'),body.find(' where\n')) if k>=0] or [len(body)])
    return body[:j]
a=get(A); b=get(B)
if ' '.join(a.split())==' '.join(b.split()): print('SAME-STRUCT-BODY',f,n); sys.exit()
print('DIFF',f,n)
for l in difflib.unified_diff(a.split('\n'),b.split('\n'),lineterm='',n=0):
  if l.startswith(('+++','---','@@')): continue
  print('   ',l[:200])
