# redline.py BASE HEAD: added/modified .lean files under proofs/ (excluding scratch/); strip comments, docstrings,
# string literals, then report sorry/admit/native_decide/bv_decide/axiom tokens. Also raw grep of added diff lines.
import re,sys,subprocess
A,B=sys.argv[1],sys.argv[2]
fs=[f for f in subprocess.check_output(['git','diff','--name-only','--diff-filter=AM',A,B,'--','proofs'],text=True).split()
    if f.endswith('.lean') and not f.startswith('proofs/scratch/')]
W=re.compile(r'\b(sorry|admit|native_decide|bv_decide|axiom)\b')
def strip(t):
  out=[];i=0;d=0;n=len(t)
  while i<n:
    if t.startswith('/-',i): d+=1;i+=2;continue
    if d and t.startswith('-/',i): d-=1;i+=2;continue
    if d: i+=1;continue
    if t.startswith('--',i):
      j=t.find('\n',i); i=n if j<0 else j; continue
    if t[i]=='"':
      j=i+1
      while j<n and t[j]!='"': j+=2 if t[j]=='\\' else 1
      i=j+1; continue
    out.append(t[i]); i+=1
  return ''.join(out)
hits=0
for f in fs:
  t=subprocess.check_output(['git','show',f'{B}:{f}'],text=True)
  for k,l in enumerate(strip(t).splitlines()):
    if W.search(l): hits+=1; print('HIT',f,l.strip()[:120])
print('files',len(fs),'hits',hits)
d=subprocess.check_output(['git','diff','-U0',A,B,'--','proofs'],text=True)
raw=[l for l in d.splitlines() if l.startswith('+') and not l.startswith('+++') and W.search(l)]
print('raw added lines mentioning a word (incl. comments/scratch):',len(raw))
for l in raw[:40]: print('  ',l[:140])
