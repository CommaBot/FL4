# stmts12.py over two git revisions (no worktree): kernel_entry_reach* theorem headers up to ':='.
import re,sys,subprocess
def get(rev):
  out={}
  fs=subprocess.check_output(['git','ls-tree','-r','--name-only',rev,'proofs/Fl4Proofs'],text=True).split()
  for f in fs:
    if not f.endswith('.lean'): continue
    t=subprocess.check_output(['git','show',f'{rev}:{f}'],text=True)
    for m in re.finditer(r'^theorem (kernel_entry_reach\S*)',t,re.M):
      i=t.find(':=',m.start()); out[m.group(1)]=(f,t[m.start():i])
  return out
a=get(sys.argv[1]); b=get(sys.argv[2])
print(len(a),len(b))
for k in sorted(set(a)|set(b)):
  if k not in a: print('NEW',k,b[k][0])
  elif k not in b: print('GONE',k)
  elif a[k]!=b[k]: print('DIFF',k)
