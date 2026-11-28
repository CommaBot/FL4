# res3.py BASE: during a `git merge --no-commit` (HEAD = ours, MERGE_HEAD = theirs), set every path to its per-path
# 3-way choice over BASE (the line's previous integrated commit, here a64 5099c9e13, squashed into main by #66):
# unchanged on one side -> the other side's blob (incl. deletion). Paths changed on both sides are listed, untouched.
import sys,subprocess
B=sys.argv[1]
def ls(r):
  out={}
  for l in subprocess.check_output(['git','ls-tree','-r',r],text=True).splitlines():
    m,p=l.split('\t',1); mm=m.split(); out[p]=(mm[0],mm[2])
  return out
b,o,t=ls(B),ls('HEAD'),ls('MERGE_HEAD')
idx={}
for l in subprocess.check_output(['git','ls-files','-s'],text=True).splitlines():
  m,p=l.split('\t',1); mm=m.split()
  if mm[2]=='0': idx[p]=(mm[0],mm[1])
  else: idx[p]='CONFLICT'
both=[];n=0
for p in sorted(set(b)|set(o)|set(t)):
  bb,oo,tt=b.get(p),o.get(p),t.get(p)
  if oo==tt: e=oo
  elif oo==bb: e=tt
  elif tt==bb: e=oo
  else: both.append(p); continue
  if idx.get(p)==e: continue
  if e is None:
    subprocess.run(['git','rm','-q','--cached','--ignore-unmatch','--',p],check=True)
    subprocess.run(['rm','-f','--',p])
  else:
    subprocess.run(['git','update-index','--add','--cacheinfo',f'{e[0]},{e[1]},{p}'],check=True)
    subprocess.run(['git','checkout','--',p],check=True)
  n+=1
print('set',n,'both-changed',both)
