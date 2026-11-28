# tw.py BASE OURS THEIRS: compare index tree with per-path 3-way choice over BASE
import sys,subprocess
B,O,T=sys.argv[1:4]
def ls(r):
  out={}
  for l in subprocess.check_output(['git','ls-tree','-r',r],text=True).splitlines():
    m,p=l.split('\t',1); out[p]=m.split()[2]
  return out
def idx():
  out={}
  for l in subprocess.check_output(['git','ls-files','-s'],text=True).splitlines():
    m,p=l.split('\t',1); out[p]=m.split()[1]
  return out
b,o,t=ls(B),ls(O),ls(T); w=ls(sys.argv[4]) if len(sys.argv)>4 else idx()
both=[];bad=[]
for p in set(b)|set(o)|set(t)|set(w):
  if p.startswith('proofs/scratch/int27/'): continue
  bb,oo,tt,ww=b.get(p),o.get(p),t.get(p),w.get(p)
  if oo==tt: e=oo
  elif oo==bb: e=tt
  elif tt==bb: e=oo
  else: both.append(p); continue
  if e!=ww: bad.append((p,bb,oo,tt,ww))
print('both-changed:',both); print('mismatch:',len(bad))
for x in bad[:20]: print(x)
