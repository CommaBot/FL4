# defdiff.py OLD NEW: list added/removed/changed top-level declarations of an Aeneas Lean file (Source comments ignored).
import re,sys
def parse(p):
  d={};cur=None;buf=[]
  txt=re.sub(r'/-.*?-/','',open(p).read(),flags=re.S)
  for l in txt.splitlines(True):
    if re.match(r'\s*/-\s*\[.*\]:\s*$',l) or l.strip().startswith('Source:') or re.match(r'^\s*(Source|Name pattern|Visibility):',l): continue
    m=re.match(r'^(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+)?(?:partial\s+)?(def|structure|inductive|abbrev|axiom|opaque|theorem|instance)\s+(\S+)',l)
    if m:
      if cur: d[cur]=''.join(buf)
      cur=m.group(2); buf=[l]; continue
    if cur: buf.append(l)
  if cur: d[cur]=''.join(buf)
  return d
a,b=parse(sys.argv[1]),parse(sys.argv[2])
for k in sorted(set(a)|set(b)):
  if k not in a: print('ADDED',k)
  elif k not in b: print('REMOVED',k)
  elif re.sub(r'\s+',' ',a[k])!=re.sub(r'\s+',' ',b[k]): print('CHANGED',k)
