# Run in proofs/: list Fl4Proofs/P*/*.lean modules not reachable from the root Fl4Proofs.lean.
import re,os,glob
seen=set();st=['Fl4Proofs']
while st:
  m=st.pop()
  if m in seen: continue
  seen.add(m); p=m.replace('.','/')+'.lean'
  if not os.path.exists(p): continue
  for l in open(p):
    mm=re.match(r'import (\S+)',l)
    if mm: st.append(mm.group(1))
for f in sorted(glob.glob('Fl4Proofs/P*/*.lean')):
  m=f[:-5].replace('/','.')
  if m not in seen: print('UNREACHED',m)
