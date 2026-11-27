# Build scratch/int26/axint26.lean from int25's axint25 + every x86 AX file new in int/j26, stages 1 and 2 (scratch/int26/axfiles.txt:
#   mmuAD gens 23-42a, sync114, virt gens 6-28, p3mc gens 18-43, p3J gens 16-40, a64's x5_ax) + scratch/int26/extra.lean (thms.py over
# every Fl4Proofs / Fl4Spec module new in int/j26). a64/a64_ax2.lean (A64 names) is run on its own.
# Dedup #print units; #check / #eval lines are dropped. Run in proofs/.
import sys
new=open('scratch/int26/axfiles.txt').read().split()
files=['scratch/int25/axint25.lean']+new+['scratch/int26/extra.lean']
seen=set();out=['import Fl4Proofs','']
for f in files:
  ls=[l.rstrip('\n') for l in open(f)]
  out.append(f'-- from {f}'); out.append('section')
  pend=''
  for l in ls:
    if l.startswith('import') or l.strip() in ('section',) or l.strip().startswith('end'): continue
    if l.startswith('open') and l.rstrip().endswith(' in'): pend+=l+'\n'; continue
    if l.startswith('#print'):
      u=pend+l; pend=''
      if u in seen: continue
      seen.add(u); out.append(u); continue
    pend=''
    if l.startswith('open'): out.append(l)
  out.append('end');out.append('')
open('scratch/int26/axint26.lean','w').write('\n'.join(out))
print(len(seen))
