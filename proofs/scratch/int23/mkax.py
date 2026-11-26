# Build scratch/int23/axint23.lean from int22's axint22 + every AX file new in int/j23 (p3J gen 3-7, mmuAD gen 11-13,
# p3mc gen 8-10, virt gen 1) + scratch/int23/extra.lean (thms.py over every Fl4Proofs module new in int/j23).
# Dedup #print units; #check lines are dropped. Run in proofs/.
import glob,sys
new=['scratch/p3J/p3J%d_ax.lean'%i for i in (3,4,5,6,7)]+\
  ['scratch/mmu11_ax.lean','scratch/mmu12_ax.lean','scratch/mmu13_ax.lean',
   'scratch/p3mc/p3mc8_ax.lean','scratch/p3mc/p3mc9_ax.lean','scratch/p3mc/p3mc10_ax.lean',
   'scratch/virt/virt1_ax.lean']
files=['scratch/int22/axint22.lean']+new+['scratch/int23/extra.lean']+sys.argv[1:]
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
    if l.startswith('open'): out.append(l)
  out.append('end');out.append('')
open('scratch/int23/axint23.lean','w').write('\n'.join(out))
print(len(seen))
