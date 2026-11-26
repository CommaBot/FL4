# Build scratch/int22/axint22.lean from axint21 + every AX file new in int/j22 (irqfix gen 3, p3J, p3mc gen 4-7,
# mmuAD gen 8-10, jboot gen 4-6) + scratch/int22/extra.lean (thms.py over every Fl4Proofs module new in int/j22).
# Dedup #print units; #check lines are dropped. Run in proofs/.
import glob,sys
new=['scratch/irqfix/irqfix3_ax.lean']+sorted(glob.glob('scratch/p3J/*_ax*.lean'))+\
  ['scratch/p3mc/p3mc4_ax.lean','scratch/p3mc/p3mc6_ax.lean','scratch/p3mc/p3mc7_ax.lean',
   'scratch/mmu8_ax.lean','scratch/mmu9_ax.lean','scratch/mmu10_ax.lean',
   'scratch/jboot/jboot4_ax.lean','scratch/jboot/jboot5_ax.lean','scratch/jboot/jboot6_ax.lean']
files=['scratch/int21/axint21.lean']+new+['scratch/int22/extra.lean']+sys.argv[1:]
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
open('scratch/int22/axint22.lean','w').write('\n'.join(out))
print(len(seen))
