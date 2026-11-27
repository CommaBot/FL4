# Build scratch/int21/axint21.lean from axint20, every line's *_ax*.lean (top level, pte, glue, wit, jboot, p3mc, irqfix)
# and scratch/int21/extra.lean (thms.py over every module new in int/j21 + CoreView, plus irqfix's transported
# Fl4ProofsQ / Fl4ProofsQI tops). Dedup #print units. Run in proofs/.
import glob,sys
files=['scratch/int20/axint20.lean']+sorted(glob.glob('scratch/*_ax*.lean'))+sorted(glob.glob('scratch/pte/*_ax*.lean'))+\
  sorted(glob.glob('scratch/glue/*_ax*.lean'))+sorted(glob.glob('scratch/wit/*_ax*.lean'))+\
  sorted(glob.glob('scratch/jboot/*_ax*.lean'))+sorted(glob.glob('scratch/p3mc/*_ax*.lean'))+\
  sorted(glob.glob('scratch/irqfix/*_ax*.lean'))+['scratch/p3P2_irqax.lean','scratch/int21/extra.lean']+sys.argv[1:]
DROP=('vcpu.report.xfP','vcpu.report.tw','set_timer_dec_guardU','st_rd_nouser')
seen=set();out=['import Fl4Proofs','']
for f in files:
  ls=[l.rstrip('\n') for l in open(f)]
  out.append(f'-- from {f}'); out.append('section')
  pend=''
  for l in ls:
    if l.startswith('import') or l.strip() in ('section',) or l.strip().startswith('end'): continue
    if l.startswith('open') and l.rstrip().endswith(' in'): pend+=l+'\n'; continue
    if l.startswith('#print') and l.split()[-1].endswith(DROP): pend=''; continue
    if l.startswith('#print'):
      u=pend+l; pend=''
      if u in seen: continue
      seen.add(u); out.append(u); continue
    if l.startswith('open'): out.append(l)
  out.append('end');out.append('')
open('scratch/int21/axint21.lean','w').write('\n'.join(out))
print(len(seen))
