# Build scratch/int20/axint20.lean from axint19, every line *_ax*.lean (incl. scratch/pte/*_ax*.lean) and scratch/int20/extra.lean (dedup). Run in proofs/
# (dedup #print units). Run in proofs/.
import glob,sys
# int/j20: also the merged lines' own AX dirs (glue, wit, jboot, p3mc), p3P's irq sweep, and extra2.lean
# (every theorem of GlueCross / CoreView / JBoot* / WitPlat / WitExec / E2EPU1P and every new top, by thms.py).
files=['scratch/int19/axint19.lean']+sorted(glob.glob('scratch/*_ax*.lean'))+sorted(glob.glob('scratch/pte/*_ax*.lean'))+\
  sorted(glob.glob('scratch/glue/*_ax*.lean'))+sorted(glob.glob('scratch/wit/*_ax*.lean'))+\
  sorted(glob.glob('scratch/jboot/*_ax*.lean'))+sorted(glob.glob('scratch/p3mc/*_ax*.lean'))+['scratch/p3P2_irqax.lean']+\
  ['scratch/int20/extra.lean','scratch/int20/extra2.lean']+sys.argv[1:]
DROP=('vcpu.report.xfP','vcpu.report.tw','set_timer_dec_guardU','st_rd_nouser')  # last two: hpzg3_ax names deleted in hpzg gen 4
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
open('scratch/int20/axint20.lean','w').write('\n'.join(out))
print(len(seen))
