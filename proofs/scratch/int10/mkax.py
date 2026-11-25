# Build scratch/int10/axint10.lean from the int8 axiom files and every line's *_ax*.lean (dedup #print units).
import glob,sys
files=['scratch/int8/axint8.lean','scratch/int8/axp2.lean']+sorted(glob.glob('scratch/*_ax*.lean'))+['scratch/p2lt/ax_afk.lean','P2ltAx.lean']+sys.argv[1:]
# removed by par/vmchk (moved to P1/VcpuCheckInv under other names)
DROP=('vcpu.report.xfP','vcpu.report.tw')
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
open('scratch/int10/axint10.lean','w').write('\n'.join(out))
print(len(seen))
