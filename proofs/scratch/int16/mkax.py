# Build scratch/int16/axint16.lean from int15's axint15.lean, every line's *_ax*.lean and scratch/int16/extra.lean
# (dedup #print units). Run in proofs/.
import glob,sys
files=['scratch/int15/axint15.lean']+sorted(glob.glob('scratch/*_ax*.lean'))+['scratch/int16/extra.lean']+sys.argv[1:]
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
open('scratch/int16/axint16.lean','w').write('\n'.join(out))
print(len(seen))
