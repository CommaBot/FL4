# gen 8: XTopJointKEntryU41 = U40 with KFinAtR13 -> KFinAtR41, KFinEv13 -> KFinEv41 and hFpu : FpuImplDet;
# kernel_entry_reachU40_of41 (U40's statement + hFpu).
import pathlib
P = pathlib.Path
src = P('Fl4Proofs/P3/XTopJointKEntryU40.lean').read_text().splitlines()
st = next(i for i, l in enumerate(src) if l.startswith('theorem kernel_entry_reachU40 '))
en = next(i for i in range(st, len(src)) if src[i].rstrip().endswith(':= by'))
u40 = '\n'.join(src[st:en + 1])
assert u40.count('KFinAtR13') == 1 and u40.count('KFinEv13') == 5, (u40.count('KFinAtR13'), u40.count('KFinEv13'))
old = '    (hMap : IoaMap arI)\n'
assert u40.count(old) == 1
u41 = u40.replace('kernel_entry_reachU40', 'kernel_entry_reachU41', 1).replace('KFinAtR13', 'KFinAtR41') \
    .replace('KFinEv13', 'KFinEv41').replace(old, old + '    (hFpu : FpuImplDet)\n')
u40of = u40.replace('kernel_entry_reachU40', 'kernel_entry_reachU40_of41', 1).replace(old, old + '    (hFpu : FpuImplDet)\n')
hb = 'set_option maxHeartbeats 8000000 in\n'
out = (P('scratch/p3J/U41head.lean').read_text() + hb + '/-- **`kernel_entry_reachU41`** (module docstring). -/\n'
       + u41 + '\n' + P('scratch/p3J/U41p41.lean').read_text() + '\n' + hb
       + '/-- **U41 gives U40** under `FpuImplDet` (module docstring). -/\n' + u40of + '\n'
       + P('scratch/p3J/U41p40.lean').read_text() + '\nend\n\nend\n\nend Fl4Proofs.P3.SInvR.G5\n')
P('Fl4Proofs/P3/XTopJointKEntryU41.lean').write_text(out)
print('ok')
