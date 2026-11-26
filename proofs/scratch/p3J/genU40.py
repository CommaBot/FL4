# gen 6: XTopJointKEntryU40 = U39 with start / exits JReachU38 -> JReachU40 (= JReachU36I ∧ IoaRel), proved from
# the p3J transport's copy of U33 (Fl4ProofsJ...kernel_entry_reachU33) as irqfix3's U36I is from U33;
# bridges kernel_entry_reachU39_of40, kernel_entry_reachU36I_of40.
import pathlib
P = pathlib.Path
def stmt(path, name):
    src = P(path).read_text().splitlines()
    st = next(i for i,l in enumerate(src) if l.startswith('theorem %s ' % name))
    en = next(i for i in range(st, len(src)) if src[i].rstrip().endswith(':= by'))
    s = '\n'.join(src[st:en+1])
    return s
u39 = stmt('Fl4Proofs/P3/XTopJointKEntryU39.lean', 'kernel_entry_reachU39')
assert u39.count('JReachU38') == 7, u39.count('JReachU38')
u40 = u39.replace('kernel_entry_reachU39', 'kernel_entry_reachU40', 1).replace('JReachU38', 'JReachU40')
u39of40 = u39.replace('kernel_entry_reachU39', 'kernel_entry_reachU39_of40', 1)
u36i = P('Fl4Proofs/P3/XTopJointKEntryU36I.lean').read_text().splitlines()
st = next(i for i,l in enumerate(u36i) if l.startswith('theorem kernel_entry_reachU36I '))
en = next(i for i in range(st, len(u36i)) if u36i[i].strip() == ':= by')
s36 = '\n'.join(u36i[st:en+1]).replace('kernel_entry_reachU36I', 'kernel_entry_reachU36I_of40', 1)
old = '{s : S} {a : A} {σ : Fl4Spec.State Unit} (hJ : JReachU36I (L := L) arI AR MR s a σ) :'
assert s36.count(old) == 1
s36 = s36.replace(old, '(hMap : IoaMap arI)\n    ' + old.replace(') :', ') (hIR : IoaRel arI σ) :'))
assert s36.count('KDispHypsKVU32') == 1 and s36.count('JReachU36I') == 7
head = P('scratch/p3J/U40head.lean').read_text()
p40 = P('scratch/p3J/U40p40.lean').read_text()
p39 = P('scratch/p3J/U40p39.lean').read_text()
p36 = P('scratch/p3J/U40p36.lean').read_text()
hb = 'set_option maxHeartbeats 8000000 in\n'
out = (head + hb + '/-- **`kernel_entry_reachU40`** (module docstring). -/\n' + u40 + '\n' + p40 + '\n' +
       hb + '/-- **U40 gives U39** (module docstring): U39\'s statement, verbatim. -/\n' + u39of40 + '\n' + p39 + '\n' +
       hb + '/-- **U40 gives U36I** with `IoaMap` and the start\'s `IoaRel` (module docstring). -/\n' + s36 + '\n' + p36 +
       '\nend\n\nend\n\nend Fl4Proofs.P3.SInvR.G5\n')
P('Fl4Proofs/P3/XTopJointKEntryU40.lean').write_text(out)
