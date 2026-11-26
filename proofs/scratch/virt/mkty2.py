# virt gen 4: SpecInvDvK4..K6 (the OBK object-size family, s26) copied as parts 4..6 of the object-TYPE family
# TYK (VirtTyK1..3, scratch/virt/mkty.py). Run from proofs/: python3 scratch/virt/mkty2.py
import re
for k in (4, 5, 6):
    s = open('Fl4Proofs/P3/SpecInvDvK%d.lean' % k).read()
    s = s.replace('namespace Fl4Proofs.P3.SInvDV', 'namespace Fl4Proofs.P3.SInvTY')
    s = s.replace('end Fl4Proofs.P3.SInvDV', 'end Fl4Proofs.P3.SInvTY')
    s = s.replace('import Fl4Proofs.P3.SpecInvDvK%d' % (k - 1), 'import Fl4Proofs.P3.VirtTyK%d' % (k - 1))
    s = re.sub(r'\bob0_auto\b', 'ty0_auto', s)
    s = re.sub(r'\bob_auto\b', 'ty_auto', s)
    s = re.sub(r'\bob_leaf\b', 'ty_leaf', s)
    s = re.sub(r'\bob_', 'ty_', s)
    s = re.sub(r'\bOBKE\b', 'TYKE', s)
    s = re.sub(r'\bOBK\b', 'TYK', s)
    s = re.sub(r'\bObSet\b', 'TySet', s)
    s = re.sub(r'\bOIn\b', 'TIn', s)
    first, rest = s.split('\n', 1)
    assert first.startswith('/- s26') and first.endswith('-/'), first
    s = ('/- virt gen 4: the object-type family `TYK`, part %d (SpecInvDvK%d with `aType` for `objBits`, '
         'proofs/scratch/virt/mkty2.py; see VirtTyK1). -/\n' % (k, k)) + rest
    body = s[s.index('-/'):]
    assert 'objBits' not in body and 'OBK' not in body and 'SInvDV' not in body and 'DvK' not in body
    open('Fl4Proofs/P3/VirtTyK%d.lean' % k, 'w').write(s)
