# virt gen 3: SpecInvDvK1..K3 (the OBK object-size family, s26) copied as the object-TYPE family TYK
# (every object's aType satisfies a predicate). Run from proofs/: python3 scratch/virt/mkty.py
import re
src = {1: 'Fl4Proofs/P3/SpecInvDvK1.lean', 2: 'Fl4Proofs/P3/SpecInvDvK2.lean', 3: 'Fl4Proofs/P3/SpecInvDvK3.lean'}
HDR1 = '''/-
P3x for virtualization (line virt, gen 3; proofs/VIRT-PLAN.md §10 R7 (b)): **the object-type family `TYK`**
(spec side only, outside the `JAtZ` cone).

For a predicate `T` on (address, object type) pairs, `TIn T σ`: every object of the heap, with its `aType`, is in
`T`; `TYK T m := IK (TIn T) m`. The family is SpecInvDvK1..K3's `OBK` (the object half of device
`valid_untyped`, itself SpecInvUtZK1..K3 renamed) with `objBits ko` replaced by `aType ko`, mechanically
(proofs/scratch/virt/mkty.py); only the leaf `ty_setObject` changes (`set_object` asserts the old object's type,
so the type is kept directly). Its use: `T := fun _ t => t ≠ .aArch .aVcpu` is "no VCPU object" (VirtR7b), kept
by `rec_del` and `cap_revoke` (`ty_recDel`, `ty_capRevoke`). No premises; new files only.
-/
'''
def conv(s, k):
    s = s.replace('namespace Fl4Proofs.P3.SInvDV', 'namespace Fl4Proofs.P3.SInvTY')
    s = s.replace('end Fl4Proofs.P3.SInvDV', 'end Fl4Proofs.P3.SInvTY')
    s = s.replace('import Fl4Proofs.P3.SpecInvDvK1', 'import Fl4Proofs.P3.VirtTyK1')
    s = s.replace('import Fl4Proofs.P3.SpecInvDvK2', 'import Fl4Proofs.P3.VirtTyK2')
    s = re.sub(r'\bob0_auto\b', 'ty0_auto', s)
    s = re.sub(r'\bob_', 'ty_', s)
    s = re.sub(r'\bOBKE\b', 'TYKE', s)
    s = re.sub(r'\bOBK\b', 'TYK', s)
    s = re.sub(r'\bObSet\b', 'TySet', s)
    s = re.sub(r'\bOIn\b', 'TIn', s)
    if k == 1:
        a = s.index('/-'); b = s.index('-/') + 3
        s = s[:a] + HDR1 + s[b:]
        old_def = s[s.index('/-- A set of objects'):s.index('variable {O : TySet}')]
        new_def = '''/-- A set of (address, object type) pairs. -/
abbrev TySet := ObjRef → AType → Prop

/-- **Every object of the heap, with its type, is in `O`.** -/
def TIn (O : TySet) (σ : State Unit) : Prop := ∀ o ko, σ.kheap o = some ko → O o (aType ko)

abbrev TYK (O : TySet) {α : Type} (m : NonDet (State Unit) α) : Prop := IK (TIn O) m
abbrev TYKE (O : TySet) {ε α : Type} (m : NonDetE (State Unit) ε α) : Prop := IKE (TIn O) m

'''
        s = s.replace(old_def, new_def)
        s = s.replace('    rw [← dv_objBits_of_aType hty]\n', '    rw [← hty]\n')
    else:
        first, rest = s.split('\n', 1)
        assert first.startswith('/- s26') and first.endswith('-/'), first
        s = ('/- virt gen 3: the object-type family `TYK`, part %d (SpecInvDvK%d with `aType` for `objBits`, '
             'proofs/scratch/virt/mkty.py; see VirtTyK1). -/\n' % (k, k)) + rest
    return s
for k, p in src.items():
    s = open(p).read()
    t = conv(s, k)
    body = t[t.index('-/'):]
    assert 'objBits' not in body and 'OBK' not in body and 'SInvDV' not in body, (k, [l for l in body.splitlines() if 'objBits' in l or 'OBK' in l or 'SInvDV' in l][:5])
    open('Fl4Proofs/P3/VirtTyK%d.lean' % k, 'w').write(t)
