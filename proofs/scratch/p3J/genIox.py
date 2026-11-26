# p3J gen 4: SpecInvIoxF/G/E = SpecInvDomF/G/E with the projection dlV (domain list) replaced by ioxV
# (the IOAPIC count and pin counts): a scripted renaming; VsDom's FK combinators are generic in the projection.
import re, sys
root = sys.argv[1]
P = root + '/Fl4Proofs/P3/'
def ren(t):
    t = t.replace('sf_unfold', 'iox_unfold')
    t = re.sub(r'\bdle_', 'ioxe_', t)
    t = re.sub(r'\bdl_', 'iox_', t)
    t = re.sub(r'\bDLE\b', 'IOXE', t)
    t = re.sub(r'\bDL\b', 'IOX', t)
    t = re.sub(r'\bdlV\b', 'ioxV', t)
    t = t.replace('SInvDom', 'SInvIox')
    t = t.replace('Fl4Proofs.P3.SpecInvDomF', 'Fl4Proofs.P3.SpecInvIoxF').replace('Fl4Proofs.P3.SpecInvDomG', 'Fl4Proofs.P3.SpecInvIoxG')
    t = t.replace('Fl4Proofs.P3.SpecInvIoxL', 'Fl4Proofs.P3.SpecInvDomL')   # the lfp lemma is reused, not copied
    t = t.replace('SInvIoxL.', 'SInvDomL.')
    return t
def body(t):  # drop the original module docstring
    assert t.startswith('/-')
    return t[t.index('-/') + 2:].lstrip('\n')
F = open(P + 'SpecInvDomF.lean').read()
F = body(F)
F = F.replace('''/-- The fields `DomListOK` reads. -/
def dlV (σ : State Unit) : List (Domain × DomainDuration) × Nat × Nat :=
  (σ.domainList, σ.domainStartIndex, σ.domainIndex)''', '''/-- The IOAPIC count and the pin counts of the spec's arch state (`x64_num_ioapics`,
`x64_ioapic_nirqs`; written by no spec step). -/
def dlV (σ : State Unit) : Word64 × (Word → BitVec 8) :=
  (σ.archState.x64NumIoapics, σ.archState.x64IoapicNirqs)''')
assert 'x64NumIoapics' in F
hdr = lambda name, what: ('/-\nP3 (line p3J, gen 4): %s (spec side only, outside the JAtZ cone): `%s` with the projection\n'
  '`dlV` (the domain list) replaced by `ioxV` (`x64_num_ioapics`, `x64_ioapic_nirqs`), a scripted renaming\n'
  '(`scratch/p3J/genIox.py`; VsDom\'s `FK` combinators are generic in the projection). No sorry.\n-/\n') % (what, name)
open(P + 'SpecInvIoxF.lean', 'w').write(hdr('SpecInvDomF', '**the IOAPIC-count frame, kit**') + ren(F))
G = body(open(P + 'SpecInvDomG.lean').read())
open(P + 'SpecInvIoxG.lean', 'w').write(hdr('SpecInvDomG', '**the IOAPIC-count frame, leaves**') + ren(G))
E = body(open(P + 'SpecInvDomE.lean').read())
open(P + 'SpecInvIoxE.lean', 'w').write(hdr('SpecInvDomE', '**the IOAPIC-count frame, kernel-entry pieces**') + ren(E))
print('ok')
