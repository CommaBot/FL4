# jboot gen 5: IrqCtlMR's IOAPIC / remapped IRQ control decodes on MaskMRF (irqfix's genA fix, applied to the
# un-narrowed originals irq_ioapic_refinesM / irq_remap_refinesM that U2's cone uses). Run from proofs/.
import re
P='Fl4Proofs/P3/'
ctl=open(P+'IrqCtlMR.lean').read().split('\n')
def rng(L,a,b): return '\n'.join(L[a-1:b])
io=rng(ctl,595,829)
rm=rng(ctl,831,1075)
assert io.startswith('/-- **`X86IRQIssueIRQHandlerIOAPIC`**') and 'theorem irq_ioapic_refinesM ' in io
assert rm.startswith('/-- **l4h `X86IRQIssueIRQHandlerIOAPICRemapped`**') and 'theorem irq_remap_refinesM ' in rm
assert 'theorem' not in io.split('theorem irq_ioapic_refinesM ')[1] and 'theorem' not in rm.split('theorem irq_remap_refinesM ')[1]
def fix(t):
    t=re.sub(r'\bMaskMR\b','MaskMRF',t)
    for n in ['invoke_mrM','irq_ioapic_refinesM','irq_remap_refinesM']:
        t=re.sub(r'\b'+n+r'\b',n+('Q' if n=='invoke_mrM' else 'Q0'),t)
    t=t.replace('have hz128 : z.val < 128 := by rw [hzv]; simp; omega',
      'have hz128 : z.val < 128 := by rw [hzv]; simp; omega\n  have hz126 : z.val < 126 := by rw [hzv]; simp; omega')
    t=t.replace('(show z.val < 256 by omega)','hz126')
    return t
io=fix(io); rm=fix(rm)
for t in (io,rm):
    assert t.count('hz126 : z.val')==1 and t.count('invoke_mrMQ')==1 and '256' not in t, t.count('hz126')
hdr=open('scratch/jboot5/A_head.lean').read()
out=hdr+'\n'+io+'\n\n'+rm+'\n\nend\n\nend\n\nend Fl4Proofs.P3\n'
open(P+'JBoot5CtlQ.lean','w').write(out)
print(len(out.split('\n')))
