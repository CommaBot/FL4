import re,sys
P='Fl4Proofs/P3/'
ctl=open(P+'IrqCtlMR.lean').read().split('\n')
nar=open(P+'ArchIrqNarrow.lean').read().split('\n')
def rng(L,a,b): return '\n'.join(L[a-1:b])
inv=rng(ctl,113,124)
iss=rng(ctl,253,415)   # issue_tailM + irq_issue_refinesM
msi=rng(ctl,416,594)
narM=rng(nar,528,1009)
def fix(t):
    t=re.sub(r'\bMaskMR\b','MaskMRF',t)
    for n in ['invoke_mrM','issue_tailM','irq_issue_refinesM','irq_msi_refinesM','irq_ioapic_refinesMN','irq_remap_refinesMN']:
        t=re.sub(r'\b'+n+r'\b',n+'Q',t)
    t=t.replace('have hz128 : z.val < 128 := by rw [hzv]; simp; omega',
      'have hz128 : z.val < 128 := by rw [hzv]; simp; omega\n  have hz126 : z.val < 126 := by rw [hzv]; simp; omega')
    t=t.replace('(show z.val < 256 by omega)','hz126')
    return t
inv=fix(inv).replace('(hR : MR a ms) (hirq : irq.val < 256)','(hR : MR a ms) (hirq : irq.val < 126)')
inv=inv.replace('ms hR hirq)','ms hR (by rw [sig_inact_false]; exact hirq))')
iss=fix(iss)
iss=iss.replace('(irq : U64) (hirq : irq.val < 128) (hin :','(irq : U64) (hirq : irq.val < 128) (hirq6 : irq.val < 126) (hin :',1)
iss=iss.replace('(show irq.val < 256 by omega)','hirq6')
iss=iss.replace('hmask ct hcur htcb hact hact2 y0 (by omega)\n','hmask ct hcur htcb hact hact2 y0 (by omega) (by omega)\n')
msi=fix(msi); narM=fix(narM)
for t,k in [(inv,'mrMQ'),(iss,'hirq6'),(msi,'hz126'),(narM,'hz126')]:
    assert k in t, k
assert narM.count('hz126 : z.val')==2 and msi.count('hz126 : z.val')==1, (narM.count('hz126 : z.val'),msi.count('hz126 : z.val'))
assert '256' not in iss+msi+narM, [l for l in (iss+msi+narM).split('\n') if '256' in l]
hdr=open('scratch/irqfix/A_head.lean').read()
out=hdr+'\n'+inv+'\n\n'+iss+'\n\n'+msi+'\n\n'+narM+'\n\nend\n\nend\n\nend Fl4Proofs.P3\n'
open(P+'IrqFixA.lean','w').write(out)
print(len(out.split('\n')))
