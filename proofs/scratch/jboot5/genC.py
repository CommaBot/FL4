# jboot gen 5: KEntry39's `jDecMRL_of` (the un-narrowed lineage U2's cone uses) on MachPlatT with the IRQ ack by
# irqfix's IrqAckU (JDecMRL2Q), as irqfix's genC.py did for the narrowed copy. Run from proofs/.
P='Fl4Proofs/P3/'
def rng(f,a,b): return '\n'.join(open(P+f).read().split('\n')[a-1:b])
j=rng('XTopJointKEntry39.lean',320,369)
assert j.startswith('set_option maxHeartbeats 4000000 in') and 'theorem jDecMRL_of ' in j
R=[('theorem jDecMRL_of ','theorem jDecMRL_ofQ0 '),
   ('(hM : MachPlat arI MR)','(hM : MachPlatT arI MR)'),
   ('(hDL : JDecMRL2 (L := L) arI AR MR Z H Cs D s ar σ ct)','(hDL : JDecMRL2Q (L := L) arI AR MR Z H Cs D s ar σ ct)'),
   ('exact XCapP.mr hM','exact Fl4ProofsQ.P3.XCapP.mr hM'),
   ('exact XCapP.mrG ','exact Fl4ProofsQ.P3.XCapP.mrG '),
   ('(hM.mask ar irq false _ hR (by omega))','(hDL.2 sl irq hsl hc hirq hR)'),
   ('exact (decode_invocation_irq_controlXSM','exact (Fl4ProofsQ.P3.decode_invocation_irq_controlXSM'),
   ("(fun a ms ms' h e => mF_mr hM h e)","(fun a ms ms' h e => Fl4ProofsQ.P3.mF_mr hM h e)"),
   ('    exact hDL hR hVT','    exact hDL.1 hR hVT')]
for a,b in R:
    assert j.count(a)==1, a
    j=j.replace(a,b)
head=open('scratch/jboot5/C_head.lean').read()
tail=open('scratch/jboot5/C_tail.lean').read()
open(P+'JBoot5C.lean','w').write(head+'\n'+j+'\n\n'+tail)
print('ok')
