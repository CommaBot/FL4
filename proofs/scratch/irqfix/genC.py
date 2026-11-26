import re
P='Fl4Proofs/P3/'
def rng(f,a,b): return '\n'.join(open(P+f).read().split('\n')[a-1:b])
a1=rng('XTopJointMRPath.lean',449,494)
a2=rng('XTopJointKEntry38.lean',728,775)
j=rng('XTopJointKEntry39.lean',320,369)
def plat(t):
    t=t.replace('(hM : MachPlat arI MR)','(hM : MachPlatT arI MR)').replace('(hIP : IrqPlatA arI AR)','(hIP : IrqPlatK arI AR)')
    return t
a1=plat(a1).replace('theorem afterInv_of_mcsIMN ','theorem afterInv_of_mcsIMNQ ')
a1=a1.replace('(hIP.noIpi a1)','(hM.noIpi a1 _ hR1)').replace('J2.handleIrqJIAN hARI hAT hIP hmbA hN\'','Fl4ProofsQ.P3.JAtZ.handleIrqJIAN hARI hAT hIP hmbA J2 hN\'')
a2=plat(a2).replace('theorem afterInv_of_mcsIMNM ','theorem afterInv_of_mcsIMNMQ ')
a2=a2.replace('(hIP.noIpi a1)','(hM.noIpi a1 _ hR1)').replace('J2.handleIrqJIANM hM hKD hARI hAT hIP hmbA hN\'','Fl4ProofsQ.P3.JAtZ.handleIrqJIANM hM hKD hARI hAT hIP hmbA J2 hN\'')
for t in (a1,a2): assert 'hM.noIpi' in t and 'Fl4ProofsQ.P3.JAtZ' in t
j=plat(j).replace('theorem jDecMRL_of ','theorem jDecMRL_ofQ ')
j=j.replace('(hE : JEntryAt (L := L) arI AR Z H Cs s ar σ)','(hE : Fl4ProofsI.P3.JEntryAtN (L := L) arI AR Z H Cs s ar σ)')
j=j.replace('(hDL : JDecMRL2 (L := L) arI AR MR Z H Cs D s ar σ ct)','(hDL : JDecMRL2Q (L := L) arI AR MR Z H Cs D s ar σ ct)')
j=j.replace('have hX0 := decOK_JMU','have hX0 := Fl4ProofsI.P3.decOK_JMU')
j=j.replace('exact XCapP.mr hM','exact Fl4ProofsQ.P3.XCapP.mr hM')
j=j.replace('exact XCapP.mrG ','exact Fl4ProofsQ.P3.XCapP.mrG ')
j=j.replace('(hM.mask ar irq false _ hR (by omega))','(hDL.2 sl irq hsl hc hirq hR)')
j=j.replace('exact (decode_invocation_irq_controlXSM','exact (Fl4ProofsQI.P3.decode_invocation_irq_controlXSM')
j=j.replace('(fun a ms ms\' h e => mF_mr hM h e)','(fun a ms ms\' h e => Fl4ProofsQ.P3.mF_mr hM h e)')
j=j.replace('    exact hDL hR hVT','    exact hDL.1 hR hVT')
for k in ['JEntryAtN','JDecMRL2Q','Fl4ProofsI.P3.decOK_JMU','Fl4ProofsQ.P3.XCapP.mr hM','Fl4ProofsQ.P3.XCapP.mrG','hDL.2 sl','Fl4ProofsQI.P3.decode','Fl4ProofsQ.P3.mF_mr','hDL.1 hR']:
    assert k in j, k
head=open('scratch/irqfix/C_head.lean').read()
mid=open('scratch/irqfix/C_mid.lean').read()
out=head+'\n'+a1+'\n\n'+a2+'\n\nend\n\n'+mid+'\n'+j+'\n\n'+open('scratch/irqfix/C_tail.lean').read()
open(P+'IrqFixC.lean','w').write(out)
print('ok')
