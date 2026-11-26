# gen 13: XTopJointKEntryU45 from U44's statement text (run from proofs/)
u=open('Fl4Proofs/P3/XTopJointKEntryU44.lean').read()
i=u.index('set_option maxHeartbeats 8000000 in\n/-- **`kernel_entry_reachU44`**')
j=u.index('set_option maxHeartbeats 8000000 in\n/-- **U44 gives U43**')
thm=u[i:j]
stmt44=thm[:thm.index(':= by')]
assert stmt44.count('JDecMRLK (L := L) arI VtxK')==1
s45=stmt44.replace('kernel_entry_reachU44','kernel_entry_reachU45').replace('JDecMRLK (L := L) arI VtxK','JDecMRLK (L := L) arI VtxU')
s45=s45.replace('/-- **`kernel_entry_reachU45`** (module docstring). -/','/-- **`kernel_entry_reachU45`** (module docstring): U44 with the per-entry `JDecMRLK VtxK` [J] narrowed to\n`JDecMRLK VtxU` [J] (D1 discharged by `jDecMRLK_ofVtxU`). -/')
s44o=stmt44.replace('kernel_entry_reachU44','kernel_entry_reachU44_of45').replace('/-- **`kernel_entry_reachU44_of45`** (module docstring). -/','/-- **U45 gives U44** (module docstring): U44\'s statement verbatim. -/')
args='arI AR MR hARI hA hnd hM hIp hKD hIo hIoa hPAi hIA hT hmax htu hRef hPI hSX hDR hMap hFpu hFW hCfg hJ'
def proof(src,conv):
  return f''':= by
  obtain ⟨Z, H, Cs, Ac, Lst, D, J, hX, hCB, hW, hI, hN, hR, hFl, hPg, hSys, hIrq, hUs, hVm, hTr, hSU⟩ :=
    {src} {args}
  refine ⟨Z, H, Cs, Ac, Lst, D, J, hX, hCB, hW, hI, hN, hR, hFl, hPg, ?_, hIrq, hUs, hVm, hTr, hSU⟩
  intro n c hct hn hfl hK hDL
  exact hSys n c hct hn hfl hK (fun σb hB V' Ac' Lst' D' s' a' hF hJ' ct' hct' =>
    {conv} (hDL σb hB V' Ac' Lst' D' s' a' hF hJ' ct' hct'))

'''
doc=open('scratch/p3J/U45head.lean').read()
out=doc+s45+proof('kernel_entry_reachU44','jDecMRLK_ofVtxU arI hA hKD')+s44o+proof('kernel_entry_reachU45','JDecMRLK.mono arI vtxU_vtxK')+'end\n\nend\n\nend Fl4Proofs.P3.SInvR.G5\n'
open('Fl4Proofs/P3/XTopJointKEntryU45.lean','w').write(out)
open('scratch/p3J/U44stmt.txt','w').write(stmt44)
open('scratch/p3J/U45stmt.txt','w').write(s45)
