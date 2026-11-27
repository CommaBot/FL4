P='Fl4Proofs/P3/'
L=open(P+'XTopJointKEntryU32.lean').read().split('\n')
st='\n'.join(L[70:129])   # lines 71..129
assert st.startswith('theorem kernel_entry_reachU32 ') and st.endswith(':= by')
u33=st.replace('theorem kernel_entry_reachU32 ','theorem kernel_entry_reachU33 ')
a='(hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)'
assert a in u33
u33=u33.replace(a,'(hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR)')
b='(hIA : IrqPlatA arI AR)'; assert b in u33
u33=u33.replace(b,'(hIA : IrqPlatK arI AR)')
c="JDecMRLK (L := L) arI VtxK AR MR (Z.mv Z.G V') H Cs D' s' a' σb ct')"; assert u33.count(c)==1
u33=u33.replace(c,"JDecMRLK (L := L) arI VtxK AR MR (Z.mv Z.G V') H Cs D' s' a' σb ct' ∧\n                IrqAckU (L := L) arI MR (Z.mv Z.G V') s' a' σb)")
u33+='''
  exact Fl4ProofsQ.P3.SInvR.G5.kernel_entry_reachU32 arI AR MR hARI hA hnd (MachPlatF.toT hM hIp) hKD hIo hIoa
    hPAi hIA hT hmax htu hRef hPI hSX hDR hJ'''
u32=st.replace('theorem kernel_entry_reachU32 ','theorem kernel_entry_reachU32_of33 ')
u32+='''
  obtain ⟨Z, H, Cs, Ac, Lst, D, J, hX, hW, hI, hN, hR, hFl, hPg, hSys, hIrq, hUs, hVm, hTr, hSU⟩ :=
    kernel_entry_reachU33 arI AR MR hARI hA hnd (MachPlat.toF hM) (IrqPlatA.toIpiF hIA) hKD hIo hIoa hPAi
      (IrqPlatA.toK hIA) hT hmax htu hRef hPI hSX hDR hJ
  exact ⟨Z, H, Cs, Ac, Lst, D, J, hX, hW, hI, hN, hR, hFl, hPg,
    fun n c hct hn hfl hK hDL hFin => hSys n c hct hn hfl hK (fun σb hb V' Ac' Lst' D' s' a' hF J' ct' hct' =>
      ⟨hDL σb hb V' Ac' Lst' D' s' a' hF J' ct' hct', IrqAckU.of_machPlat hM⟩) hFin,
    hIrq, hUs, hVm, hTr, hSU⟩'''
out=open('scratch/irqfix/U_head.lean').read()+'''
/-- **`kernel_entry_reachU33`** (module docstring): `kernel_entry_reachU32` with `MachPlatF` + `IpiF` for
`MachPlat`, `IrqPlatK` for `IrqPlatA`, and the syscall clause's decode premise with `IrqAckU`. -/
'''+u33+'''

/-- **U33 is at least as strong as U32**: `kernel_entry_reachU32`'s statement, from U33 (its premises give
U33's: `MachPlat.toF`, `IrqPlatA.toIpiF`, `IrqPlatA.toK`, `IrqAckU.of_machPlat`). -/
'''+u32+'\n\nend\n\nend\n\nend Fl4Proofs.P3.SInvR.G5\n'
open(P+'XTopJointKEntryU33.lean','w').write(out)
print('ok')
