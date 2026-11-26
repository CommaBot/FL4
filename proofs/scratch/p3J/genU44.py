# gen 12: writes Fl4Proofs/P3/XTopJointKEntryU44.lean from XTopJointKEntryU43.lean's statement text
src=open('Fl4Proofs/P3/XTopJointKEntryU43.lean').read()
i0=src.index('theorem kernel_entry_reachU43 ')
pr=src.index('   := by\n',i0)
stmt=src[i0:pr]
assert stmt.count('KDispHypsKVU39')==1
assert stmt.count('    (hFpu : FpuImplDet) (hFW : FpuWriteDet)\n')==1
s44=stmt.replace('theorem kernel_entry_reachU43 ','theorem kernel_entry_reachU44 ').replace(
    'KDispHypsKVU39','KDispHypsKVU44').replace(
    '    (hFpu : FpuImplDet) (hFW : FpuWriteDet)\n','    (hFpu : FpuImplDet) (hFW : FpuWriteDet) (hCfg : KCfgFL4)\n')
s43=stmt.replace('theorem kernel_entry_reachU43 ','theorem kernel_entry_reachU43_of44 ').replace(
    '    (hFpu : FpuImplDet) (hFW : FpuWriteDet)\n','    (hFpu : FpuImplDet) (hFW : FpuWriteDet) (hCfg : KCfgFL4)\n')
args='arI AR MR hARI hA hnd hM hIp hKD hIo hIoa hPAi hIA hT hmax htu hRef hPI hSX hDR hMap hFpu hFW'
def prf(base,conv,extra):
    return f'''   := by
  obtain ⟨Z, H, Cs, Ac, Lst, D, J, hX, hCB, hW, hI, hN, hR, hFl, hPg, hSys, hIrq, hUs, hVm, hTr, hSU⟩ :=
    {base} {args}{extra} hJ
  refine ⟨Z, H, Cs, Ac, Lst, D, J, hX, hCB, hW, hI, hN, hR, hFl, hPg, ?_, hIrq, hUs, hVm, hTr, hSU⟩
  intro n c hct hn hfl hK hDL
  exact hSys n c hct hn hfl (fun σb hB V' Ac' Lst' D' s' a' hF hJ' => (hK σb hB V' Ac' Lst' D' s' a' hF hJ').{conv}) hDL
'''
head=open('scratch/p3J/U44head.lean').read()
out=head+'set_option maxHeartbeats 8000000 in\n/-- **`kernel_entry_reachU44`** (module docstring). -/\n'+s44+prf('kernel_entry_reachU43','toU39 hCfg','')
out+='\nset_option maxHeartbeats 8000000 in\n/-- **U44 gives U43** under `KCfgFL4` (module docstring). -/\n'+s43+prf('kernel_entry_reachU44','toU44',' hCfg')
out+='\nend\n\nend\n\nend Fl4Proofs.P3.SInvR.G5\n'
open('Fl4Proofs/P3/XTopJointKEntryU44.lean','w').write(out)
