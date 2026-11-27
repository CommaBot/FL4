# gen 11: writes Fl4Proofs/P3/XTopJointKEntryU43.lean from XTopJointKEntryU42.lean
src=open('Fl4Proofs/P3/XTopJointKEntryU42.lean').read()
i0=src.index('set_option maxHeartbeats 8000000 in\n/-- **`kernel_entry_reachU42`**')
i1=src.index('set_option maxHeartbeats 8000000 in\n/-- **U42 gives U41**')
u42=src[i0:i1]
st0=u42.index('theorem kernel_entry_reachU42'); pr=u42.index('   := by\n')
stmt=u42[st0:pr]
assert stmt.count('KFinAtR42')==1 and stmt.count('KFinEv42')==5
def rm(s,old,n=1):
    assert s.count(old)==n,(old,s.count(old)); return s.replace(old,'')
s43=stmt.replace('theorem kernel_entry_reachU42','theorem kernel_entry_reachU43')
s43=s43.replace('    (hFpu : FpuImplDet)\n','    (hFpu : FpuImplDet) (hFW : FpuWriteDet)\n')
s43=rm(s43,'''        (∀ x ∈ (specFront c σ).1, ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64)
          (D' : Set U64) (s' : S) (a' : A), KFrontF (L := L) arI n s a s' a' →
            JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 →
            KFinAtR42 (L := L) arI AR Z' H' Cs' s' a' x.2) →
''')
s43=rm(s43,"        KFinEv42 (L := L) arI AR .interrupt (KFrontI (st := st) arI s a1 w) σ →\n")
s43=rm(s43,"        KFinEv42 (L := L) arI AR (.userLevelFault n.bv c.bv) (KFrontF2 (st := st) arI (brU (st := st) arI n c) s a) σ →\n")
s43=rm(s43,"        KFinEv42 (L := L) arI AR (.vmFaultEvent ft) (KFrontF2 (st := st) arI (brV (st := st) arI ad c) s a) σ →\n")
s43=rm(s43,'''        (∀ ev, KEvSpec (.trap v) true ev → ∀ w ∈ (Fl4Spec.fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
          KFinEv42 (L := L) arI AR ev (KFrontTrap (st := st) arI s a) w.2) →
''')
s43=rm(s43,'''        (∀ ev, KEvSpec (.sysU n) true ev → ∀ w ∈ (Fl4Spec.fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
          KFinEv42 (L := L) arI AR ev (KFrontSysU (st := st) arI n s a) w.2) →
''')
assert 'KFin' not in s43
s42=stmt.replace('theorem kernel_entry_reachU42','theorem kernel_entry_reachU42_of43').replace(
    '    (hFpu : FpuImplDet)\n','    (hFpu : FpuImplDet) (hFW : FpuWriteDet)\n')
args='arI AR MR hARI hA hnd hM hIp hKD hIo hIoa hPAi hIA hT hmax htu hRef hPI hSX hDR hMap hFpu'
K='(kFinEv42_of hFpu hFW hA)'
p43=f'''   := by
  obtain ⟨Z, H, Cs, Ac, Lst, D, J, hX, hCB, hW, hI, hN, hR, hFl, hPg, hSys, hIrq, hUs, hVm, hTr, hSU⟩ :=
    kernel_entry_reachU42 {args} hJ
  refine ⟨Z, H, Cs, Ac, Lst, D, J, hX, hCB, hW, hI, hN, hR, hFl, hPg, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n c hct hn hfl hK hDL
    exact hSys n c hct hn hfl hK hDL (fun _ _ _ _ _ _ _ _ _ _ _ _ => kFinAtR42_of hFpu hFW hA)
  · intro w a1 hIh; exact hIrq w a1 hIh {K}
  · intro n c hct hU; exact hUs n c hct hU {K}
  · intro ad c ft hct hVm'; exact hVm ad c ft hct hVm' {K}
  · intro v hct hv; exact hTr v hct hv (fun _ _ _ _ => {K})
  · intro n hct hU hD; exact hSU n hct hU hD (fun _ _ _ _ => {K})
'''
p42=f'''   := by
  obtain ⟨Z, H, Cs, Ac, Lst, D, J, hX, hCB, hW, hI, hN, hR, hFl, hPg, hSys, hIrq, hUs, hVm, hTr, hSU⟩ :=
    kernel_entry_reachU43 {args} hFW hJ
  refine ⟨Z, H, Cs, Ac, Lst, D, J, hX, hCB, hW, hI, hN, hR, hFl, hPg, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n c hct hn hfl hK hDL _; exact hSys n c hct hn hfl hK hDL
  · intro w a1 hIh _; exact hIrq w a1 hIh
  · intro n c hct hU _; exact hUs n c hct hU
  · intro ad c ft hct hVm' _; exact hVm ad c ft hct hVm'
  · intro v hct hv _; exact hTr v hct hv
  · intro n hct hU hD _; exact hSU n hct hU hD
'''
head=open('scratch/p3J/U43head.lean').read()
out=head+'set_option maxHeartbeats 8000000 in\n/-- **`kernel_entry_reachU43`** (module docstring). -/\n'+s43+p43
out+='\nset_option maxHeartbeats 8000000 in\n/-- **U43 gives U42** under `FpuWriteDet` (module docstring). -/\n'+s42+p42
out+='\nend\n\nend\n\nend Fl4Proofs.P3.SInvR.G5\n'
open('Fl4Proofs/P3/XTopJointKEntryU43.lean','w').write(out)
