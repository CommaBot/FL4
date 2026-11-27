# virt gen 7 item 3: generate VirtKEntryV.lean (kernel_entry_reachV) from U36I's statement text.
import re, sys
src = open('Fl4Proofs/P3/XTopJointKEntryU36I.lean').read()
i = src.index('theorem kernel_entry_reachU36I ')
j = src.index('\n  := by', i)
st = src[i:j]
def rep(a, b, cnt=1):
    global st
    n = st.count(a)
    assert n >= 1, a
    st = st.replace(a, b) if cnt == 0 else st.replace(a, b, cnt)
rep('theorem kernel_entry_reachU36I ', 'theorem kernel_entry_reachV ')
rep('    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hJ : JReachU36I (L := L) arI AR MR s a σ) :',
    '    (hvk : Fl4Spec.virtKind = .none) (onCore : Fl4Spec.ObjRef → Bool)\n'
    '    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hJ : JReachU36I (L := L) arI AR MR s a σ) (hNR : VirtR7e.NR σ) :')
rep("        syscall.handle_syscall st arI s a n ⦃ r =>\n          ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧\n            RJ",
    "        VirtAgree.ScopeE6 c σ →\n        syscall.handle_syscall st arI s a n ⦃ r =>\n          ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscallV (Z := Unit) onCore true c σ).1 ∧\n            (RJ")
rep("SInvUZ.UtPgR σ' ∧ JReachU36I (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧",
    "SInvUZ.UtPgR σ' ∧ JReachU36I (L := L) arI AR MR r.1 r.2 σ') ∧ VirtR7e.NR σ' ⦄) ∧")
st, n1 = re.subn(r"∃ σ', EvOut false (\(.*?\)|\.interrupt) σ σ' ∧\n          RJ",
                 lambda m: "∃ σ', VirtExtTop.EvOutV onCore " + m.group(1) + " σ σ' ∧\n          (RJ", st)
st, n2 = re.subn(r"KEvSpec (\(.*?\)) true ev ∧ EvOut true ev σ σ' ∧\n          RJ",
                 lambda m: "KEvSpec " + m.group(1) + " true ev ∧ VirtKEntryV.EvOutVT onCore ev σ σ' ∧\n          (RJ", st)
st, n3 = re.subn(r"SpecUtZ σ' ∧ JReachU36I \(L := L\) arI AR MR r\.1 r\.2 σ' ⦄\)",
                 "SpecUtZ σ' ∧ JReachU36I (L := L) arI AR MR r.1 r.2 σ') ∧ VirtR7e.NR σ' ⦄)", st)
st, n4 = re.subn(r"(          KFinEv13 \(L := L\) arI AR ev \(KFront\w+ \(st := st\) arI[^\n]*\) w\.2\) →\n)(        syscall\.handle_\w+ st arI s a (?:v|n) ⦃ r => ∃ ev σ', KEvSpec (\(.*?\)) true ev)",
                 lambda m: m.group(1) + "        (∀ ev, KEvSpec " + m.group(3) + " true ev → ∀ c, ev = .syscallEvent c → VirtAgree.ScopeE6 c σ) →\n" + m.group(2), st)
print(n1, n2, n3, n4, file=sys.stderr)
assert (n1, n2, n3, n4) == (3, 2, 5, 2), (n1, n2, n3, n4)
proof = '''
  := by
  obtain ⟨Z, H, Cs, Ac, Lst, D, J, hX, hCB, hW, hI, hN, hR, hFl, hPg, hSys, hIrq, hUs, hVm, hTr, hSU⟩ :=
    kernel_entry_reachU36I arI AR MR hARI hA hnd hM hIp hKD hIo hIoa hPAi hIA hT hmax htu hRef hPI hSX hDR hJ
  refine ⟨Z, H, Cs, Ac, Lst, D, J, hX, hCB, hW, hI, hN, hR, hFl, hPg, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n c hct hn hfl hK hDL hFin hr
    exact VirtAgree.kentryV_post6 hvk onCore hNR hr (hSys n c hct hn hfl hK hDL hFin)
  · intro w a1 hIh hE
    exact VirtExtTop.evV_post hvk onCore (fun c h => by cases h) hNR (hIrq w a1 hIh hE)
  · intro n c hct hU hE
    exact VirtExtTop.evV_post hvk onCore (fun c h => by cases h) hNR (hUs n c hct hU hE)
  · intro ad c ft hct hVm' hE
    exact VirtExtTop.evV_post hvk onCore (fun c h => by cases h) hNR (hVm ad c ft hct hVm' hE)
  · intro v hct hv hE hsc
    refine WP.spec_mono (hTr v hct hv hE) ?_
    rintro r ⟨ev, σ', hK, hO, hrest⟩
    obtain ⟨e1, e2⟩ := VirtKEntryV.evOutVT_of hvk onCore hNR (hsc ev hK) hO
    exact ⟨ev, σ', hK, e1, hrest, e2⟩
  · intro n hct hU hD hE hsc
    refine WP.spec_mono (hSU n hct hU hD hE) ?_
    rintro r ⟨ev, σ', hK, hO, hrest⟩
    obtain ⟨e1, e2⟩ := VirtKEntryV.evOutVT_of hvk onCore hNR (hsc ev hK) hO
    exact ⟨ev, σ', hK, e1, hrest, e2⟩
'''
head = open('scratch/virt/kentryV_head.lean').read()
open('Fl4Proofs/P3/VirtKEntryV.lean', 'w').write(head + 'set_option maxHeartbeats 8000000 in\n'
  '/-- **`kernel_entry_reachV`: U36I restated against the extended spec** (module docstring). -/\n'
  + st + proof + '\nend\n\nend\n\nend Fl4Proofs.P3.SInvR.G5\n')
