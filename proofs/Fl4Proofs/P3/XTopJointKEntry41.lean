/-
P3 (DESIGN.md §9), invariant line G4 (g4k, KENTRY-PLAN g4k; g4j's handoff):
**`JUtResetHyp` [W] discharged** (the Untyped retypes with a reset, `MR` at
the outcome).

* `jUtResetHyp_of`: `JUtResetHyp` at a dispatch state from `JAtZ`,
  `JEntryGlobM`, `JEntryAt`, `MachPlat`, `MRKeepD` and the Untyped path's
  facts inside `JPathM` (the ones `jDecMRLK_ofU` passes to
  `JAtZ.jUtRetHypM` / `jUtRetHypDevM`): RAM caps by UtResetMR's
  `JAtZ.jUtResetMRM`, device caps by `JAtZ.jUtResetMRDev`.
* Copies (scratch/g4k/gentops.py from XTopJointKEntry40) with
  `hDL : … → JDecMRLK VtxK …` only: `dispatch_all13PUNM4`,
  `kernel_entryJ13PUGMD4`, NEW TOPS **`kernel_entryJ41`** and
  **`kernel_entry_reachMD4`** (`kernel_entryJ40` / `kernel_entry_reachMD3`
  without `JUtResetHyp`; the old ones kept). `hDL` is asked at the same
  states as before (σb after FaultIP + a passing budget check, `KFrontB`,
  `JAtZ (Z.mv Z.G V') …`).
-/
import Fl4Proofs.P3.XTopJointKEntry40
import Fl4Proofs.P3.UtResetMR
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {MR : A → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 8000000 in
/-- **`JUtResetHyp` at a dispatch state** (module docstring). -/
theorem jUtResetHyp_of [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (hG : JEntryGlobM (L := L) arI AR Z.th) (hE : JEntryAt (L := L) arI AR Z H Cs s ar σ)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (hM : MachPlat arI MR) (hKD : MRKeepD arI MR) :
    JUtResetHyp (L := L) arI AR MR Z H Cs D s ar σ ct := by
  intro hR hVT hVI lbl length blk call don fp buf extra slbl argsU hlen hargs hbuf hl ci sl hsl c hc p sb fi dev hcE
    hNat excaps buffer hXO hXN hLb hA5 hN
  subst hcE
  obtain ⟨hDv, hU⟩ := hN
  cases dev
  · have hN := hU rfl
    exact J.jUtResetMRM hE.ni hct hsl hc hN.bufObj hN.heapH.1 hN.heapH.2 hN.core0 hG.ari.toARKeep hG.tot hG.nd hM
      hG.ppA hKD hN.rcb hE.rd0 hE.ctnq hN.vsReach hE.urz hE.utks hR hVT hVI hNat
  · have hN := hDv rfl
    exact J.jUtResetMRDev hE.ni hct hsl hc hN.bufObj hN.heapH.1 hN.heapH.2 hN.core0 hN.devApart hN.devFree hN.devGpm
      hN.rcb hN.vsReach hM hKD hG.tot hR

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {MR : A → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 4000000 in
/-- **`dispatch_all13PUNM3` without `JUtResetHyp`** (`jUtResetHyp_of`). `dispatch_all13PUN` with `MR` at the chosen outcome (`DispPostRM`;
module docstring): the invoking and mid syscalls by the `…M` layer, the
receiving ones and `Yield` by g4b's keeps (`JDispMR.of_keep`). -/
theorem dispatch_all13PUNM4 [Fl4Proofs.P1.PlainStore st] (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hni : Entered σ) (n : I64) (c : Fl4Spec.Syscall)
    (hn : NativeSys n c) (hK : KDispHyps13PU (L := L) arI AR MR Z H Cs D s a σ n c)
    (hDL : ∀ ct, sched.cur_thread st s = ok ct → JDecMRLK (L := L) arI VtxK AR MR Z H Cs D s a σ ct)
    (hR : MR a σ.machineState) (hVI : ValidIrqMasks σ) (hN : NativeScope σ)
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR) (hIo : MRKeepIo arI MR) (hIoa : MRKeepIoapic arI MR) (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) :
    syscall.dispatch_syscall st arI s a n ⦃ r =>
      DispPostRM (L := L) arI AR MR (Fl4Spec.fl4HandleSyscall true c) σ r ⦄ := by
  have hct := cur_thread_eq (L := L) s
  have hD := dispatch_all13PUN s a σ J hni n c hn hK hR hVI hN hARI hA hnd hM hKD.toK hPA hIA hmrt hmax htu
  rcases hn with ⟨call, bl, don, hi, rfl⟩ | ⟨bl, cr, hr, rfl⟩ | ⟨rfl, rfl⟩ | hm
  · obtain ⟨hG, hE, hP, hPD⟩ := hK.inv _ call bl don hct hi
    exact dispatch_invokeJAllMUNM s a σ J _ hct n call bl don hi hG hE hP hPD
      (jDecMRL_of arI s a σ J hG hE _ hct hPD hN hM hKD hIo hIoa (jDecMRL2_ofT arI s a σ J hG hE _ hct hM hKD (jDecMRLK_ofU arI s a σ J hG hE _ hct hM hKD (hDL _ hct) (jUtResetHyp_of arI s a σ J hG hE _ hct hM hKD)))) hR hK.vmt hVI hN hARI
      hA hnd hM hKD hPA hIA hmrt
  · refine WP.spec_mono (WP.spec_and hD (JDispMR.of_keep (L := L) (AR := AR) hM
      (fun hR => dispatch_recv_mr hKD hA hr hR) ?_ hR)) fun _ ⟨h1, h2⟩ => h2 h1
    rw [fl4HandleSyscall_recv true bl cr]
    intro y hy
    obtain ⟨h1, h2⟩ := MachT.mtk_withoutPreemption (MachT.mtk_handleRecvG bl cr) y hy
    exact ⟨congrArg Prod.fst h1, h2⟩
  · refine WP.spec_mono (WP.spec_and hD (JDispMR.of_keep (L := L) (AR := AR) hM
      (fun hR => dispatch_yield_mr hKD hA hR) ?_ hR)) fun _ ⟨h1, h2⟩ => h2 h1
    have e : Fl4Spec.fl4HandleSyscall (Z := Unit) true .sysYield = Fl4Spec.withoutPreemption Fl4Spec.handleYield := rfl
    rw [e]
    intro y hy
    obtain ⟨h1, h2⟩ := MachT.mtk_withoutPreemption MachT.mtk_handleYieldG y hy
    exact ⟨congrArg Prod.fst h1, h2⟩
  · obtain ⟨rg, sr, cr, hm'⟩ := midSysR_of hm
    obtain ⟨hG, hE, hP, hW, hV, hS6, hPD⟩ := hK.mid _ rg sr cr hct hm'
    obtain ⟨hs, hq⟩ := J.midCQ hni hE
    have hS : JMidRecvHypS (L := L) arI AR (Fl4Spec.toBl (L.mem s (regA _ rg)).bv) cr σ :=
      jMidRecvHypS_of hA (jMidLeavesHyp_of2 hA (jMidLeavesHyp_of3 hA (jMidLeavesHyp_of4 hA hmax htu
        (jMidLeavesHyp_of5 hA hmax htu (jMidLeavesHyp_of6 hA hmax htu hS6)))))
    exact dispatch_midJMUNM s a σ J hni _ hct n c rg sr cr hm' hG hE hP hW.toP
      (jMidRecvHyp_of hA hG.maxTU hG.tu hs hq hW hV hS) hPD
      (jDecMRL_of arI s a σ J hG hE _ hct hPD hN hM hKD hIo hIoa (jDecMRL2_ofT arI s a σ J hG hE _ hct hM hKD (jDecMRLK_ofU arI s a σ J hG hE _ hct hM hKD (hDL _ hct) (jUtResetHyp_of arI s a σ J hG hE _ hct hM hKD)))) hR hK.vmt hVI hN hARI hA hnd hM hKD hPA hIA
      hmrt

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {MR : A → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 16000000 in
/-- **`kernel_entryJ13PUGMD3` without `JUtResetHyp`**: the dispatch by `dispatch_all13PUNM4`
(`MR` at the chosen outcome, `JDecMRL2` [W] for the loud cap kinds). -/
theorem kernel_entryJ13PUGMD4 [Fl4Proofs.P1.PlainStore st] {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap}
    {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hni : Entered σ)
    (hR : MR a σ.machineState) (hVI : ValidIrqMasks σ) (hNS0 : NativeScope σ) (n : I64) (c : Fl4Spec.Syscall)
    (hn : NativeSys n c)
    (hflag : ∀ ct v, sched.cur_thread st s = ok ct → obj.Tcb.flags st ct (L.wr s (regA ct layout.reg.FAULT_IP) v)
      ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄)
    (hB : ∀ x, σ.kheap σ.curThread = some (.tcb x) → KBudgetB arI a (faultIPSt σ σ.curThread x))
    (hK : ∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64)
      (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
        JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
        KDispHyps13PU (L := L) arI AR MR (Z.mv Z.G V') H Cs D' s' a' σb n c)
    (hDL : ∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64)
      (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
        JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
        ∀ ct', sched.cur_thread st s' = ok ct' → JDecMRLK (L := L) arI VtxK AR MR (Z.mv Z.G V') H Cs D' s' a' σb ct')
    (hFin : ∀ x ∈ (specFront c σ).1, ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64)
      (D' : Set U64) (s' : S) (a' : A), KFrontF (L := L) arI n s a s' a' →
        JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 →
        KFinAtR (L := L) arI AR Z' H' Cs' s' a' x.2)
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR) (hIo : MRKeepIo arI MR) (hIoa : MRKeepIoapic arI MR) (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) :
    syscall.handle_syscall_old st arI s a n ⦃ r => KPostM (L := L) arI AR MR c σ r ⦄ := by
  have hMK := hKD.toK
  have hct := cur_thread_eq (L := L) s
  generalize L.mem s (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD) = ct at hct
  obtain ⟨hcur, -⟩ := J.curEq hct
  have hctT : ct ∈ Z.T := TopSR.cur_mem J.xtop.fin.1 hcur.symm
  have hI := J.xtop.irelK J.ks J.buf
  obtain ⟨x, hk, hTR⟩ := hI.1.tcb ct hctT
  have hxs := hI.1.toE.at_tcb hctT hk
  have hk' : σ.kheap σ.curThread = some (.tcb x) := by rw [hcur]; exact hk
  -- the FaultIP write
  unfold syscall.handle_syscall_old
  rw [hct]; simp only [bind_ok]
  refine WP.spec_bind (Endp.obj.Tcb.reg.spec s ct layout.reg.NEXT_IP) ?_
  rintro nx hnx
  simp only [lift, bind_ok]
  refine WP.spec_bind (Endp.obj.Tcb.set_reg.spec s ct layout.reg.FAULT_IP _) ?_
  rintro s1 rfl
  generalize hv : core.num.U64.wrapping_sub nx 2#u64 = v
  have hvb : v.bv = x.tcbArch.tcbContext.userRegs .nextIP - 2 := by
    rw [← hv, core.num.U64.wrapping_sub_bv_eq, hnx, ← hxs.regs .nextIP, regIdx_nextIP]; rfl
  have hX2 := reg_wr_irel J.ip hI hctT hk Fl4Spec.Register.faultIP (by decide) v
  rw [regIdx_faultIP] at hX2
  obtain ⟨V0, J0⟩ := J.regWrJ hctT hk Fl4Spec.Register.faultIP v (by rw [regIdx_faultIP]; exact hX2)
  rw [regIdx_faultIP, hvb] at J0
  rw [← hcur] at J0
  have hF : ((), faultIPSt σ σ.curThread x) ∈ (Fl4Spec.fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1 := by
    rw [fl4SyscallFaultIP_eq hk']; exact Set.mem_singleton _
  have hni0 : Entered (faultIPSt σ σ.curThread x) := hni
  have hBu := hB x hk'
  -- the trap flag and the number range
  refine WP.spec_bind (hflag ct v hct) ?_
  rintro f hf
  simp only [hf, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  rw [if_neg hn.range.1, if_neg hn.range.2]
  -- budget_ok
  have hAK := hARI.toARKeep
  have hBud : syscall.budget_ok st arI (L.wr s (regA ct layout.reg.FAULT_IP) v) a ⦃ r =>
      (r.1 = true → ∃ σ', (Fl4Spec.updateTimeStamp (Z := Unit) >>= fun _ => Fl4Spec.checkBudgetRestart)
          (faultIPSt σ σ.curThread x) = ({(true, σ')}, False) ∧
        σ'.kheap = (faultIPSt σ σ.curThread x).kheap ∧ σ'.curThread = (faultIPSt σ σ.curThread x).curThread ∧
        σ'.curSc = (faultIPSt σ σ.curThread x).curSc ∧
        σ'.schedulerAction = (faultIPSt σ σ.curThread x).schedulerAction ∧
        σ'.idleThread = (faultIPSt σ σ.curThread x).idleThread ∧
        CurInv σ' ∧ OffReady σ' ∧ ∃ (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
          JAtZ (L := L) arI AR (Z.mv Z.G V0) H Cs Ac' Lst' D' r.2.1 r.2.2 σ') ∧
      (r.1 = false → ∃ z ∈ (specBudget (faultIPSt σ σ.curThread x)).1, z.1 = false ∧
        ∃ (Z' : XSets) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
          JAtZ (L := L) arI AR Z' H Cs Ac' Lst' D' r.2.1 r.2.2 z.2) ⦄ := by
    exact JAtZ.budgetOkB (σ0 := faultIPSt σ σ.curThread x) J0 hni0 hBu (SInv.ns_fl4SyscallFaultIP σ.curThread σ hNS0 _ hF) hAK hA
      hnd hmrt hmb hmax htu
  refine WP.spec_bind (WP.spec_and (spec_and_eq hBud fun _ h => h) (budget_ok_mr hM hMK hA hR _)) ?_
  rintro ⟨b, s2, a1⟩ ⟨⟨⟨hTr, hFa⟩, hbeq⟩, hMRb⟩
  cases b
  · -- the budget check stops the system call
    obtain ⟨z, hz, hz1, Z', Ac', Lst', D', J'⟩ := hFa rfl
    obtain ⟨b', σb⟩ := z
    simp only at hz1; subst hz1
    show (do
      let (s3, a2) ← (if false = true then syscall.dispatch_syscall st arI s2 a1 n else ok (s2, a1))
      syscall.finish st arI s3 a2) ⦃ r => KPostM (L := L) arI AR MR c σ r ⦄
    rw [if_neg (by decide)]
    simp only [bind_ok]
    have hx : ((.ok (), σb) : Except Unit Unit × Fl4Spec.State Unit) ∈ (specFront c σ).1 :=
      mem_specFront hF (mem_handleE_ok (mem_fl4HandleEvent hz mem_whenE_false))
    have F := hFin _ hx Z' H Cs Ac' Lst' D' s2 a1
      ⟨ct, v, false, s2, a1, hct, hbeq, Or.inl ⟨rfl, rfl, rfl⟩⟩ J'.toR
    have hMσb := (budget_mr_at (σ0 := faultIPSt σ σ.curThread x) hM hnd hz hMRb hVI).1
    exact WP.spec_mono (jat_finishJRNM s2 a1 σb J'.toR (SInvN.ns_front true c hNS0 _ hx) F.hd hnd hA F.vt hmb
      F.arch F.archNd F.fo F.sni F.send hT F.tail hmax htu hM hKD hMσb)
      fun r ⟨σ', hmem, hRJ, hM'⟩ => Or.inr ⟨σ', mem_kentry hx hmem, hRJ, hM'⟩
  · -- the system call runs
    obtain ⟨σb, he, ekh, ect, ecs, eact, eidle, hCb, hOb, Ac', Lst', D', J'⟩ := hTr rfl
    show (do
      let (s3, a2) ← (if true = true then syscall.dispatch_syscall st arI s2 a1 n else ok (s2, a1))
      syscall.finish st arI s3 a2) ⦃ r => KPostM (L := L) arI AR MR c σ r ⦄
    rw [if_pos rfl]
    have hb : (true, σb) ∈ (specBudget (faultIPSt σ σ.curThread x)).1 := by
      unfold specBudget
      rw [he]; exact Set.mem_singleton _
    have hBA : BudgetAt σ σb true := ⟨_, hF, hb⟩
    obtain ⟨hMRσb, hVIσb⟩ := budget_mr_at (σ0 := faultIPSt σ σ.curThread x) hM hnd (show (true, σb) ∈ _ by rw [he]; exact Set.mem_singleton _)
      hMRb hVI
    have hnib : Entered σb := ⟨by rw [ect, eidle]; exact hni0.1, by rw [eact]; exact hni0.2⟩
    have hNSb : NativeScope σb := SInvN.ns_of_kheap ekh (SInv.ns_fl4SyscallFaultIP σ.curThread σ hNS0 _ hF)
    have hfr : KFrontB (L := L) arI s a s2 a1 := ⟨ct, v, hct, hbeq⟩
    refine WP.spec_bind (spec_and_eq (dispatch_all13PUNM4 s2 a1 σb J' hnib n c hn
      (hK σb hBA V0 _ _ _ s2 a1 hfr J') (hDL σb hBA V0 _ _ _ s2 a1 hfr J') hMRσb hVIσb hNSb hARI hA hnd hM hKD hIo hIoa hPA hIA
      hmrt hmax htu)
      fun _ h => h) ?_
    rintro ⟨s3, a2⟩ ⟨hDMp, hdeq⟩
    obtain ⟨y, hy, ⟨hy1, hR, hJ, hMy⟩ | ⟨hy1, hQ⟩⟩ := hDMp
    · obtain ⟨Zm, Hm, Csm, Acm, Lstm, Dm, JmR⟩ := hJ
      obtain ⟨u, σm⟩ := y
      simp only at hy1; subst hy1
      have hx : ((.ok (), σm) : Except Unit Unit × Fl4Spec.State Unit) ∈ (specFront c σ).1 :=
        mem_specFront hF (mem_handleE_ok (mem_fl4HandleEvent hb (mem_whenE_true hy)))
      have F := hFin _ hx Zm Hm Csm Acm Lstm Dm s3 a2
        ⟨ct, v, true, s2, a1, hct, hbeq, Or.inr ⟨rfl, hdeq⟩⟩ JmR
      exact WP.spec_mono (jat_finishJRNM s3 a2 σm JmR (SInvN.ns_front true c hNS0 _ hx) F.hd hnd hA F.vt hmb
        F.arch F.archNd F.fo F.sni F.send hT F.tail hmax htu hM hKD hMy)
        fun r ⟨σ', hmem, hRJ, hM'⟩ => Or.inr ⟨σ', mem_kentry hx hmem, hRJ, hM'⟩
    · obtain ⟨u, σ1⟩ := y
      simp only at hy1; subst hy1
      have hPA : PreemptedAt c σ σ1 := ⟨σb, hBA, hy⟩
      refine WP.spec_mono (kPreFinAtGM (r := (s3, a2))
        (fun x hx Z' H' Cs' Ac' Lst' D' J' =>
          hFin x hx Z' H' Cs' Ac' Lst' D' s3 a2 ⟨ct, v, true, s2, a1, hct, hbeq, Or.inr ⟨rfl, hdeq⟩⟩ J')
        hA hnd hmb hNS0 hT hmax htu hM hKD σ1 hPA hQ) ?_
      rintro r (hfail | ⟨z, hz, σ', hmem, hRJ, hM'⟩)
      · exact Or.inl (fail_kentry hF hb hy hfail)
      · have hx : ((.ok z.1, z.2) : Except Unit Unit × Fl4Spec.State Unit) ∈ (specFront c σ).1 :=
          mem_specFront hF (mem_handleE_err (mem_fl4HandleEvent hb (mem_whenE_true hy)) (mem_liftE hz))
        exact Or.inr ⟨σ', mem_kentry hx hmem, hRJ, hM'⟩

end

/-! ## The tops -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {MR : A → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 4000000 in
/-- **The newest top** (module docstring): `kernel_entryJ40` with `hDL : JDecMRLK VtxK` only
(`JUtResetHyp` [W] proved, `jUtResetHyp_of`). As J40: `kernel_entryJ39` with `hDL` narrowed
from `JDecMRL2` (Thread, Untyped) to `JDecMRLK LoudT` (Untyped, Thread at
SetEPTRoot); as J39: `kernel_entryJ37` without `hDM`
(`JDispMRI` [W]): `MR` at the chosen outcome (`KPostXM`) carried through the
dispatch; in its place the narrower `hDL` [W] (`JDecMRL2`: the loud cap
kinds' decode with `MR`, at the dispatch states). Every other premise as
J36 / J37. -/
theorem kernel_entryJ41 [Fl4Proofs.P1.PlainStore st] {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap}
    {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hct : σ.curThread ≠ σ.idleThread)
    (hR : MR a σ.machineState) (hX : SInvX σ)
    (n : I64) (c : Fl4Spec.Syscall)
    (hn : NativeSys n c)
    (hflag : ∀ ct v, sched.cur_thread st s = ok ct → obj.Tcb.flags st ct (L.wr s (regA ct layout.reg.FAULT_IP) v)
      ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄)
    (hK : ∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64)
      (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
        JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
        KDispHypsKV35 (L := L) arI AR MR (Z.mv Z.G V') H Cs D' s' a' σb n c)
    (hDL : ∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64)
      (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
        JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
        ∀ ct', sched.cur_thread st s' = ok ct' → JDecMRLK (L := L) arI VtxK AR MR (Z.mv Z.G V') H Cs D' s' a' σb ct')
    (hFin : ∀ x ∈ (specFront c σ).1, ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64)
      (D' : Set U64) (s' : S) (a' : A), KFrontF (L := L) arI n s a s' a' →
        JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 →
        KFinAtR31 (L := L) arI AR Z' H' Cs' s' a' x.2)
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR) (hIo : MRKeepIo arI MR) (hIoa : MRKeepIoapic arI MR) (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hPI : PortInVal arI)
    (hFast : n = fl4_abi.syscall.SysReplyRecv →
      FastRR (L := L) (arI := arI) s a n (fun r => KPostM (L := L) arI AR MR c σ r)) :
    syscall.handle_syscall st arI s a n ⦃ r => KPostXM (L := L) arI AR MR c σ r ⦄ := by
  have hni := hX.entered hct
  have hS := hX.sb
  have hE := hX.epQAll
  have hQ := hX.ctQ
  have hB : ∀ x, σ.kheap σ.curThread = some (.tcb x) → OffReady (faultIPSt σ σ.curThread x) :=
    fun _ _ => offReady_faultIPSt hX.offReady
  have hC : CurInv σ := J.cur.resolve_left (by rw [hni.2]; intro e; cases e)
  have hG : syscall.handle_syscall_old st arI s a n ⦃ r => KPostM (L := L) arI AR MR c σ r ⦄ :=
    kernel_entryJ13PUGMD4 s a σ J hni hR hS.1.1.vim hS.1.1.ns n c hn hflag
      (fun x hk => ⟨hM.nowAgree hR hS.1.1.vmt, curInv_faultIPSt hk hC, hB x hk, Or.inr hQ⟩)
      (fun σb hBA V' Ac' Lst' D' s' a' hfr J' =>
        ((((((((hK σb hBA V' Ac' Lst' D' s' a' hfr J').to33 J'
          (jEntryGlobM32_of _ hARI hA hnd hPA hT hmax htu hRef hPI)).to32
          (liveDN_front hnd J J.live hS hARI.toARKeep hA hfr hBA)).to31).to27b.to27 hnd hS hni hE hBA).to26
          hnd hS hni hQ hB hBA).to25 hA hmax htu hmb J' (hBA.enteredP hnd hni)).to23 hA hmax htu).to13PU J' hBA
          hA hnd hM hKD hmax htu)
      hDL
      (fun x hx Z' H' Cs' Ac' Lst' D' s' a' hfr J' =>
        (hFin x hx Z' H' Cs' Ac' Lst' D' s' a' hfr J').to27.toR
          (fun o e => SInvAll.sinvB_front_fo true c hS hct x hx o e))
      hARI hA hnd hM hKD hIo hIoa hPA hIA hmrt hmb hT hmax htu
  have hP : syscall.handle_syscall st arI s a n ⦃ r => KPostM (L := L) arI AR MR c σ r ⦄ := by
    by_cases hrr : n = fl4_abi.syscall.SysReplyRecv
    · exact P1.FastAgree.spec st arI (P1.FastAgree.of_acc st arI P1.LawfulStore.total hA
        (FastRR.acc hflag hn.range hrr (hFast hrr))) hG
    · rw [handle_syscall_eq_general_of hflag hn.range hrr, P1.handle_syscall_general_eq]; exact hG
  refine WP.spec_mono hP ?_
  rintro r (hF | ⟨σ', hy, hRJ, hM'⟩)
  · exact Or.inl hF
  · exact Or.inr ⟨σ', hy, hRJ, hM', kentry_sinvX hnd c hX hct _ hy⟩

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 4000000 in
/-- **`kernel_entry_reachMD3` without `JUtResetHyp`** (by `kernel_entryJ41`): no `JDispMR` input; the
per-state premises are g4a's (`hflag`, `hK`, `hFin`, `hFast` for `KPostM`)
and `hDL` [W] (`JDecMRL2` at the dispatch states). -/
theorem kernel_entry_reachMD4 [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR) (hIo : MRKeepIo arI MR) (hIoa : MRKeepIoapic arI MR) (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hPI : PortInVal arI)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hJ : JReachM (L := L) arI AR MR s a σ) :
    ∃ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ ∧ SInvX σ ∧ MR a σ.machineState ∧
      ∀ (n : I64) (c : Fl4Spec.Syscall), σ.curThread ≠ σ.idleThread → NativeSys n c →
      (∀ ct v, sched.cur_thread st s = ok ct → obj.Tcb.flags st ct (L.wr s (regA ct layout.reg.FAULT_IP) v)
        ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄) →
      (∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64)
        (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
          JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
          KDispHypsKV35 (L := L) arI AR MR (Z.mv Z.G V') H Cs D' s' a' σb n c) →
      (∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64)
        (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
          JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
          ∀ ct', sched.cur_thread st s' = ok ct' → JDecMRLK (L := L) arI VtxK AR MR (Z.mv Z.G V') H Cs D' s' a' σb ct') →
      (∀ x ∈ (specFront c σ).1, ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64)
        (D' : Set U64) (s' : S) (a' : A), KFrontF (L := L) arI n s a s' a' →
          JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 →
          KFinAtR31 (L := L) arI AR Z' H' Cs' s' a' x.2) →
      (n = fl4_abi.syscall.SysReplyRecv →
        FastRR (L := L) (arI := arI) s a n (fun r => KPostM (L := L) arI AR MR c σ r)) →
      syscall.handle_syscall st arI s a n ⦃ r => (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).2 ∨
        ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          JReachM (L := L) arI AR MR r.1 r.2 σ' ⦄ := by
  obtain ⟨⟨Z, H, Cs, Ac, Lst, D, J⟩, hX, hR⟩ := jreach_invM hnd hJ
  refine ⟨Z, H, Cs, Ac, Lst, D, J, hX, hR, fun n c hct hn hflag hK hDL hFin hFast => ?_⟩
  have hE := kernel_entryJ41 (MR := MR) s a σ J hct hR hX n c hn hflag hK hDL hFin hARI hA hnd hM hKD hIo hIoa hPA hIA
    hmrt hmb hT hmax htu hRef hPI hFast
  obtain ⟨⟨s', a'⟩, hv, hP⟩ := spec_exists hE
  rw [hv, WP.spec_ok]
  rcases hP with hF | ⟨σ', hy, hRJ, hM', hX'⟩
  · exact Or.inl hF
  · exact Or.inr ⟨σ', hy, hRJ, hX', hM', JReachM.step n c hJ hct hn hv hy ⟨hRJ, hM'⟩⟩

end
end

end Fl4Proofs.P3
