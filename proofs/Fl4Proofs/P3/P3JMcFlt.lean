/-
P3 (p3J gen 27): **the fault entries' footprint composed along P3's joint chain** — the user-exception and VM-fault
entries write only `ProjW H Cs s` from every `CKI ∧ RR` `JAtZ` entry state (stage A; stage Q and the tops in
P3JMcFltQ).

* **Glue** (namespace `Mc`): `ipcWN_projW` (P2's `IpcWN … ∅` words over `H`'s sets are `ProjW` words: `KWN`,
  the TCBs' user context, cap-slot and debug words); `noBufCap_cki` (at a `CKI` `JAtZ` state no TCB of `H` has a
  frame cap in its IPC-buffer slot: P3JMcBuf's argument, `StateRel.bufCap` + `CKI`); `bufApart_blk` (the
  buffer-slot words are no `KW` words, P1's `capw_not_kw` from `BlkOK`).
* **`faultProjW`**: at a `CKI` `JAtZ` state whose current thread is entered and not queued, FL4's `handle_fault` of
  the current thread writes only `ProjW`. P3JFltX's `handle_fault.footNB` with `sE := s` (`BufK.refl`), P1's sets
  of `H`, `CanBlock` by `JAtZ.canBlockCur`, the fault-handler cap typed by `JAtZ.timeoutTyped`, `XG` at the guard
  `P3Ok := True` (trivially, from `s` itself). This is the gen 23 "intermediate-state" gap closed: the transfer's
  buffer fact is carried from the entry of `handle_fault` by `BufK` along P2's `RS`, not asked at every `XG` state.
* **`budOk_projW_rr`**: `syscall.budget_ok` (update_timestamp, `check_budget`, the restart) writes only `ProjW`
  at an `RR` `JAtZ` state with action resume (P3JMcIrqR's `budFoot_rr` argument, keeping P2's `BXI` after the
  check for the restart's `set_thread_state`).
* **`jEvRef_fltFt`**: StPostEv's `jEvRef_fltSt` re-run with the footprint as post (same leaves `budgetOkB` /
  `budgetOkBSt`, the branch's `JFltHypSt` for the post-branch `JStab`): budget by `budOk_projW_rr`, the branch by
  a given footprint at the post-budget `JAtZ` (`CKI` there: `specBudget` keeps the heap), the finish by
  `finFootJ_holds` (`CKI` of the event's outcome: `ck_handleEvent_other`). No `KFinEv` (`hFin`) needed.
* `brU_projW`, `brV_projW`: the user / VM-fault branches by `faultProjW`; **`jEvRef_userFt`**, **`jEvRef_vmfFt`**.

No premise beyond the stated hypotheses (all already globals of the clause tops); no sorry. New module; no existing
statement changed.
-/
import Fl4Proofs.P3.P3JFltX
import Fl4Proofs.P3.P3JMcFin
import Fl4Proofs.P3.P3JStEv
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Mc
open fl4_core Classical Fl4Spec Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.G5 Fl4Proofs.P3.Vs Fl4Proofs.P3.JBootQ

/-! ## Glue -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]
variable {H : P1.Heap} {Cs : Set U64}

/-- P2's `IpcWN … ∅` words over `H`'s sets are `ProjW` words. -/
theorem ipcWN_projW (hH : P1.HeapOK H) {s : S} (hNP : ∀ c ∈ Cs, NodePlaced st (P1.Heap.tcbs H) s c) {b : U64}
    (hb : IpcWN st ∅ False (P1.Heap.tcbs H) Cs (P1.Heap.omega H) (P1.Heap.frame H) (P1.Heap.scs H)
      (P1.Heap.scBits H) (EH H) ∅ s b) : ProjW (L := L) H Cs s b := by
  obtain ⟨hw, hi⟩ := hb
  rcases hw with hk | hx | ⟨hc, -⟩ | hd
  · exact kwN_projW hH hNP (Kp := ∅) (Nd := False) ⟨hk, hi⟩
  · rcases hx with ⟨y, hy, K, hK, -, rfl⟩ | hu
    · exact obj_projW hH (k := .tcb) hy (by simp only [P1.HKind.bits]; omega)
    · exact absurd hu (Set.notMem_empty _)
  · exact capW_projW hH hc
  · exact dbgW_projW hH hNP hd

/-- The buffer-slot words are no `KW` words at a `BlkOK` state. -/
theorem bufApart_blk {T Cs Ω : Set U64} {Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64} {s : S}
    (h : P1.BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) : P1.BufApart (L := L) T Cs Sg Scs Z (EH H) s := by
  have hT := h.1.choose_spec.choose_spec.tcbs
  intro y hy b hb
  have hw : P1.CapW T Ω Sg b ∧ P1.Aligned b := by
    rcases hb with rfl | rfl
    · rw [P1.sbWordA_eq]
      exact ⟨Or.inl ⟨y, hy, 64#u64, by simp, rfl⟩, P1.field_aligned (hT y hy) (by simp) (by simp)⟩
    · rw [P1.sbWordA8_eq]
      exact ⟨Or.inl ⟨y, hy, 72#u64, by simp, rfl⟩, P1.field_aligned (hT y hy) (by simp) (by simp)⟩
  exact ⟨hw.2, fun hk => P1.capw_not_kw h hw.1 hw.2 le_rfl (by omega) hk⟩

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
  {AR : A → Fl4Spec.Cr3 → Prop}
variable {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A}
  {σ : Fl4Spec.State Unit}

/-- **At a `CKI` `JAtZ` state no TCB of `H` has a frame cap in its IPC-buffer slot.** -/
theorem noBufCap_cki (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hC : SInvCk.CKI σ) :
    P1.NoBufCap (L := L) (P1.Heap.tcbs H) s := by
  intro t ht
  have htT : Z.th t = some .tcb := J.thTcb (by rw [J.tcbs_eq.1]; exact ht)
  obtain ⟨x, c, hkx, hc, hca⟩ := J.xtop.rel.2.1.1.bufCap htT
  have hco : capOpt (σ.kheap t.bv) (Fl4Spec.tcbCnodeIndex 2) = some x.tcbIpcframe := by
    simp only [capOpt, hkx]; exact Endp.tcbCnodeMap_two x
  have hk := hC _ _ _ hco
  rw [← hca.2] at hk
  have e : slotOf t 2 = P1.sbWordA t := by
    have h2 : obj.Tcb.slot t layout.tcb.SLOT_BUFFER = ok (P1.sbWordA t) := by
      simp [obj.Tcb.slot, lift, P1.sbWordA]
    exact ok_inj_ff ((Endp.tcb_slot_buffer t).symm.trans h2)
  rw [e] at hc
  refine ⟨c, hc, ?_⟩
  cases c <;> first | exact True.intro | (exfalso; simp [absCap, SInvCk.KW] at hk)

set_option maxHeartbeats 4000000 in
/-- **`handle_fault` of the current thread writes only `ProjW`** at a `CKI` `JAtZ` state (module docstring). -/
theorem faultProjW (hA : P0.ArchTotal arI) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (hC : SInvCk.CKI σ) (hni : Entered σ) (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p) {ct : U64}
    (hct : sched.cur_thread st s = ok ct) (f : error.Fault) :
    faults.handle_fault st arI s a ct f ⦃ r => P1.WritesIn st s r.1 (ProjW (L := L) H Cs s) ⦄ := by
  obtain ⟨hcur, x, hk, hrn⟩ := J.curRunnable hni hct
  have hctT : ct ∈ Z.T := TopSR.cur_mem J.xtop.fin.1 hcur.symm
  have htcb : Z.th ct = some .tcb := J.thTcb hctT
  have hcb := J.canBlockCur hctT hcur hk hrn hni hnq
  have hblk := J.blk
  obtain ⟨Q, R, hq⟩ := hblk.1
  have hcap : obj.Tcb.slot ct layout.tcb.SLOT_FAULT_HANDLER ⦃ sl => obj.Slot.cap st sl s ⦃ c =>
      P1.CapTyped H (P1.Heap.replies H) (P1.Heap.ntfns H) c ⦄ ⦄ := by
    have e : obj.Tcb.slot ct layout.tcb.SLOT_FAULT_HANDLER = ok (slotOf ct 3) := by
      unfold obj.Tcb.slot layout.tcb.SLOT_FAULT_HANDLER layout.cte.SIZE
      simp only [lift, bind_ok]
      congr 1
    rw [e, WP.spec_ok]
    exact J.timeoutTyped ⟨ct, 3, Or.inr ⟨htcb, by decide⟩, rfl⟩
  have hG : P1.XG st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.scs H)
      (P1.Heap.scBits H) (fun _ => True) s :=
    ⟨s, ⟨s, trivial, P1.WritesIn.refl _ _⟩, P1.WritesIn.refl _ _⟩
  refine WP.spec_mono (P1.faults.handle_fault.footNB hA (noBufCap_cki J hC) (bufApart_blk hblk) s a ct f hblk hcb
    hcap (P1.BufK.refl s) hG) ?_
  rintro ⟨s', a'⟩ hF
  try simp only [WP.uncurry'_pair] at hF
  exact (Fl4Proofs.P1.WritesA.w hF).mono fun b hb => ipcWN_projW J.kern.heap hq.nodes hb

set_option maxHeartbeats 4000000 in
/-- **On a round-robin run `budget_ok` writes only `ProjW`** (module docstring). -/
theorem budOk_projW_rr (hA : P0.ArchTotal arI) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (hres : σ.schedulerAction = .resumeCurThread) (hRR : SInvRr.RR σ) :
    syscall.budget_ok st arI s a ⦃ r => P1.WritesIn st s r.2.1 (ProjW (L := L) H Cs s) ⦄ := by
  have hI := J.entryInv hres
  have hI' := hI
  obtain ⟨⟨Q0, R0, h0⟩, -, hX0, -, -, -, -, -⟩ := hI'
  unfold syscall.budget_ok
  refine WP.spec_bind (WP.spec_and (WP.spec_and (sched.update_timestamp.entry hA s a hI)
    (sched.update_timestamp.fr hA s a (h0.nodes _ h0.cur)))
    (sched.update_timestamp.kwN (Kp := ∅) (Nd := False) (T := P1.Heap.tcbs H) (Sg := P1.Heap.frame H)
      (Scs := P1.Heap.scs H) (Z := P1.Heap.scBits H) (Es := EH H) hA s a h0.nodes h0.cur)) ?_
  rintro ⟨s1, a1⟩ ⟨⟨U1, U2⟩, f1⟩
  try simp only [WP.uncurry'_pair] at U1 U2 f1
  obtain ⟨⟨⟨Q1, R1, hq1⟩, hB1, hX1, hSg1, hS1⟩, ecs1, hcA1, hna1, hcsc1, -⟩ := U1
  have F1 : P1.WritesIn st s s1 (ProjW (L := L) H Cs s) :=
    projW_of_cur0wN J ((Fl4Proofs.P1.WritesA.w f1).mono fun _ hb => Or.inl hb)
  -- the spec period of the current SC is `0`, so is FL4's (P3JMcIrqR's `budFoot_rr`)
  have hC : CurInv σ := J.curInv (by rw [hres]; intro e; cases e)
  have hS := J.xtop.fin.1.1.1
  obtain ⟨Q, R0', hc, hs⟩ := hS.lists
  obtain ⟨hscC, -, -, -, -, -, -⟩ := CurInv.facts hS J.inv hC
  have ecsc : L.cscW s = nodeW st s Z.c layout.node.CUR_SC := by
    show L.mem s (L.nodeAt s (L.cpu s) _) = _; rw [hc.cur]; rfl
  obtain ⟨x, n, hk, hx⟩ := hs.scs _ hscC
  have hx0 : x.scPeriod = 0 := SInvRr.rr_period hRR hk
  have hp0 : L.rperiod s (L.cscW s) = 0#u64 := by
    rw [ecsc]; exact P1.eq_of_bv (by rw [← hx.period, hx0]; rfl)
  have hcS : L.cscW s ∈ P1.Heap.scs H := hX0.2.2.cur
  obtain ⟨hP, hz⟩ := hX0.1.sc _ hcS
  obtain ⟨h8c, h128, -⟩ := sc_lo hP hz
  have hpz : layout.sc.PERIOD.val = 0 := by simp [layout.sc.PERIOD]
  have hpv : (periodA (L.cscW s)).val = (L.cscW s).val := by
    unfold periodA; rw [sc_word_val (o := layout.sc.PERIOD) hP hz (by rw [hpz]; omega), hpz, Nat.add_zero]
  have hal : Aligned (periodA (L.cscW s)) := by unfold Aligned; rw [hpv]; exact h8c
  have hpin : InSC (L.cscW s) (P1.Heap.scBits H (L.cscW s)) (periodA (L.cscW s)) := ⟨by omega, by omega⟩
  have hp1 : L.rperiod s1 (L.cscW s1) = 0#u64 := by
    rw [ecs1, ← hp0]
    unfold LawfulStore.rperiod
    refine U2.mem_eq hal ?_
    rintro ⟨o, -, ho, -, e⟩
    exact out_ne_node (h0.omega _ (hX0.1.scW _ hcS _ hal hpin)) h0.cur (h0.nodes _ h0.cur) ho
      (congrArg UScalar.val e).symm
  unfold sched.check_budget_restart
  refine WP.spec_bind (Fl4Proofs.P2.Stall.sched.check_budget.rr (Kp := ∅) (Nd := False) (Es := (∅ : Set U64)) hA s1 a1 Q1 R1 hq1
    hB1 hX1 hSg1 hS1 hcsc1 hna1 hcA1 (fun _ h => h) (fun _ _ _ => ⟨hp1, fun h => h⟩)) ?_
  rintro ⟨b, s2, a2⟩ hr
  try simp only [WP.uncurry'_pair] at hr
  obtain ⟨⟨⟨Q2, R2, hq2⟩, -, -, -, -⟩, F, -, -⟩ := hr
  have F2 : P1.WritesIn st s s2 (ProjW (L := L) H Cs s) :=
    F1.projW_trans ((Fl4Proofs.P1.WritesA.w F).mono fun _ hb => cur0wN_projW J.kern.heap hq1.nodes (Or.inl hb))
  try simp only [uncurry_apply_pair]
  rw [Fl4Proofs.P1.cur_thread_ok]; simp only [bind_ok]
  split
  · exact (WP.spec_ok _).2 F2
  · refine WP.spec_bind (P0.sched.is_runnable.p0 st s2 _ L.total) fun rb _ => ?_
    split
    · refine WP.spec_bind (Fl4Proofs.P2.Stall.sched.set_thread_state.kwNP (Kp := ∅) (Nd := False)
        (Sg := P1.Heap.frame H) (Scs := P1.Heap.scs H) (Z := P1.Heap.scBits H) (Es := EH H) s2 _ _ hq2.tcbs
        hq2.nodes hq2.cur hq2.curT (Set.notMem_empty _)) fun s3 f3 => ?_
      exact (WP.spec_ok _).2 (F2.projW_trans ((Fl4Proofs.P1.WritesA.w f3).mono fun _ hb =>
        cur0wN_projW J.kern.heap hq2.nodes (Or.inl hb)))
    · exact (WP.spec_ok _).2 F2

end

end Fl4Proofs.P3.Mc

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.G4 Fl4Proofs.P3.Mc

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop}

open Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvF in
set_option maxHeartbeats 16000000 in
/-- **`jEvRef_fltSt`'s run writes only `ProjW`** (module docstring): the branch's footprint `hBF` at the
post-budget `JAtZ`, the budget by `budOk_projW_rr`, the finish by `finFootJ_holds`. -/
theorem jEvRef_fltFt {ev : Fl4Spec.Event} {G : Fl4Spec.SMonad Unit Unit} {B : S → A → Result (S × A)}
    (hev : Fl4Spec.handleEvent (Z := Unit) ev = Fl4Spec.withoutPreemption (do
      Fl4Spec.updateTimeStamp; let restart ← Fl4Spec.checkBudgetRestart; Fl4Spec.NonDet.when restart G))
    (hsc : ∀ c, ev ≠ .syscallEvent c) (hin : ev ≠ .interrupt)
    {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64}
    {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) [VxE Z] (hX : SInvX σ) (hct : σ.curThread ≠ σ.idleThread)
    (hR : MR a σ.machineState) (hC : SInvCk.CKI σ) (hRR : SInvRr.RR σ)
    (hB : JFltHypSt (L := L) arI AR MR Z H Cs B G s a σ)
    (hBF : ∀ (σb : Fl4Spec.State Unit) (s1 : S) (a1 : A) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
      (true, σb) ∈ (specBudget σ).1 → JAtZ (L := L) arI AR Z H Cs Ac' Lst' D' s1 a1 σb → SInvCk.CKI σb →
      B s1 a1 ⦃ r => P1.WritesIn st s1 r.1 (ProjW (L := L) H Cs s1) ⦄)
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) :
    (do let (b, s1, a1) ← syscall.budget_ok st arI s a
        let (s2, a2) ← if b then B s1 a1 else ok (s1, a1)
        syscall.finish st arI s2 a2) ⦃ r => P1.WritesIn st s r.1 (ProjW (L := L) H Cs s) ⦄ := by
  have hni := hX.entered hct
  have hS := hX.sb
  have hNS : NativeScope σ := hS.1.1.ns
  have hMK := hKD.toK
  have hCI : CurInv σ := J.cur.resolve_left (by rw [hni.2]; intro e; cases e)
  have hBu : KBudgetB arI a σ := ⟨hM.nowAgree hR hS.1.1.vmt, hCI, hX.offReady, Or.inr hX.ctQ⟩
  have fin : ∀ (s2 : S) (a2 : A) (y : Fl4Spec.State Unit),
      ((.ok (), y) : Except Unit Unit × Fl4Spec.State Unit) ∈ ((Fl4Spec.handleEvent (Z := Unit) ev).run σ).1 →
      JStab (L := L) arI AR Z H Cs s2 a2 y →
      syscall.finish st arI s2 a2 ⦃ r => P1.WritesIn st s2 r.1 (ProjW (L := L) H Cs s2) ⦄ := by
    rintro s2 a2 y hE ⟨G', V', Ac', Lst', D', J'⟩
    have hCy : SInvCk.CKI y := SInvCk.ck_handleEvent_other ev hsc σ hC _ hE
    exact finFootJ_holds hA _ H Cs Ac' Lst' D' s2 a2 y J' inferInstance hCy
  refine WP.spec_bind (spec_and_eq (WP.spec_and (WP.spec_and (WP.spec_and (J.budgetOkB hni hBu hNS
    hARI.toARKeep hA hnd hmrt hmb hmax htu) (J.budgetOkBSt hni hBu hNS hARI.toARKeep hA hnd hmrt hmb hmax htu))
    (budget_ok_mr hM hMK hA hR s)) (budOk_projW_rr hA J hX.cr.2 hRR)) fun _ h => h) ?_
  rintro ⟨b, s1, a1⟩ ⟨⟨⟨⟨⟨hTr, -⟩, hFa⟩, hM1⟩, F1⟩, heq⟩
  cases b with
  | false =>
    obtain ⟨⟨b', σb⟩, hz, hz1, hJ'⟩ := hFa rfl
    simp only at hz1; subst hz1
    have hE : ((.ok (), σb) : Except Unit Unit × Fl4Spec.State Unit) ∈ ((Fl4Spec.handleEvent (Z := Unit) ev).run σ).1 := by
      rw [hev]
      obtain ⟨u, hu, hc⟩ := mem_bind_elim hz
      exact mem_liftE (x := ((), σb)) (mem_bind_nd hu (mem_bind_nd hc (mem_when_false (by simp) _ σb)))
    show (do let (s2, a2) ← (if false = true then B s1 a1 else ok (s1, a1)); syscall.finish st arI s2 a2) ⦃ _ ⦄
    rw [if_neg (by decide)]
    simp only [bind_ok]
    exact WP.spec_mono (fin s1 a1 σb hE hJ') fun r hr => F1.projW_trans hr
  | true =>
    obtain ⟨σb, he, -, -, -, -, -, -, -, Ac', Lst', D', J'⟩ := hTr rfl
    have hb : (true, σb) ∈ (specBudget σ).1 := by unfold specBudget; rw [he]; exact Set.mem_singleton _
    have hMb := (budget_mr_at hM hnd hb hM1 hS.1.1.vim).1
    have hCb : SInvCk.CKI σb := by
      obtain ⟨ek, -⟩ := specBudget_true_shape hnd hb
      intro p cref c hc; rw [ek] at hc; exact hC p cref c hc
    show (do let (s2, a2) ← (if true = true then B s1 a1 else ok (s1, a1)); syscall.finish st arI s2 a2) ⦃ _ ⦄
    rw [if_pos rfl]
    refine WP.spec_bind (spec_and_eq (WP.spec_and (hB σb s1 a1 Ac' Lst' D' hb heq J' hMb)
      (hBF σb s1 a1 Ac' Lst' D' hb J' hCb)) fun _ h => h) ?_
    rintro ⟨s2, a2⟩ ⟨⟨⟨z', hz', hJ', -⟩, F2⟩, -⟩
    have hE : ((.ok (), z'.2) : Except Unit Unit × Fl4Spec.State Unit) ∈
        ((Fl4Spec.handleEvent (Z := Unit) ev).run σ).1 := by
      rw [hev]
      obtain ⟨u, hu, hc⟩ := mem_bind_elim hb
      refine mem_liftE (x := z') (mem_bind_nd hu (mem_bind_nd hc ?_))
      show z' ∈ (Fl4Spec.NonDet.when (true = true) G σb).1
      unfold Fl4Spec.NonDet.when; rw [if_pos rfl]; exact hz'
    exact WP.spec_mono (fin s2 a2 z'.2 hE hJ') fun r hr => (F1.projW_trans F2).projW_trans hr

set_option maxHeartbeats 4000000 in
/-- The user-exception branch writes only `ProjW` at the post-budget `JAtZ` (`faultProjW`). -/
theorem brU_projW (hnd : Fl4Spec.numDomains = 1) (hA : P0.ArchTotal arI) {Z : XSets} {H : P1.Heap}
    {Cs : Set U64} {σ : Fl4Spec.State Unit} (hX : SInvX σ) (hct : σ.curThread ≠ σ.idleThread) (n c : U64) :
    ∀ (σb : Fl4Spec.State Unit) (s1 : S) (a1 : A) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
      (true, σb) ∈ (specBudget σ).1 → JAtZ (L := L) arI AR Z H Cs Ac' Lst' D' s1 a1 σb → SInvCk.CKI σb →
      brU (st := st) arI n c s1 a1 ⦃ r => P1.WritesIn st s1 r.1 (ProjW (L := L) H Cs s1) ⦄ := by
  intro σb s1 a1 Ac' Lst' D' hb J1 hC1
  obtain ⟨hni1, hnq1, -, -, -, -⟩ := budget_true_facts hnd hX hct hb
  obtain ⟨ct, hct1, -⟩ := spec_exists (sched.cur_thread.spec' (L := L) s1)
  show (do let t ← sched.cur_thread st s1; faults.handle_fault st arI s1 a1 t (.UserException n c)) ⦃ _ ⦄
  rw [hct1, bind_ok]
  exact faultProjW hA J1 hC1 hni1 hnq1 hct1 _

set_option maxHeartbeats 4000000 in
/-- The VM-fault branch writes only `ProjW` at the post-budget `JAtZ` (`faultProjW`). -/
theorem brV_projW (hnd : Fl4Spec.numDomains = 1) (hA : P0.ArchTotal arI) {Z : XSets} {H : P1.Heap}
    {Cs : Set U64} {σ : Fl4Spec.State Unit} (hX : SInvX σ) (hct : σ.curThread ≠ σ.idleThread) (ad c : U64) :
    ∀ (σb : Fl4Spec.State Unit) (s1 : S) (a1 : A) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
      (true, σb) ∈ (specBudget σ).1 → JAtZ (L := L) arI AR Z H Cs Ac' Lst' D' s1 a1 σb → SInvCk.CKI σb →
      brV (st := st) arI ad c s1 a1 ⦃ r => P1.WritesIn st s1 r.1 (ProjW (L := L) H Cs s1) ⦄ := by
  intro σb s1 a1 Ac' Lst' D' hb J1 hC1
  obtain ⟨hni1, hnq1, -, -, -, -⟩ := budget_true_facts hnd hX hct hb
  obtain ⟨ct, hct1, -⟩ := spec_exists (sched.cur_thread.spec' (L := L) s1)
  show (do
      let t ← sched.cur_thread st s1
      let i ← c >>> 4#i32
      let i1 ← lift (i &&& 1#u64)
      let f ← vspace.vm_fault ad c (i1 != 0#u64)
      faults.handle_fault st arI s1 a1 t f) ⦃ _ ⦄
  rw [hct1, bind_ok, shr_eq c 4#i32 (by decide) (by decide), bind_ok]
  simp only [lift, bind_ok, vspace.vm_fault]
  exact faultProjW hA J1 hC1 hni1 hnq1 hct1 _

set_option maxHeartbeats 8000000 in
/-- **The user-exception entry writes only `ProjW`** from a `CKI ∧ RR` `JAtZ` state (module docstring). -/
theorem jEvRef_userFt {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64}
    {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) [VxE Z] (hX : SInvX σ) (hct : σ.curThread ≠ σ.idleThread)
    (hR : MR a σ.machineState) (hC : SInvCk.CKI σ) (hRR : SInvRr.RR σ) (n c : U64) (hU : UserHw n c)
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) :
    syscall.handle_user_exception st arI s a n c ⦃ r => P1.WritesIn st s r.1 (ProjW (L := L) H Cs s) ⦄ :=
  jEvRef_fltFt (ev := .userLevelFault n.bv c.bv) (G := brUS n c) (B := brU (st := st) arI n c) rfl
    (fun _ h => by cases h) (fun h => by cases h) J hX hct hR hC hRR (jFltHyp_userSt hnd hM hKD hA hX hct n c hU)
    (brU_projW hnd hA hX hct n c) hARI hA hnd hM hKD hmrt hmb hmax htu

set_option maxHeartbeats 8000000 in
/-- **The VM-fault entry writes only `ProjW`** from a `CKI ∧ RR` `JAtZ` state (module docstring). -/
theorem jEvRef_vmfFt {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64}
    {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) [VxE Z] (hX : SInvX σ) (hct : σ.curThread ≠ σ.idleThread)
    (hR : MR a σ.machineState) (hC : SInvCk.CKI σ) (hRR : SInvRr.RR σ) (ad c : U64) (ft : Fl4Spec.VMFaultType)
    (hV : VmfHw ad c ft σ)
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) :
    syscall.handle_vm_fault st arI s a ad c ⦃ r => P1.WritesIn st s r.1 (ProjW (L := L) H Cs s) ⦄ :=
  jEvRef_fltFt (ev := .vmFaultEvent ft) (G := brVS ft) (B := brV (st := st) arI ad c) rfl (fun _ h => by cases h)
    (fun h => by cases h) J hX hct hR hC hRR (jFltHyp_vmfSt hnd hM hKD hA hX hct ad c ft hV)
    (brV_projW hnd hA hX hct ad c) hARI hA hnd hM hKD hmrt hmb hmax htu

end

end

end Fl4Proofs.P3
