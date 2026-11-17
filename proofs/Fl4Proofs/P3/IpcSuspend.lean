/-
P3 (DESIGN.md §9), TCB invocations: **Suspend on `IRel`** (`sched::suspend`
against l4v `suspend`), and its leaf at `XTop` (XTopTcbSched's
`SuspendXLeaf`).

`cancel_ipc` (`cancel_ipc_irel`), the restart PC of a running thread
(`reg_wr_irel`: XTopTcbSched's register write at `IRel`), the scheduler
queues (`dequeue_refines`, `release_remove_refines`, lifted by
`sc_step_lift`), the yield-to pair cut (`cancel_yield_to_irel`, lifted by
`tk_liftCW`), then the thread `Inactive`.
-/
import Fl4Proofs.P3.IpcRemoveTcb
import Fl4Proofs.P3.IpcSetPrioX
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open Fl4Spec

noncomputable section

theorem nkt_schedContextCancelYieldTo (t : ObjRef) : NKT (schedContextCancelYieldTo (Z := Unit) t) := by
  unfold schedContextCancelYieldTo getTcbObjRef setScObjRef setTcbObjRef
  repeat' (first | nkt_step | (unfold NonDet.when; split) | split)

theorem nks_tcbReleaseRemove (t : ObjRef) : Ipc.NKS (tcbReleaseRemove (Z := Unit) t) := by
  unfold tcbReleaseRemove
  repeat' (first | nks_step | (unfold NonDet.when; split) | split)

end

end Fl4Proofs.P3.Sched

namespace Fl4Proofs.P3.Ipc
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

set_option maxHeartbeats 8000000 in
/-- **`IRel` across a register write** of a TCB's saved context (not the
badge register): XTopTcbSched's `XTopAt.regWr` at `IRel`. -/
theorem reg_wr_irel (hP0 : IPlaced N T E R B) {s : S} {σ : Fl4Spec.State Unit}
    (hX : IRel st th cr N T C E R B c s σ) {t : U64} (ht : t ∈ T) {x : Fl4Spec.Tcb}
    (hk : σ.kheap t.bv = some (.tcb x)) (r : Fl4Spec.Register) (hr : r ≠ Fl4Spec.badge_register) (v : U64) :
    IRel st th cr N T C E R B c (L.wr s (regA t (regIdx r)) v) (Notif.updK σ t.bv (.tcb (Notif.setReg x r v.bv))) := by
  obtain ⟨hIR, hSRT⟩ := hX
  have hPe := hP0.e
  have hSch := hSRT.2.1
  obtain ⟨Q, R0, hc, -⟩ := hSch.lists
  have hT := hc.tcbs
  have hta := hT t ht
  obtain ⟨hR1, hW1, hS1⟩ := write_reg_rel hPe s σ hIR.toE ht hk r v
  have hSRT' : SRT st th cr N T C E R B c (SRE st N T C E R B c)
      (L.wr s (regA t (regIdx r)) v) (Notif.updK σ t.bv (.tcb (Notif.setReg x r v.bv))) :=
    ⟨hSRT.1.stableE hW1 hS1, hSRT.2.1.stableE hPe hSRT.2.2 hW1 hS1, hSRT.2.2.mono hW1.1 (SzKeep.epStep hS1)⟩
  have hwv := regA_val hta (regIdx_lt r)
  have hil := regIdx_lt r
  have hwa : P1.Aligned (regA t (regIdx r)) := by unfold P1.Aligned; rw [hwv]; have := hta.align; omega
  have hw : P1.WritesIn st s (L.wr s (regA t (regIdx r)) v) (· = regA t (regIdx r)) := P1.writesIn_wr hwa
  have hbne : (regA t (regIdx r)).val ≠ (regA t (regIdx Fl4Spec.badge_register)).val := regA_ne hta hr
  have hNt' : Notif.NtfnStateRel N T (L.mem (L.wr s (regA t (regIdx r)) v))
      (Notif.updK σ t.bv (.tcb (Notif.setReg x r v.bv))) := by
    refine hIR.toN.frame hSch.placed (fun b hb hf => hw.mem_eq hb fun e => ?_) ⟨fun q y hq => ?_, fun q y hq => ?_⟩
    · subst e
      rcases hf with ⟨n, hn, h1, h2⟩ | ⟨y, hy, h⟩
      · have := hSch.placed.disj n hn t ht; omega
      · by_cases e : y = t
        · subst e
          have hv := nfootT_val hta h
          have hb0 := regA_val hta (regIdx_lt Fl4Spec.badge_register)
          have hbi : (regIdx Fl4Spec.badge_register).val = 0 := rfl
          omega
        · have hv := nfootT_val (hT y hy) h
          have := tcb_disj hPe ht hy e; omega
    · by_cases e : q = t.bv
      · subst e; rw [hk] at hq; cases hq
      · simp only [Notif.updK, Function.update_of_ne e]; exact hq
    · by_cases e : q = t.bv
      · subst e; rw [hk] at hq; cases hq
        refine ⟨Notif.setReg x r v.bv, by simp [Notif.updK], rfl, ?_, rfl⟩
        unfold Notif.badgeOf
        rw [Notif.setReg_regs, Function.update_of_ne (Ne.symm hr)]
      · exact ⟨y, by simp only [Notif.updK, Function.update_of_ne e]; exact hq, rfl, rfl, rfl⟩
  exact ⟨IpcRel.of hNt' hR1 (sched_sc hSRT'.2.1), hSRT'⟩

/-- The spec's `update_restart_pc`: the fault register set to the next IP. -/
theorem updateRestartPc_eq {σ : Fl4Spec.State Unit} {t : Fl4Spec.ObjRef} {x : Fl4Spec.Tcb}
    (hk : σ.kheap t = some (.tcb x)) :
    Fl4Spec.updateRestartPc (Z := Unit) t σ = ({((), Notif.updK σ t (.tcb (Notif.setReg x .faultIP
      (x.tcbArch.tcbContext.userRegs .nextIP))))}, False) := by
  unfold Fl4Spec.updateRestartPc
  rw [asUser_one hk _ (uc' := ⟨(Fl4Spec.archTcbContextGet x.tcbArch).userFpuState,
    Function.update (Fl4Spec.archTcbContextGet x.tcbArch).userRegs .faultIP
      ((Fl4Spec.archTcbContextGet x.tcbArch).userRegs .nextIP)⟩)
    (by rw [nd_bind_one' (show Fl4Spec.getRegister Fl4Spec.nextInstructionRegister (Fl4Spec.archTcbContextGet x.tcbArch) =
          ({(_, Fl4Spec.archTcbContextGet x.tcbArch)}, False) from rfl)]; rfl)]
  rfl

set_option maxHeartbeats 4000000 in
/-- **`cancel_yield_to` on `IRel`**, given the yield-to relation: the pair
`(t, p)` is cut (`YieldRel`'s link, `set_sc_yf`, `set_yt`), the spec's
`sched_context_cancel_yield_to` (`ScTKw` by `nkt_schedContextCancelYieldTo`),
lifted by `tk_liftCW`. -/
theorem cancel_yield_to_irel (hP0 : IPlaced N T E R B) {s : S} {σ : Fl4Spec.State Unit}
    (hX : IRel st th cr N T C E R B c s σ) (hY : YieldRel T C (L.mem s) σ) {t : U64} (ht : t ∈ T) :
    schedcontext.cancel_yield_to st s t ⦃ s' => ∃ σ', Fl4Spec.schedContextCancelYieldTo (Z := Unit) t.bv σ =
      ({((), σ')}, False) ∧ IRel st th cr N T C E R B c s' σ' ∧
      ∀ x, σ.kheap t.bv = some (.tcb x) → ∃ x', σ'.kheap t.bv = some (.tcb x') ∧ x'.tcbState = x.tcbState ⦄ := by
  have hS := hX.2.2.1
  obtain ⟨Q, R0, hc, hs⟩ := hS.lists
  have hT := hc.tcbs
  have hy0 : t ≠ 0#u64 := fun e => (hc.tcbs t ht).ne0 (by rw [e]; rfl)
  obtain ⟨xy, hky, eyt⟩ := hY.tcb t ht
  unfold schedcontext.cancel_yield_to
  step with obj.Tcb.is_null.spec as ⟨b, hb⟩
  have hb' : b = false := by rw [hb]; exact decide_eq_false hy0
  rw [hb']
  simp only [Bool.false_eq_true, ↓reduceIte]
  step with obj.Tcb.yield_to.spec as ⟨i, hi⟩
  subst hi
  by_cases hi0 : L.mem s (yieldA t) = 0#u64
  · have : (L.mem s (yieldA t) != 0#u64) = false := by simp [hi0]
    simp only [this, Bool.false_eq_true, ↓reduceIte]
    refine (WP.spec_ok _).mpr ⟨σ, ?_, hX, fun x hx => ⟨x, hx, rfl⟩⟩
    unfold Fl4Spec.schedContextCancelYieldTo
    rw [nd_bind_one (getTcbObjRef_eq _ hky), eyt, hi0, optRef_zero]; rfl
  obtain ⟨p, hp⟩ : ∃ p, L.mem s (yieldA t) = p := ⟨_, rfl⟩
  rw [hp] at hi0 eyt ⊢
  have hb' : (p != 0#u64) = true := by simp [hi0]
  simp only [hb', ↓reduceIte]
  obtain ⟨hpC, ysc, nsc, hksc, -⟩ := hY.toSc t ht (by rw [hp]; exact hi0)
  rw [hp] at hpC hksc
  have hsw56 := sw_hdr hS hpC (K := 56#u64) (by simp) (by simp) (by decide)
  have hal56 : Aligned (scW p 56#u64) := by
    obtain ⟨x0, n0, -, hx0⟩ := hs.scs p hpC; exact (hx0.hdr (K := 56#u64) (by simp) (by simp)).1
  have hcan : (do
      let s1 ← obj.Sc.set_yield_from st p s 0#u64
      obj.Tcb.set_yield_to st t s1 0#u64) ⦃ s4 =>
        s4 = L.wr (L.wr s (scYieldFromA p) 0#u64) (yieldA t) 0#u64 ⦄ :=
    WP.spec_bind (obj.Sc.set_yield_from.spec s _ 0#u64) fun s3 h3 => h3 ▸ obj.Tcb.set_yield_to.spec _ t 0#u64
  refine WP.spec_mono hcan ?_
  rintro s4 rfl
  obtain ⟨hS3, hf3, hK3, -⟩ := hS.set_sc_yf hpC hksc 0#u64
  rw [optRef_zero] at hS3 hK3
  have hpy : p.bv ≠ t.bv := fun e => by rw [e, hky] at hksc; cases hksc
  have hkay : (updSc σ p.bv { ysc with scYieldFrom := none } nsc).kheap t.bv = some (.tcb xy) := by
    simp [updK, Ne.symm hpy, hky]
  obtain ⟨hS4, hf4, hK4⟩ := hS3.set_yt ht hkay 0#u64
  rw [optRef_zero] at hS4 hK4
  have hN4 := (hX.1.toN.frame hS.placed hf3 hK3).frame hS3.placed hf4 hK4
  have hwy : WritesIn st s (L.wr (L.wr s (scYieldFromA p) 0#u64) (yieldA t) 0#u64) (TFoot st T N C c s σ) :=
    ((writesIn_wr (st := st) (s := s) (v := 0#u64)
        (show Aligned (scYieldFromA p) by rw [scYieldFromA_eq]; exact hal56)).trans
      (writesIn_wr (st := st) (s := L.wr s (scYieldFromA p) 0#u64) (v := 0#u64) (yieldA_aligned hT ht))).mono
      fun b hb => by
        rcases hb with rfl | rfl
        · exact Or.inl (KFoot.of_sw (by rw [scYieldFromA_eq]; exact hsw56))
        · exact Or.inr ⟨t, ht, rfl⟩
  have hsp := cancelYieldTo_some hky (by rw [eyt, Notif.optRef_ne hi0]) hksc hpy
  have hK : ScTKw (fun q => q = σ.curThread) σ _ :=
    ScTKw.ofFalse (NKT.of_eq (nkt_schedContextCancelYieldTo t.bv) hsp)
  have hX4 := tk_liftCW hP0 hX (hwy.mono fun _ h => Or.inl h) hK hS4 hN4
  refine ⟨_, hsp, hX4, fun x hx => ?_⟩
  rw [hky] at hx; cases hx
  exact ⟨{ xy with tcbYieldTo := none }, by simp [updK], rfl⟩


/-- **`release_remove`'s footprint** at the precision of `SFootI`. -/
theorem release_remove_sfootI {s : S} {σ : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) {t : U64} (ht : t ∈ T) :
    sched.release_remove st s t ⦃ s' => WritesIn st s s' (SFootI st T c s) ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  have haf := hc.aff t ht
  have hN : NodePlaced st T s (L.mem s (affA t)) := by rw [haf]; exact hc.node
  have hN' : NodePlaced st T s (L.cpu s) := by rw [hc.cur]; exact hc.node
  have hrel : QueueRel (L.mem s) T .Sched (L.relQ s (L.mem s (affA t))) R := by rw [haf]; exact hc.release
  refine WP.spec_mono (sched.release_remove.foot s t _ hc.tcbs ht hN hN' hrel (hc.released t ht).1) ?_
  rintro s' ⟨hw, -⟩
  rw [haf] at hw
  exact hw.mono fun b hb => qfoot_sfootI hc.tcbs (fun w hw' => hc.release.mem w hw') ht hc.node hc.cur hb

theorem cancelSt_code (ts : Fl4Spec.ThreadState) :
    tsCode (cancelSt ts) ≠ 3 ∧ tsCode (cancelSt ts) ≠ 4 ∧ tsCode (cancelSt ts) ≠ 6 := by
  cases ts <;> simp [cancelSt, tsCode]

end

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]
variable {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

set_option maxHeartbeats 8000000 in
/-- **`suspend` on `IRel`** (module docstring). Named: `SchedValid`,
`ObjCover`, `Inv` at the start (`cancel_ipc_irel`) [J], `RemoveTcbHyp`,
and the yield-to relation `YieldRel` on `IRel` [J]. -/
theorem suspend_irel (hP0 : IPlaced N T E R B) (hRT : RemoveTcbHyp st th cr N T C E R B c)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (hX : IRel st th cr N T C E R B c s σ) {t : U64} (ht : t ∈ T)
    (hSV : SchedValid σ) (hOC : ObjCover N T E R C σ) (hInv : Inv σ)
    (hY : ∀ s' σ', IRel st th cr N T C E R B c s' σ' → YieldRel T C (L.mem s') σ') :
    sched.suspend st ar s a t ⦃ r => r.2 = a ∧ ∃ σ', Fl4Spec.suspend (Z := Unit) t.bv σ = ({((), σ')}, False) ∧
      IRel st th cr N T C E R B c r.1 σ' ⦄ := by
  obtain ⟨x, hk, -⟩ := hX.1.tcb t ht
  unfold sched.suspend
  refine WP.spec_bind (cancel_ipc_irel hP0 hRT s a σ hX ht hk hSV hOC hInv) ?_
  rintro ⟨s1, a1⟩ ⟨rfl, σ1, x1, hc1, hX1, hk1, hs1⟩
  step with P1.obj.Tcb.state.spec as ⟨i, hi⟩
  obtain ⟨x1', hk1', hTR1⟩ := hX1.1.tcb t ht
  rw [hk1] at hk1'; cases hk1'
  have hw : i.val = tsCode x1.tcbState := by rw [hi]; exact hTR1.st
  have hrun : i = sched.TS_RUNNING ↔ x1.tcbState = .running := by
    constructor
    · intro h; rw [h] at hw; unfold sched.TS_RUNNING at hw
      generalize x1.tcbState = ts at hw ⊢; cases ts <;> simp_all [tsCode]
    · intro h; rw [h] at hw; apply UScalar.eq_of_val_eq; unfold sched.TS_RUNNING; simp [tsCode] at hw; simp [hw]
  -- the restart PC
  have hreg : (if i = sched.TS_RUNNING then do
        let ip ← obj.Tcb.reg st t s1 layout.reg.NEXT_IP
        obj.Tcb.set_reg st t s1 layout.reg.FAULT_IP ip
      else ok s1) ⦃ s2 => ∃ σ2 x2,
        Fl4Spec.NonDet.when (x1.tcbState = .running) (Fl4Spec.updateRestartPc (Z := Unit) t.bv) σ1 =
          ({((), σ2)}, False) ∧ IRel st th cr N T C E R B c s2 σ2 ∧ σ2.kheap t.bv = some (.tcb x2) ∧
          x2.tcbState = x1.tcbState ⦄ := by
    by_cases hr : x1.tcbState = .running
    · rw [if_pos (hrun.2 hr)]
      step with Endp.obj.Tcb.reg.spec as ⟨ip, hip⟩
      refine WP.spec_mono (Endp.obj.Tcb.set_reg.spec s1 t _ ip) ?_
      rintro s2 rfl
      have hF : layout.reg.FAULT_IP = regIdx .faultIP := by unfold layout.reg.FAULT_IP; rfl
      have hNx : layout.reg.NEXT_IP = regIdx .nextIP := by unfold layout.reg.NEXT_IP; rfl
      have hipv : ip.bv = x1.tcbArch.tcbContext.userRegs .nextIP := by rw [hip, hNx]; exact hTR1.regs .nextIP
      rw [hF]
      refine ⟨_, Notif.setReg x1 .faultIP ip.bv, ?_, reg_wr_irel hP0 hX1 ht hk1 .faultIP (by decide) ip,
        by simp [Notif.updK], rfl⟩
      unfold Fl4Spec.NonDet.when
      rw [if_pos hr, updateRestartPc_eq hk1, hipv]
    · rw [if_neg (fun h => hr (hrun.1 h)), WP.spec_ok]
      refine ⟨σ1, x1, ?_, hX1, hk1, rfl⟩
      unfold Fl4Spec.NonDet.when
      rw [if_neg hr]; rfl
  refine WP.spec_bind hreg ?_
  rintro s2 ⟨σ2, x2, hw2, hX2, hk2, hs2⟩
  -- the ready queue
  have hS2 := hX2.2.2.1
  refine WP.spec_bind (WP.spec_and (dequeue_refines s2 σ2 hS2 t ht) (dequeue_sfootI hS2 ht)) ?_
  rintro s3 ⟨⟨σ3, he3, hk3, -, -, hS3⟩, hw3⟩
  have hX3 := sc_step_lift hP0 hX2 (hw3.mono fun _ h => Or.inr h) (NKS.of_eq (nks_tcbSchedActionI _ _) he3) hS3
  -- the release queue
  have hS3' := hX3.2.2.1
  refine WP.spec_bind (WP.spec_and (release_remove_refines s3 σ3 hS3' ht) (release_remove_sfootI hS3' ht)) ?_
  rintro s4 ⟨⟨σ4, he4, ⟨bb, hσ4⟩, -, hS4⟩, hw4⟩
  have hX4 := sc_step_lift hP0 hX3 (hw4.mono fun _ h => Or.inr h) (NKS.of_eq (nks_tcbReleaseRemove _) he4) hS4
  have hk4 : σ4.kheap t.bv = some (.tcb x2) := by rw [hσ4]; show σ3.kheap t.bv = _; rw [hk3]; exact hk2
  -- the yield-to pair
  refine WP.spec_bind (cancel_yield_to_irel hP0 hX4 (hY _ _ hX4) ht) ?_
  rintro s5 ⟨σ5, he5, hX5, hk5f⟩
  obtain ⟨x5, hk5, hs5⟩ := hk5f x2 hk4
  have hst5 : x5.tcbState = cancelSt x.tcbState := by rw [hs5, hs2, hs1]
  -- inactive
  obtain ⟨x5', hk5', hTR5⟩ := hX5.1.tcb t ht
  rw [hk5] at hk5'; cases hk5'
  have hc5 := cancelSt_code x.tcbState
  have hw5 : (L.mem s5 (tStA t)).val = tsCode (cancelSt x.tcbState) := by rw [hTR5.st, hst5]
  have hq := IpcRel.not_ep_queued hX5.1 (t := t) ⟨by rw [hw5]; exact hc5.1, by rw [hw5]; exact hc5.2.1⟩
  have hH := ipcCore_top (st := st) (th := th) (cr := cr) (N := N) (C := C) (c := c) hP0.e
  have hSR := IpcRel.toSRN hX5.1 hX5.2
  refine WP.spec_bind (set_thread_state_c hH hP0 hP0.e _ _ hX5.1.toE hSR ht hk5 hq (by rw [hst5]; exact hc5.2.2)
    .inactive (by simp [tsCode]) sched.TS_INACTIVE (by unfold sched.TS_INACTIVE; rfl)) ?_
  rintro s6 ⟨hR6, hS6⟩
  rw [WP.spec_ok]
  refine ⟨rfl, _, ?_, IpcRel.ofSRN hR6 hS6⟩
  unfold Fl4Spec.suspend
  rw [nd_bind_one hc1, nd_bind_one (getThreadState_eq hk1), nd_bind_one hw2, nd_bind_one he3, nd_bind_one he4,
    nd_bind_one he5, Notif.setThreadState_eq _ hk5]

end

end

end Fl4Proofs.P3.Ipc

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **What Suspend needs beyond `IRel`**, at a state: `reply_remove_tcb`'s
facts (`RemoveTcbOK`: the call stacks, `RPlaced`, `NSC`, `Inv`,
`SchedValid`, `ObjCover`) and the yield-to relation `YieldRel` [J]. -/
def SuspendOK (st : machine.Store S) [L : P1.LawfulStore st] (Z : XSets) (s : S) (σ : Fl4Spec.State Unit) : Prop :=
  RemoveTcbOK st Z.N Z.T Z.C Z.E Z.R Z.c s σ ∧ YieldRel Z.T Z.C (L.mem s) σ

/-- **`SuspendXLeaf`**: the restart (`xleaf_restart`), then `suspend_irel`.
Named, at every `Z` the entry's `XTopAt` holds at: `KsApart`, the IPC
placement, the target among the TCBs, `SuspendOK` on `IRel`; `BufWordRel`
at `XTopAt`; `CurRun` [J]. -/
theorem suspendXLeaf_of {AR : A → Fl4Spec.Cr3 → Prop} {s : S} {ar : A} {σ σ1 : Fl4Spec.State Unit} {p : U64}
    (hst : Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False)) (hC : CurRun σ)
    (hZ : ∀ Z : XSets, XTopAt (L := L) AR Z s ar σ → KsApart Z.N Z.T Z.E Z.R Z.B (L.ksb s) ∧
      IPlaced Z.N Z.T Z.E Z.R Z.B ∧ p ∈ Z.T ∧
      (∀ s' σ', IRel st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c s' σ' → SuspendOK st Z s' σ'))
    (hBW : ∀ (Z : XSets) s' a' σ', XTopAt (L := L) AR Z s' a' σ' → BufWordRel Z.T (L.mem s') σ') :
    SuspendXLeaf (L := L) arI AR s ar σ σ1 p := by
  refine xleaf_restart hst hC (fun Z hX => (hZ Z hX).1) hBW fun Z s1 hX _ _ hI1 => ?_
  obtain ⟨-, hP0, hpT, hOK⟩ := hZ Z hX
  have hAR : AR ar σ.archState.x64CurrentCr3 := hX.fin.1.1.2.2.2.2.2.2
  obtain ⟨⟨Lst, -, -, -, -, hInv, -, hSV, hOC⟩, -⟩ := hOK _ _ hI1
  refine WP.spec_bind (suspend_irel (ar := arI) hP0 (removeTcbHyp_of hP0 fun s' σ' h => (hOK s' σ' h).1)
    s1 ar σ1 hI1 hpT hSV hOC hInv fun s' σ' h => (hOK s' σ' h).2) ?_
  rintro ⟨s2, a2⟩ ⟨rfl, σ2, hm, hI2⟩
  exact (WP.spec_ok _).2 ⟨rfl, hAR, ((), σ2), by rw [hm]; exact Set.mem_singleton _, hI2⟩

end

end

end Fl4Proofs.P3
