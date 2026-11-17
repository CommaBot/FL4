/-
P3 (DESIGN.md §9), TCB invocations: **Suspend on `IRel`** (`sched::suspend`
against l4v `suspend`); the theorem is IpcSuspendJ's
`suspend_irelY` (the leaf from `JAtZ`: `suspendXLeafJ`); here its steps.

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
    (by simp [RelOffs])

theorem cancelSt_code (ts : Fl4Spec.ThreadState) :
    tsCode (cancelSt ts) ≠ 3 ∧ tsCode (cancelSt ts) ≠ 4 ∧ tsCode (cancelSt ts) ≠ 6 := by
  cases ts <;> simp [cancelSt, tsCode]

end
end

end Fl4Proofs.P3.Ipc

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

end

end

end Fl4Proofs.P3
