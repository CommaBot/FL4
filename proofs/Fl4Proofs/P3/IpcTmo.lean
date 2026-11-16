/-
P3 (DESIGN.md §9), IPC: **the transfer of a timeout fault from a thread
with a scheduling context** (`ReplyTmoHyps.tmoXfer`).

The fault message is the badge and the SC's consumed time
(`sched_context_update_consumed`): FL4's `update_consumed` writes the SC's
consumed word (to 0: FL4 caps the consumed time at `U64::MAX` ticks, and
`ticks ≥ U64::MAX` means `ticks = U64::MAX`), the spec sets the SC's
`scConsumed` (to 0 likewise, given the x86 platform fact `hmax`).

* `update_consumed_ref0`: ScConsumed's `update_consumed_refines` with the
  written word and the spec's state explicit.
* `set_mrs_fault_tmoSC`, `_tmoSCN`: `set_mrs_fault` of the timeout fault,
  the SC step lifted by `sc_step_lift`, then the two message words.
* `do_ipc_transfer_tmoSC`: `do_ipc_transfer` of the faulted sender (with or
  without a receive buffer), at `XferPost`; the SC's change is `KeepNC`'s SC
  clause. Named: `hmax` and `htu` (FL4's `ticks_to_us` is the spec's).
-/
import Fl4Proofs.P3.IpcSchedLift
import Fl4Proofs.P3.ScConsumed
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]

/-- The time `sched_context_update_consumed` returns for consumed ticks `x`. -/
def consumedUs (x : Fl4Spec.Ticks) : Fl4Spec.Time :=
  Fl4Spec.ticksToUs (if Fl4Spec.maxTicksToUs ≤ x then Fl4Spec.maxTicksToUs else x)

/-- **`update_consumed`**, with the written word and the spec's state
explicit (ScConsumed's `update_consumed_refines`). -/
theorem update_consumed_ref0 {N T C : Set U64} {c : U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ)
    {sc : U64} (hsc : sc ∈ C) {x : Fl4Spec.SchedContext} {n : Nat} (hk : σ.kheap sc.bv = some (.schedContext x n))
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ v, ar.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) :
    schedcontext.update_consumed st ar s a sc ⦃ r => r.2 = L.wr s (scW sc 8#u64) 0#u64 ∧
      r.1.bv = consumedUs x.scConsumed ∧
      Fl4Spec.schedContextUpdateConsumed (Z := Unit) sc.bv σ =
        ({(r.1.bv, updSc σ sc.bv { x with scConsumed := (0#u64 : U64).bv } n)}, False) ∧
      SchedRel st N T C c r.2 (updSc σ sc.bv { x with scConsumed := (0#u64 : U64).bv } n) ∧
      NtfnStateRel N T (L.mem r.2) (updSc σ sc.bv { x with scConsumed := (0#u64 : U64).bv } n) ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨x', n', hk', hx⟩ := hs.scs sc hsc
  rw [hk] at hk'; cases hk'
  have hsp : Fl4Spec.schedContextUpdateConsumed (Z := Unit) sc.bv σ =
      (if Fl4Spec.maxTicksToUs ≤ x.scConsumed then
        (do
          Fl4Spec.setScObjRef Fl4Spec.scConsumedUpdate sc.bv (x.scConsumed - Fl4Spec.maxTicksToUs)
          return Fl4Spec.ticksToUs Fl4Spec.maxTicksToUs) σ
      else (do
          Fl4Spec.setScObjRef Fl4Spec.scConsumedUpdate sc.bv 0
          return Fl4Spec.ticksToUs x.scConsumed) σ) := by
    unfold Fl4Spec.schedContextUpdateConsumed
    rw [nd_bind_one (getSchedContext_eq hk), nd_pure_bind']
    split_ifs <;> rfl
  have fin : ∀ (w : Fl4Spec.Ticks), (0#u64 : U64).bv = w → ∀ (r : U64) (tm : Fl4Spec.Ticks), r.bv = tm →
      (Fl4Spec.setScObjRef Fl4Spec.scConsumedUpdate sc.bv w >>= fun _ => pure tm) σ =
        ({(r.bv, updSc σ sc.bv { x with scConsumed := (0#u64 : U64).bv } n)}, False) ∧
      SchedRel st N T C c (L.wr s (scW sc 8#u64) 0#u64) (updSc σ sc.bv { x with scConsumed := (0#u64 : U64).bv } n) ∧
      NtfnStateRel N T (L.mem (L.wr s (scW sc 8#u64) 0#u64))
        (updSc σ sc.bv { x with scConsumed := (0#u64 : U64).bv } n) := by
    intro w hv r tm hr
    obtain ⟨hS1, hf, hkv⟩ := hS.set_sc_consumed hsc hk 0#u64
    refine ⟨?_, hS1, hR.frame hS.placed hf hkv⟩
    rw [nd_bind_one (updateSchedContext_eq hk _), hr, ← hv]; rfl
  unfold schedcontext.update_consumed
  step with obj.Sc.consumed.spec' as ⟨cv, hcv⟩
  have hxc : x.scConsumed = cv.bv := by rw [hx.consumed, hcv]
  by_cases hge : cv ≥ core.num.U64.MAX
  · simp only [hge, ↓reduceIte]
    have hcm : cv = core.num.U64.MAX := by
      have := cv.hBounds
      simp [core.num.U64.MAX, U64.rMax] at hge ⊢
      scalar_tac
    subst hcm
    step as ⟨i, hi⟩
    have hi0 : i = 0#u64 := by scalar_tac
    subst hi0
    step with obj.Sc.set_consumed.spec' as ⟨s1, hs1⟩
    subst hs1
    refine WP.spec_bind (htu _) ?_
    intro r hr
    simp only [WP.spec_ok]
    have hle : Fl4Spec.maxTicksToUs ≤ x.scConsumed := by rw [hxc, hmax]; exact BitVec.le_refl _
    obtain ⟨h1, h2, h3⟩ := fin (x.scConsumed - Fl4Spec.maxTicksToUs)
      (by rw [hxc, hmax]; simp) r _ (by rw [hr, ← hmax])
    refine ⟨by first | rfl | trivial, by rw [hr, consumedUs, if_pos hle, hmax], ?_, h2, h3⟩
    rw [hsp, if_pos hle]
    exact h1
  · simp only [hge, ↓reduceIte]
    step with obj.Sc.set_consumed.spec' as ⟨s1, hs1⟩
    subst hs1
    refine WP.spec_bind (htu _) ?_
    intro r hr
    simp only [WP.spec_ok]
    have hnle : ¬ Fl4Spec.maxTicksToUs ≤ x.scConsumed := by rw [hxc, hmax, ← u64_le_bv]; exact hge
    obtain ⟨h1, h2, h3⟩ := fin 0 rfl r _ (by rw [hr, ← hxc])
    refine ⟨by first | rfl | trivial, by rw [hr, consumedUs, if_neg hnle, hxc], ?_, h2, h3⟩
    rw [hsp, if_neg hnle]
    exact h1

end

end

end Fl4Proofs.P3.Sched

namespace Fl4Proofs.P3.Ipc
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Sched

noncomputable section

section Spec
open Fl4Spec

theorem nks_schedContextUpdateConsumed (p : ObjRef) : NKS (schedContextUpdateConsumed (Z := Unit) p) := by
  unfold schedContextUpdateConsumed
  nks_auto

/-- The fault message of a timeout fault from a thread with an SC. -/
theorem makeFaultMsg_timeoutSC {σ σu : State Unit} {t sc : ObjRef} {x : Tcb} (hk : σ.kheap t = some (.tcb x))
    (hsc : x.tcbSchedContext = some sc) {cv : Time}
    (hu : schedContextUpdateConsumed (Z := Unit) sc σ = ({(cv, σu)}, False)) (b : Word) :
    makeFaultMsg (Z := Unit) (.timeout b) t σ = ({((5, [b, cv]), σu)}, False) := by
  rw [makeFaultMsg]
  show (NonDet.getsThe _ >>= _) σ = _
  rw [nd_bind_one (getTcb_eq hk), hsc]
  show (schedContextUpdateConsumed sc >>= _) σ = _
  rw [nd_bind_one hu]
  simp [wordsFromTime, ucast]

/-- **`sched_context_update_consumed`**, its outcome (the consumed time at
most `maxTicksToUs`, which is `U64::MAX`). -/
theorem schedContextUpdateConsumed_eq {σ : State Unit} {sc : ObjRef} {y : SchedContext} {n : Nat}
    (hk : σ.kheap sc = some (.schedContext y n)) (hmax : maxTicksToUs = core.num.U64.MAX.bv) :
    schedContextUpdateConsumed (Z := Unit) sc σ =
      ({(Sched.consumedUs y.scConsumed, Sched.updSc σ sc { y with scConsumed := (0#u64 : U64).bv } n)}, False) := by
  unfold schedContextUpdateConsumed
  rw [nd_bind_one (Sched.getSchedContext_eq hk), nd_pure_bind']
  have h0 : ((0#u64 : U64).bv : Ticks) = 0 := rfl
  split_ifs with h
  · have hm : y.scConsumed = maxTicksToUs := by
      apply BitVec.le_antisymm _ h
      rw [hmax]; simp [core.num.U64.MAX, U64.rMax]; bv_omega
    show (updateSchedContext _ _ >>= _) σ = _
    rw [nd_bind_one (Sched.updateSchedContext_eq hk _), Sched.consumedUs, if_pos h]
    simp only [hm, BitVec.sub_self]
    rfl
  · show (updateSchedContext _ _ >>= _) σ = _
    rw [nd_bind_one (Sched.updateSchedContext_eq hk _), Sched.consumedUs, if_neg h]
    rfl

end Spec

section Msg
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]
variable {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

/-- The SC step of a timeout fault's message on `IRel`: `update_consumed`
lifted by `sc_step_lift`. -/
theorem update_consumed_irel (hP0 : IPlaced N T E R B) (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hX : IRel st th cr N T C E R B c s σ) {sc : U64} (hsc : sc ∈ C) {y : Fl4Spec.SchedContext} {n : Nat}
    (hky : σ.kheap sc.bv = some (.schedContext y n))
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ v, ar.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) :
    schedcontext.update_consumed st ar s a sc ⦃ r => r.2 = L.wr s (scW sc 8#u64) 0#u64 ∧
      r.1.bv = consumedUs y.scConsumed ∧
      Fl4Spec.schedContextUpdateConsumed (Z := Unit) sc.bv σ =
        ({(r.1.bv, updSc σ sc.bv { y with scConsumed := (0#u64 : U64).bv } n)}, False) ∧
      IRel st th cr N T C E R B c r.2 (updSc σ sc.bv { y with scConsumed := (0#u64 : U64).bv } n) ⦄ := by
  have hS := hX.2.2.1
  refine WP.spec_mono (update_consumed_ref0 s a σ hS hX.1.toN hsc hky hmax htu) ?_
  rintro ⟨cv, s1⟩ ⟨hs1, hcv, hsp, hS1, -⟩
  simp only at hs1 hcv hsp hS1 ⊢
  subst hs1
  obtain ⟨Q, R0, hc, hs⟩ := hS.lists
  obtain ⟨x0, n0, hk0, hx0⟩ := hs.scs sc hsc
  have hal : Aligned (scW sc 8#u64) := (hx0.hdr (K := 8#u64) (by simp) (by simp)).1
  have hW : WritesIn st s (L.wr s (scW sc 8#u64) 0#u64) (fun b => ScW st C c s σ b ∨ SFootI st T c s b) :=
    (writesIn_wr hal).mono fun b hb => Or.inl (Or.inl (hb ▸ sw_hdr hS hsc (K := 8#u64) (by simp) (by simp) (by decide)))
  have hK := nks_schedContextUpdateConsumed sc.bv σ (cv.bv, _) (by rw [hsp]; rfl)
  exact ⟨rfl, hcv, hsp, sc_step_lift hP0 hX hW hK hS1⟩

/-- The spec's state after the timeout fault's SC step. -/
abbrev tmoSt (σ : Fl4Spec.State Unit) (sc : U64) (y : Fl4Spec.SchedContext) (n : Nat) : Fl4Spec.State Unit :=
  updSc σ sc.bv { y with scConsumed := (0#u64 : U64).bv } n

variable (st) in
/-- The FL4 state after the timeout fault's SC step. -/
abbrev tmoS (s : S) (sc : U64) : S := L.wr s (scW sc 8#u64) 0#u64

set_option maxHeartbeats 2000000 in
/-- **`set_mrs_fault` of a timeout fault from a thread with an SC**, into a
receive buffer: the SC step (`update_consumed_irel`), then the badge and the
consumed time. -/
theorem set_mrs_fault_tmoSC (hH : IpcSchedHyps st ar N T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c)))
    (hP0 : IPlaced N T E R B) (s : S) (a : A) (σ : Fl4Spec.State Unit) (hX : IRel st th cr N T C E R B c s σ)
    {snd rcv : U64} (hs : snd ∈ T) (hr : rcv ∈ T) {xs xr : Fl4Spec.Tcb}
    (hks : σ.kheap snd.bv = some (.tcb xs)) (hkr : σ.kheap rcv.bv = some (.tcb xr))
    {b : Fl4Spec.Word} (hf : xs.tcbFault = some (.timeout b)) {sc : U64} (hsc : L.mem s (scA snd) = sc)
    (hsc0 : sc ≠ 0#u64) (hscC : sc ∈ C) {y : Fl4Spec.SchedContext} {n : Nat}
    (hky : σ.kheap sc.bv = some (.schedContext y n))
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ v, ar.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    {rw : U64} {p : Fl4Spec.ObjRef} (hrw0 : rw ≠ 0#u64) (hmr : BufMap B rw p) :
    faults.set_mrs_fault st ar s a snd rcv rw ⦃ r => r.1.val = [b, consumedUs y.scConsumed].length ∧
      MrInv (L := L) T E R B (SRS st T (SRT st th cr N T C E R B c (SRE st N T C E R B c))) (tmoS st s sc)
        (tmoSt σ sc y n) rcv xr p r.2 [b, consumedUs y.scConsumed] ⦄ := by
  have hE := hH.epHyps hP0
  have hP := hP0.e
  have hxs := hX.1.toE.at_tcb hs hks
  have hfr := hxs.faultR
  unfold FaultRel at hfr
  rw [hf] at hfr
  obtain ⟨hty, hw0⟩ := hfr
  have hrsc : rcv.bv ≠ sc.bv := kheap_ne hkr hky (fun _ h1 h2 => by subst h1; cases h2)
  unfold faults.set_mrs_fault
  step with obj.Tcb.fault_type.spec as ⟨ty, hty'⟩
  step with obj.Tcb.fault_w0.spec as ⟨w0, hw0'⟩
  step with obj.Tcb.fault_w1.spec as ⟨w1, hw1'⟩
  step with obj.Tcb.fault_w2.spec as ⟨w2, hw2'⟩
  step with Endp.obj.Tcb.reg.spec as ⟨pc, hpc'⟩
  subst hty' hw0' hw1' hw2' hpc'
  rw [hty, ite_eq_right_of_eq_false _ _ (by unfold fl4_abi.consts.fault.CapFault; decide),
    ite_eq_right_of_eq_false _ _ (by unfold fl4_abi.consts.fault.UnknownSyscall; decide),
    ite_eq_right_of_eq_false _ _ (by unfold fl4_abi.consts.fault.UserException; decide),
    ite_eq_left_of_eq_true _ _ (eq_true (by unfold fl4_abi.consts.fault.Timeout; rfl))]
  step with obj.Tcb.sc.spec as ⟨i, hi⟩
  subst hi
  unfold obj.Sc.is_null
  apply ok_bind_spec
  simp only [hsc, hsc0, decide_false, Bool.false_eq_true, ↓reduceIte]
  refine WP.spec_bind (update_consumed_irel hP0 s a σ hX hscC hky hmax htu) ?_
  rintro ⟨cv, s1⟩ ⟨hs1, hcv, -, hI1⟩
  simp only at hs1 hcv hI1
  subst hs1
  have hkr1 : (tmoSt σ sc y n).kheap rcv.bv = some (.tcb xr) := by simp [updK, hrsc, hkr]
  have hM0 := mrInv_init (L := L) (SR := SRS st T (SRT st th cr N T C E R B c (SRE st N T C E R B c)))
    hI1.1.toE ⟨hI1.2, ScRelM.of hI1.1⟩ hkr1 p
  refine WP.spec_bind (set_mr_inv (L := L) hE hP hr hkr1 hrw0 hmr hM0 0#u64 rfl (by decide)
    (L.mem s (tFw0A snd))) ?_
  rintro ⟨k, s2⟩ ⟨hk, hM1⟩
  simp only at hk hM1
  refine WP.spec_mono (set_mr_inv (L := L) hE hP hr hkr1 hrw0 hmr hM1 k (by simpa using hk) (by simp at hk; omega)
    cv) ?_
  rintro ⟨k2, s3⟩ ⟨hk2, hM2⟩
  simp only at hk2 hM2 ⊢
  rw [hw0, hcv] at hM2
  exact ⟨by simp at hk hk2 ⊢; omega, hM2⟩

set_option maxHeartbeats 2000000 in
/-- **`set_mrs_fault` of a timeout fault from a thread with an SC**, without a
receive buffer: the SC step (`update_consumed_irel`), then the badge and the
consumed time. -/
theorem set_mrs_fault_tmoSCN (hH : IpcSchedHyps st ar N T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c)))
    (hP0 : IPlaced N T E R B) (s : S) (a : A) (σ : Fl4Spec.State Unit) (hX : IRel st th cr N T C E R B c s σ)
    {snd rcv : U64} (hs : snd ∈ T) (hr : rcv ∈ T) {xs xr : Fl4Spec.Tcb}
    (hks : σ.kheap snd.bv = some (.tcb xs)) (hkr : σ.kheap rcv.bv = some (.tcb xr))
    {b : Fl4Spec.Word} (hf : xs.tcbFault = some (.timeout b)) {sc : U64} (hsc : L.mem s (scA snd) = sc)
    (hsc0 : sc ≠ 0#u64) (hscC : sc ∈ C) {y : Fl4Spec.SchedContext} {n : Nat}
    (hky : σ.kheap sc.bv = some (.schedContext y n))
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ v, ar.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) :
    faults.set_mrs_fault st ar s a snd rcv 0#u64 ⦃ r => r.1.val = min [b, consumedUs y.scConsumed].length 4 ∧
      MrInvN (L := L) T E R B (SRS st T (SRT st th cr N T C E R B c (SRE st N T C E R B c))) (tmoS st s sc)
        (tmoSt σ sc y n) rcv xr r.2 [b, consumedUs y.scConsumed] ⦄ := by
  have hE := hH.epHyps hP0
  have hP := hP0.e
  have hxs := hX.1.toE.at_tcb hs hks
  have hfr := hxs.faultR
  unfold FaultRel at hfr
  rw [hf] at hfr
  obtain ⟨hty, hw0⟩ := hfr
  have hrsc : rcv.bv ≠ sc.bv := kheap_ne hkr hky (fun _ h1 h2 => by subst h1; cases h2)
  unfold faults.set_mrs_fault
  step with obj.Tcb.fault_type.spec as ⟨ty, hty'⟩
  step with obj.Tcb.fault_w0.spec as ⟨w0, hw0'⟩
  step with obj.Tcb.fault_w1.spec as ⟨w1, hw1'⟩
  step with obj.Tcb.fault_w2.spec as ⟨w2, hw2'⟩
  step with Endp.obj.Tcb.reg.spec as ⟨pc, hpc'⟩
  subst hty' hw0' hw1' hw2' hpc'
  rw [hty, ite_eq_right_of_eq_false _ _ (by unfold fl4_abi.consts.fault.CapFault; decide),
    ite_eq_right_of_eq_false _ _ (by unfold fl4_abi.consts.fault.UnknownSyscall; decide),
    ite_eq_right_of_eq_false _ _ (by unfold fl4_abi.consts.fault.UserException; decide),
    ite_eq_left_of_eq_true _ _ (eq_true (by unfold fl4_abi.consts.fault.Timeout; rfl))]
  step with obj.Tcb.sc.spec as ⟨i, hi⟩
  subst hi
  unfold obj.Sc.is_null
  apply ok_bind_spec
  simp only [hsc, hsc0, decide_false, Bool.false_eq_true, ↓reduceIte]
  refine WP.spec_bind (update_consumed_irel hP0 s a σ hX hscC hky hmax htu) ?_
  rintro ⟨cv, s1⟩ ⟨hs1, hcv, -, hI1⟩
  simp only at hs1 hcv hI1
  subst hs1
  have hkr1 : (tmoSt σ sc y n).kheap rcv.bv = some (.tcb xr) := by simp [updK, hrsc, hkr]
  have hM0 := mrInvN_init (L := L) (SR := SRS st T (SRT st th cr N T C E R B c (SRE st N T C E R B c)))
    hI1.1.toE ⟨hI1.2, ScRelM.of hI1.1⟩ hkr1
  refine WP.spec_bind (set_mr_invN (L := L) hE hP hr hkr1 hM0 0#u64 rfl (by decide)
    (L.mem s (tFw0A snd))) ?_
  rintro ⟨k, s2⟩ ⟨hk, hM1⟩
  simp only at hk hM1
  refine WP.spec_mono (set_mr_invN (L := L) hE hP hr hkr1 hM1 k (by simpa using hk) (by simp at hk; omega)
    cv) ?_
  rintro ⟨k2, s3⟩ ⟨hk2, hM2⟩
  simp only at hk2 hM2 ⊢
  rw [hw0, hcv] at hM2
  exact ⟨by simp at hk hk2 ⊢; omega, hM2⟩

end Msg


section Xfer
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]
variable {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

set_option maxHeartbeats 4000000 in
/-- **`do_ipc_transfer` of a timeout fault from a thread with an SC**
(`ReplyTmoHyps.tmoXfer`), with or without a receive buffer: the SC step
(`set_mrs_fault_tmoSC`, `_tmoSCN`) inside the fault transfer, at `XferPost`
(the SC's change is `KeepNC`'s SC clause). Named: `hmax` (x86's
`getMaxTicksToUs()` is `UINT64_MAX`) and `htu` (FL4's `ticks_to_us` is the
spec's `ticksToUs`). -/
theorem tmoXfer_top (hH : IpcSchedHyps st ar N T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c)))
    (hBf : EpBufHyps st T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c)))
    (hBm : EpBufMapHyps st T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c)))
    (hP0 : IPlaced N T E R B) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ (a : A) v, ar.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) :
    ∀ (a : A) (t : U64) (xt : Fl4Spec.Tcb) (bb : Fl4Spec.Word) (e bdg : U64) (g : Bool) (d : U64)
      (xd : Fl4Spec.Tcb), t ∈ T → d ∈ T → t ≠ d → xt.tcbFault = some (.timeout bb) → xt.tcbSchedContext ≠ none →
      ∀ (s1 : S) (σ1 : Fl4Spec.State Unit),
        EpStateRel T E R B (L.mem s1) σ1 → SRN st N T (SRS st T (SRT st th cr N T C E R B c (SRE st N T C E R B c))) s1 σ1 →
        σ1.kheap t.bv = some (.tcb xt) → σ1.kheap d.bv = some (.tcb xd) →
        ipc.do_ipc_transfer st ar s1 a t e bdg g d ⦃ s' => XferPost (L := L) T E R B
          (SRN st N T (SRS st T (SRT st th cr N T C E R B c (SRE st N T C E R B c)))) s1 σ1 t d e bdg g xd s' ⦄ := by
  intro a t xt bb e bdg g d xd ht hd htd hf hscn s σ hR hSN hks hkd
  have hX : IRel st th cr N T C E R B c s σ := IpcRel.ofSRN hR hSN
  have hP := hP0.e
  have hE := hH.epHyps hP0
  have hS := hX.2.2.1
  have hA := hX.2.2.2
  obtain ⟨Q, R0, hc, hsp⟩ := hS.lists
  obtain ⟨x0, hk0, -, -, hscw, -⟩ := hsp.tcb t ht
  rw [hks] at hk0; cases hk0
  obtain ⟨scb, hscb⟩ := Option.ne_none_iff_exists'.1 hscn
  set sc := L.mem s (scA t) with hscdef
  obtain ⟨hsc0, hscbv⟩ := Notif.optRef_some (hscw.symm.trans hscb)
  have hscC := hsp.scMem t ht hsc0
  obtain ⟨y, n, hky, hy⟩ := hsp.scs sc hscC
  have hscx : xt.tcbSchedContext = some sc.bv := by rw [hscb, hscbv]
  have hdsc : d.bv ≠ sc.bv := kheap_ne hkd hky (fun _ h1 h2 => by subst h1; cases h2)
  have hkd' : (tmoSt σ sc y n).kheap d.bv = some (.tcb xd) := by simp [updK, hdsc, hkd]
  have hupd := schedContextUpdateConsumed_eq hky hmax
  have hmsg := makeFaultMsg_timeoutSC hks hscx hupd bb
  have hxs := hR.at_tcb ht hks
  have hfr := hxs.faultR
  unfold FaultRel at hfr
  rw [hf] at hfr
  have hta := hP.tcb t ht
  -- the SC word is no IPC word
  have hscw8 : ScW st C c s σ (scW sc 8#u64) := Or.inl (sw_hdr hS hscC (K := 8#u64) (by simp) (by simp) (by decide))
  have hnot : ∀ b, IFoot N T E R B b → b ≠ scW sc 8#u64 := fun b hb e => scw_not_ifoot hP0 hS hA (e ▸ hscw8) hb
  have hal8 : Aligned (scW sc 8#u64) := (hy.hdr (K := 8#u64) (by simp) (by simp)).1
  have hty0 : L.mem (tmoS st s sc) (tFaultA t) = 5#u64 := by
    rw [rd_wr_ne hal8 (a_fault hta).1 (fun e => hnot _ (Or.inl (Or.inr (Or.inr (Or.inl ⟨t, ht, Or.inl
      (a_fault hta).2⟩)))) e.symm)]
    exact hfr.1
  -- the post from the fault transfer's
  have hI0 : IRel st th cr N T C E R B c (tmoS st s sc) (tmoSt σ sc y n) := by
    obtain ⟨hS1, -, -⟩ := hS.set_sc_consumed hscC hky 0#u64
    have hW : WritesIn st s (tmoS st s sc) (fun b => ScW st C c s σ b ∨ SFootI st T c s b) :=
      (writesIn_wr hal8).mono fun b hb => Or.inl (hb ▸ hscw8)
    exact sc_step_lift hP0 hX hW (nks_schedContextUpdateConsumed sc.bv σ (_, _) (by rw [hupd]; rfl)) hS1
  have post : ∀ s' : S, (∃ σ', Fl4Spec.doIpcTransfer (Z := Unit) t.bv (some e.bv) bdg.bv g d.bv σ = ({((), σ')}, False) ∧
      EpStateRel T E R B (L.mem s') σ' ∧
      SRS st T (SRT st th cr N T C E R B c (SRE st N T C E R B c)) s' σ' ∧
      Agree (L.mem (tmoS st s sc)) (L.mem s') (fun b => ¬ RcvReg d b ∧ ¬ BufW B b) ∧
      (∀ q, q ≠ d.bv → σ'.kheap q = (tmoSt σ sc y n).kheap q) ∧
      ∃ x', σ'.kheap d.bv = some (.tcb x') ∧ x'.tcbState = xd.tcbState) →
      XferPost (L := L) T E R B (SRN st N T (SRS st T (SRT st th cr N T C E R B c (SRE st N T C E R B c)))) s σ t d e
        bdg g xd s' := by
    rintro s' ⟨σ', h1, h2, h3, h4, h5, x', h6, h7⟩
    refine ⟨σ', h1, h2, ⟨h3, ntfn_lift_rcv hP0.toC hI0.1.toN h2 hd h4 h5 hkd' h6 h7⟩, fun b hb ⟨⟨y0, hy0, htf⟩, hn⟩ => ?_,
      fun q hq => ?_, x', h6, h7⟩
    · rw [h4 b hb hn, rd_wr_ne hal8 hb (fun e' => hnot _ (Or.inl (Or.inr (Or.inr (Or.inl ⟨y0, hy0, Or.inl htf⟩))))
        e'.symm)]
    · rw [h5 q hq]
      by_cases eq : q = sc.bv
      · subst eq
        exact Or.inr (Or.inr ⟨y, { y with scConsumed := (0#u64 : U64).bv }, n, hky, by simp [Sched.updSc, updK]⟩)
      · exact Or.inl (by simp [Sched.updSc, updK, eq])
  cases hrb : ipcBufOf true xd with
  | none =>
    have hspec : Fl4Spec.doIpcTransfer (Z := Unit) t.bv (some e.bv) bdg.bv g d.bv σ =
        Fl4Spec.doFaultTransfer (Z := Unit) bdg.bv t.bv d.bv none σ := by
      unfold Fl4Spec.doIpcTransfer
      rw [nd_bind_one (lookupIpcBuffer_eq hkd true), hrb, nd_bind_one (threadGet_eq _ hks), hf]
    unfold ipc.do_ipc_transfer
    refine WP.spec_bind (hBf.srs.lookup s σ d xd true hR hSN.1 hd hkd) ?_
    rintro rw hrw
    obtain rfl : rw = 0#u64 := hrw.2 hrb
    step with obj.Tcb.fault_type.spec as ⟨ft, hft⟩
    have hft0 : ¬ ft = fl4_abi.consts.fault.NullFault := by
      intro h
      have : L.mem s (tFaultA t) = 0#u64 := by rw [← hft, h]; unfold fl4_abi.consts.fault.NullFault; rfl
      rw [hxs.fault0.1 this] at hf; cases hf
    simp only [hft0, ↓reduceIte]
    refine WP.spec_mono (do_fault_transfer_fullN hE hP s a σ ht hd htd hks hkd' hf hmsg hty0 (by rw [mask52]; decide)
      bdg (set_mrs_fault_tmoSCN hH hP0 s a σ hX ht hd hks hkd hf rfl hsc0 hscC hky hmax (htu a))) ?_
    rintro s' ⟨σ', h1, h2⟩
    exact post s' ⟨σ', hspec.trans h1, h2⟩
  | some rp =>
    have hu := hBm.srs.frame s σ d xd rp hR hSN.1 hd hkd hrb
    have hu' : ∀ k, k < 128 → Fl4Spec.inUserFrame (bufAddr rp k) (tmoSt σ sc y n) := by
      intro k hk
      obtain ⟨sz, hz⟩ := hu k hk
      refine ⟨sz, ?_⟩
      have hne : bufAddr rp k &&& ~~~(Fl4Spec.mask (Fl4Spec.pageBitsForSize sz)) ≠ sc.bv := by
        intro e'; rw [e', hky] at hz; cases hz
      simp [updK, hne, hz]
    have hspec : Fl4Spec.doIpcTransfer (Z := Unit) t.bv (some e.bv) bdg.bv g d.bv σ =
        Fl4Spec.doFaultTransfer (Z := Unit) bdg.bv t.bv d.bv (some rp) σ := by
      unfold Fl4Spec.doIpcTransfer
      rw [nd_bind_one (lookupIpcBuffer_eq hkd true), hrb, nd_bind_one (threadGet_eq _ hks), hf]
    unfold ipc.do_ipc_transfer
    refine WP.spec_bind (hBm.srs.lookupMap s σ d xd true rp hR hSN.1 hd hkd hrb) ?_
    rintro rw ⟨hrw0, hmr⟩
    step with obj.Tcb.fault_type.spec as ⟨ft, hft⟩
    have hft0 : ¬ ft = fl4_abi.consts.fault.NullFault := by
      intro h
      have : L.mem s (tFaultA t) = 0#u64 := by rw [← hft, h]; unfold fl4_abi.consts.fault.NullFault; rfl
      rw [hxs.fault0.1 this] at hf; cases hf
    simp only [hft0, ↓reduceIte]
    refine WP.spec_mono (do_fault_transfer_full hE hP s a σ hR ht hd htd hks hkd' hf hmsg (by simp) hty0
      (by rw [mask52]; decide) hmr hu' bdg
      (set_mrs_fault_tmoSC hH hP0 s a σ hX ht hd hks hkd hf rfl hsc0 hscC hky hmax (htu a) hrw0 hmr)) ?_
    rintro s' ⟨σ', h1, h2⟩
    exact post s' ⟨σ', hspec.trans h1, h2⟩

end Xfer

end

end Fl4Proofs.P3.Ipc
