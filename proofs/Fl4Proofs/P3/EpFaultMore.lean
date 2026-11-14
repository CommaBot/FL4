/-
P3 (DESIGN.md §9), endpoints: the remaining fault messages (user exception,
timeout without a scheduling context, VM fault) and the fault branch of
`do_ipc_transfer`.

`copy_mrs_fault_rel` is `faults::copy_mrs_fault` for any register list whose
FL4 slice is the list's `regIdx` image (`SYSCALL_MESSAGE`,
`EXCEPTION_MESSAGE`).
-/
import Fl4Proofs.P3.EpFaultUs
import Fl4Proofs.P3.Ep
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Endp
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section Spec
open Fl4Spec

/-- The fault message of a user exception (l4v `make_fault_msg`). -/
def ueMsg (regs : Register → Word) (e c : Word) : List Word := exceptionMessage.map regs ++ [e, c]

theorem makeFaultMsg_user {σ : State Unit} {t : ObjRef} {x : Tcb} (hk : σ.kheap t = some (.tcb x)) (e c : Word) :
    makeFaultMsg (Z := Unit) (.userException e c) t σ =
      ({((3, ueMsg x.tcbArch.tcbContext.userRegs e c), σ)}, False) := by
  rw [makeFaultMsg, nd_bind_one (asUser_read_eq hk (mapM_getRegister _ _))]
  rfl

theorem ueMsg_length (regs : Register → Word) (e c : Word) : (ueMsg regs e c).length = 5 := rfl

theorem makeFaultMsg_timeout {σ : State Unit} {t : ObjRef} {x : Tcb} (hk : σ.kheap t = some (.tcb x))
    (hsc : x.tcbSchedContext = none) (b : Word) :
    makeFaultMsg (Z := Unit) (.timeout b) t σ = ({((5, [b]), σ)}, False) := by
  rw [makeFaultMsg]
  show (NonDet.getsThe _ >>= _) σ = _
  rw [nd_bind_one (getTcb_eq hk), hsc]
  rfl

/-- The fault message of a VM fault (l4v `make_arch_fault_msg`). -/
def vmMsg (pc a : Word) (d : List Word) : List Word := pc :: a :: d

theorem makeFaultMsg_vm {σ : State Unit} {t : ObjRef} {x : Tcb} (hk : σ.kheap t = some (.tcb x))
    (a : VSpaceRef) (d : List Word) :
    makeFaultMsg (Z := Unit) (.archFault (.vmFault a d)) t σ =
      ({((6, vmMsg (x.tcbArch.tcbContext.userRegs .faultIP) a d), σ)}, False) := by
  rw [makeFaultMsg, makeArchFaultMsg]
  rw [show getRestartPC = getRegister .faultIP from rfl, nd_bind_one (asUser_getRegister_eq hk .faultIP)]
  rfl

end Spec

theorem exc_slice_val : (Array.to_slice faults.EXCEPTION_MESSAGE).val = Fl4Spec.exceptionMessage.map regIdx := by
  unfold faults.EXCEPTION_MESSAGE layout.reg.FAULT_IP layout.reg.RSP layout.reg.FLAGS
  rfl

theorem getElem_regs {sl : List U64} {rl : List Fl4Spec.Register} (hsl : sl = rl.map regIdx) (k : Nat)
    (h : k < sl.length) : sl[k] = regIdx (rl[k]'(by subst hsl; simpa using h)) := by
  subst hsl; simp

theorem take_succ_map {α β : Type} (f : α → β) (l : List α) (k : Nat) (hk : k < l.length) :
    (l.take (k + 1)).map f = (l.take k).map f ++ [f l[k]] := by
  simp only [List.take_succ, List.getElem?_eq_getElem hk, Option.toList_some, List.map_append, List.map_cons,
    List.map_nil]

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {T E R : Set U64}
  {B : Set (U64 × Fl4Spec.Word)} {SR : S → Fl4Spec.State Unit → Prop}

theorem slice_len_val {sl : Slice U64} {rl : List Fl4Spec.Register} (hsl : sl.val = rl.map regIdx) :
    (Slice.len sl).val = rl.length := by
  simp [Slice.len, hsl]

/-- The first loop of `copy_mrs_fault`: message registers `0 .. min n 4`. -/
theorem copy_mrs_fault_loop0_rel (hH : EpHyps st T E R B SR) (hP : EPlaced T E R B) (s0 : S)
    (σ0 : Fl4Spec.State Unit) (hR : EpStateRel T E R B (L.mem s0) σ0) (hSR : SR s0 σ0)
    {snd rcv : U64} (hs : snd ∈ T) (hr : rcv ∈ T) (hne : snd ≠ rcv) {x0 : Fl4Spec.Tcb}
    (hk0 : σ0.kheap rcv.bv = some (.tcb x0)) {regs : Fl4Spec.Register → Fl4Spec.Word}
    (hreg : ∀ r, (L.mem s0 (regA snd (regIdx r))).bv = regs r) (p : Fl4Spec.ObjRef)
    {sl : Slice U64} {rl : List Fl4Spec.Register} (hsl : sl.val = rl.map regIdx) (hn : rl.length ≤ 120) :
    faults.copy_mrs_fault_loop0 st s0 snd rcv sl 0#usize ⦃ r =>
      r.2.val = min rl.length 4 ∧
      MrInv (L := L) T E R B SR s0 σ0 rcv x0 p r.1 ((rl.take r.2.val).map regs) ⦄ := by
  have hN : msg.N_MSG_REGISTERS.val = 4 := by unfold msg.N_MSG_REGISTERS; rfl
  have hlen := slice_len_val hsl
  unfold faults.copy_mrs_fault_loop0
  apply loop.spec_decr_nat (measure := fun x => 4 - x.2.val)
    (inv := fun x => x.2.val ≤ min rl.length 4 ∧
      MrInv (L := L) T E R B SR s0 σ0 rcv x0 p x.1 ((rl.take x.2.val).map regs))
  · rintro ⟨s', i⟩ ⟨hi4, hI⟩
    unfold faults.copy_mrs_fault_loop0.body
    simp only at hi4 hI ⊢
    by_cases h1 : i < Slice.len sl
    · have hin : i.val < rl.length := by have := us_lt_iff.1 h1; omega
      simp only [h1, ↓reduceIte]
      step as ⟨i2, hi2⟩
      have hi2v : i2.val = i.val := by rw [hi2]; exact cast_us i (by omega)
      by_cases h2 : i2 < msg.N_MSG_REGISTERS
      · have hi : i.val < 4 := by have := (gt_iff_val).1 h2; omega
        simp only [h2, ↓reduceIte]
        step as ⟨r, hr'⟩
        step as ⟨v, hv⟩
        step as ⟨i4, hi4'⟩
        have hi4v : i4.val = i.val := by rw [hi4']; exact cast_us i (by omega)
        refine WP.spec_bind (msg_register_spec i4 (by omega)) ?_
        rintro r5 rfl
        have hlen' : ((rl.take i.val).map regs).length = i.val := by simp; omega
        refine WP.spec_bind (set_reg_mr_inv (L := L) hH hP hr hI i4.val (by omega) (by omega) v) ?_
        rintro s1 hI1
        step as ⟨i6, hi6⟩
        have hi6v : i6.val = i.val + 1 := by simpa using hi6
        have hvb : v.bv = regs rl[i.val] := by
          rw [hv, hr', getElem_regs hsl, snd_word_eq hP hs hr hne hI.2.2 (a_reg (hP.tcb snd hs) _), hreg]
        refine ⟨by omega, ?_, by omega⟩
        rw [hi6v, take_succ_map regs rl i.val hin, ← hvb]
        exact hI1
      · simp only [h2, ↓reduceIte, WP.spec_ok]
        have hi : i.val = 4 := by
          have h2' : ¬ i.val < 4 := fun h => h2 ((gt_iff_val).2 (by rw [hN]; omega))
          omega
        exact ⟨by omega, hI⟩
    · simp only [h1, ↓reduceIte, WP.spec_ok]
      have : ¬ i.val < rl.length := fun h => h1 (us_lt_iff.2 (by omega))
      exact ⟨by omega, hI⟩
  · refine ⟨by simp, ?_⟩
    have := mrInv_init (L := L) (SR := SR) (B := B) hR hSR hk0 p
    simpa using this

/-- The second loop of `copy_mrs_fault`: message words `4 .. n`, in the
receiver's IPC buffer. -/
theorem copy_mrs_fault_loop1_rel (hH : EpHyps st T E R B SR) (hP : EPlaced T E R B) {s0 : S}
    {σ0 : Fl4Spec.State Unit} {snd rcv : U64} (hs : snd ∈ T) (hr : rcv ∈ T) (hne : snd ≠ rcv) {x0 : Fl4Spec.Tcb}
    {regs : Fl4Spec.Register → Fl4Spec.Word} (hreg : ∀ r, (L.mem s0 (regA snd (regIdx r))).bv = regs r)
    {rw : U64} {p : Fl4Spec.ObjRef} (hmr : BufMap B rw p)
    {sl : Slice U64} {rl : List Fl4Spec.Register} (hsl : sl.val = rl.map regIdx) (hn : rl.length ≤ 120)
    (s1 : S) (i0 : Usize) (hi0 : i0.val = min rl.length 4)
    (hI : MrInv (L := L) T E R B SR s0 σ0 rcv x0 p s1 ((rl.take i0.val).map regs)) :
    faults.copy_mrs_fault_loop1 st s1 snd sl rw i0 ⦃ s2 =>
      MrInv (L := L) T E R B SR s0 σ0 rcv x0 p s2 (rl.map regs) ⦄ := by
  have hlen := slice_len_val hsl
  unfold faults.copy_mrs_fault_loop1
  apply loop.spec_decr_nat (measure := fun x => rl.length - x.2.val)
    (inv := fun x => min rl.length 4 ≤ x.2.val ∧ x.2.val ≤ rl.length ∧
      MrInv (L := L) T E R B SR s0 σ0 rcv x0 p x.1 ((rl.take x.2.val).map regs))
  · rintro ⟨s', i⟩ ⟨h4, hle, hI'⟩
    unfold faults.copy_mrs_fault_loop1.body
    simp only at h4 hle hI' ⊢
    by_cases h1 : i < Slice.len sl
    · have hi : i.val < rl.length := by have := us_lt_iff.1 h1; omega
      simp only [h1, ↓reduceIte]
      step as ⟨r, hr'⟩
      step as ⟨v, hv⟩
      step as ⟨i3, hi3⟩
      step as ⟨i4, hi4⟩
      have hi4v : i4.val = i.val + 1 := by
        have h3v : i3.val = i.val := by rw [hi3]; exact cast_us i (by omega)
        rw [hi4]; simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits, h3v]; omega
      have hlen' : ((rl.take i.val).map regs).length = i.val := by simp; omega
      refine WP.spec_bind (buf_set_mr_inv (L := L) hH hP hmr hI' i4 (by omega) (by omega) (by omega) v) ?_
      rintro s3 hI3
      step as ⟨i5, hi5⟩
      have hi5v : i5.val = i.val + 1 := by simpa using hi5
      have hvb : v.bv = regs rl[i.val] := by
        rw [hv, hr', getElem_regs hsl, snd_word_eq hP hs hr hne hI'.2.2 (a_reg (hP.tcb snd hs) _), hreg]
      refine ⟨by omega, by omega, ?_, by omega⟩
      rw [hi5v, take_succ_map regs rl i.val hi, ← hvb]
      exact hI3
    · simp only [h1, ↓reduceIte, WP.spec_ok]
      have hi : i.val = rl.length := by
        have : ¬ i.val < rl.length := fun h => h1 (us_lt_iff.2 (by omega))
        omega
      rw [hi, List.take_of_length_le (le_refl _)] at hI'
      exact hI'
  · simp only [hi0]
    exact ⟨le_refl _, by omega, hi0 ▸ hI⟩

/-- **`copy_mrs_fault`** of the sender's registers `rl` into a receiver
with a mapped IPC buffer: message words `0 .. |rl|`. -/
theorem copy_mrs_fault_rel (hH : EpHyps st T E R B SR) (hP : EPlaced T E R B) (s : S)
    (σ : Fl4Spec.State Unit) (hR : EpStateRel T E R B (L.mem s) σ) (hSR : SR s σ)
    {snd rcv : U64} (hs : snd ∈ T) (hr : rcv ∈ T) (hne : snd ≠ rcv) {xr : Fl4Spec.Tcb}
    (hkr : σ.kheap rcv.bv = some (.tcb xr)) {regs : Fl4Spec.Register → Fl4Spec.Word}
    (hreg : ∀ r, (L.mem s (regA snd (regIdx r))).bv = regs r)
    {rw : U64} {p : Fl4Spec.ObjRef} (hrw0 : rw ≠ 0#u64) (hmr : BufMap B rw p)
    {sl : Slice U64} {rl : List Fl4Spec.Register} (hsl : sl.val = rl.map regIdx) (hn : rl.length ≤ 120) :
    faults.copy_mrs_fault st s snd rcv sl rw ⦃ s2 =>
      MrInv (L := L) T E R B SR s σ rcv xr p s2 (rl.map regs) ⦄ := by
  unfold faults.copy_mrs_fault
  refine WP.spec_bind (copy_mrs_fault_loop0_rel (L := L) hH hP s σ hR hSR hs hr hne hkr hreg p hsl hn) ?_
  rintro ⟨s1, i⟩ ⟨hi, hI⟩
  have hb : (rw != 0#u64) = true := by simp [hrw0]
  simp only [hb, ↓reduceIte]
  exact copy_mrs_fault_loop1_rel hH hP hs hr hne hreg hmr hsl hn s1 i hi hI

/-- The fault words of the sender, read before the message is written. -/
theorem fault_words {s : S} {σ : Fl4Spec.State Unit} (hR : EpStateRel T E R B (L.mem s) σ) {snd : U64}
    (hs : snd ∈ T) {xs : Fl4Spec.Tcb} (hks : σ.kheap snd.bv = some (.tcb xs)) :
    FaultRel (L.mem s) snd xs.tcbFault := (hR.at_tcb hs hks).faultR

/-- **`set_mrs_fault` of a user exception**. -/
theorem set_mrs_fault_user {A : Type} {ar : machine.Arch A} (hH : EpHyps st T E R B SR) (hP : EPlaced T E R B)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (hR : EpStateRel T E R B (L.mem s) σ) (hSR : SR s σ)
    {snd rcv : U64} (hs : snd ∈ T) (hr : rcv ∈ T) (hne : snd ≠ rcv) {xs xr : Fl4Spec.Tcb}
    (hks : σ.kheap snd.bv = some (.tcb xs)) (hkr : σ.kheap rcv.bv = some (.tcb xr))
    {e c : Fl4Spec.Word} (hf : xs.tcbFault = some (.userException e c))
    {rw : U64} {p : Fl4Spec.ObjRef} (hrw0 : rw ≠ 0#u64) (hmr : BufMap B rw p) :
    faults.set_mrs_fault st ar s a snd rcv rw ⦃ r =>
      r.1.val = (ueMsg xs.tcbArch.tcbContext.userRegs e c).length ∧
      MrInv (L := L) T E R B SR s σ rcv xr p r.2 (ueMsg xs.tcbArch.tcbContext.userRegs e c) ⦄ := by
  have hxs := hR.at_tcb hs hks
  have hfr := hxs.faultR
  unfold FaultRel at hfr
  rw [hf] at hfr
  obtain ⟨hty, hw0, hw1⟩ := hfr
  unfold faults.set_mrs_fault
  step as ⟨ty, hty'⟩
  step as ⟨w0, hw0'⟩
  step as ⟨w1, hw1'⟩
  step as ⟨w2, hw2'⟩
  step as ⟨pc, hpc'⟩
  subst hty' hw0' hw1' hw2' hpc'
  rw [hty, ite_eq_right_of_eq_false _ _ (by unfold fl4_abi.consts.fault.CapFault; decide),
    ite_eq_right_of_eq_false _ _ (by unfold fl4_abi.consts.fault.UnknownSyscall; decide),
    ite_eq_left_of_eq_true _ _ (eq_true (by unfold fl4_abi.consts.fault.UserException; rfl))]
  unfold lift
  apply ok_bind_spec
  refine WP.spec_bind (copy_mrs_fault_rel (L := L) hH hP s σ hR hSR hs hr hne hkr (fun r => hxs.regs r)
    hrw0 hmr exc_slice_val (by decide)) ?_
  rintro s2 hI2
  refine WP.spec_bind (set_mr_inv (L := L) hH hP hr hkr hrw0 hmr hI2 3#u64 (by simp [Fl4Spec.exceptionMessage])
    (by decide) (L.mem s (tFw0A snd))) ?_
  rintro ⟨k3, s3⟩ ⟨-, hI3⟩
  refine WP.spec_mono (set_mr_inv (L := L) hH hP hr hkr hrw0 hmr hI3 4#u64 (by simp [Fl4Spec.exceptionMessage])
    (by decide) (L.mem s (tFw1A snd))) ?_
  rintro ⟨k4, s4⟩ ⟨hk4, hI4⟩
  rw [hw0, hw1, List.append_assoc] at hI4
  exact ⟨by rw [ueMsg_length]; simpa using hk4, hI4⟩

/-- **`set_mrs_fault` of a timeout fault** of a sender without a
scheduling context. -/
theorem set_mrs_fault_timeout {A : Type} {ar : machine.Arch A} (hH : EpHyps st T E R B SR) (hP : EPlaced T E R B)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (hR : EpStateRel T E R B (L.mem s) σ) (hSR : SR s σ)
    {snd rcv : U64} (hs : snd ∈ T) (hr : rcv ∈ T) {xs xr : Fl4Spec.Tcb}
    (hks : σ.kheap snd.bv = some (.tcb xs)) (hkr : σ.kheap rcv.bv = some (.tcb xr))
    {b : Fl4Spec.Word} (hf : xs.tcbFault = some (.timeout b)) (hsc : L.mem s (scA snd) = 0#u64)
    {rw : U64} {p : Fl4Spec.ObjRef} (hrw0 : rw ≠ 0#u64) (hmr : BufMap B rw p) :
    faults.set_mrs_fault st ar s a snd rcv rw ⦃ r =>
      r.1.val = [b].length ∧ MrInv (L := L) T E R B SR s σ rcv xr p r.2 [b] ⦄ := by
  have hxs := hR.at_tcb hs hks
  have hfr := hxs.faultR
  unfold FaultRel at hfr
  rw [hf] at hfr
  obtain ⟨hty, hw0⟩ := hfr
  unfold faults.set_mrs_fault
  step as ⟨ty, hty'⟩
  step as ⟨w0, hw0'⟩
  step as ⟨w1, hw1'⟩
  step as ⟨w2, hw2'⟩
  step as ⟨pc, hpc'⟩
  subst hty' hw0' hw1' hw2' hpc'
  rw [hty, ite_eq_right_of_eq_false _ _ (by unfold fl4_abi.consts.fault.CapFault; decide),
    ite_eq_right_of_eq_false _ _ (by unfold fl4_abi.consts.fault.UnknownSyscall; decide),
    ite_eq_right_of_eq_false _ _ (by unfold fl4_abi.consts.fault.UserException; decide),
    ite_eq_left_of_eq_true _ _ (eq_true (by unfold fl4_abi.consts.fault.Timeout; rfl))]
  step with obj.Tcb.sc.spec as ⟨i, hi⟩
  subst hi
  unfold obj.Sc.is_null
  apply ok_bind_spec
  simp only [hsc, decide_true, ↓reduceIte]
  refine WP.spec_mono (set_mr_inv (L := L) hH hP hr hkr hrw0 hmr (mrInv_init hR hSR hkr p) 0#u64 rfl
    (by decide) (L.mem s (tFw0A snd))) ?_
  rintro ⟨k, s1⟩ ⟨hk, hI⟩
  rw [hw0, List.nil_append] at hI
  exact ⟨by simpa using hk, hI⟩

/-- **`set_mrs_fault` of a VM fault**. -/
theorem set_mrs_fault_vm {A : Type} {ar : machine.Arch A} (hH : EpHyps st T E R B SR) (hP : EPlaced T E R B)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (hR : EpStateRel T E R B (L.mem s) σ) (hSR : SR s σ)
    {snd rcv : U64} (hs : snd ∈ T) (hr : rcv ∈ T) {xs xr : Fl4Spec.Tcb}
    (hks : σ.kheap snd.bv = some (.tcb xs)) (hkr : σ.kheap rcv.bv = some (.tcb xr))
    {va : Fl4Spec.VSpaceRef} {d : List Fl4Spec.Word} (hf : xs.tcbFault = some (.archFault (.vmFault va d)))
    {rw : U64} {p : Fl4Spec.ObjRef} (hrw0 : rw ≠ 0#u64) (hmr : BufMap B rw p) :
    faults.set_mrs_fault st ar s a snd rcv rw ⦃ r =>
      r.1.val = (vmMsg (xs.tcbArch.tcbContext.userRegs .faultIP) va d).length ∧
      MrInv (L := L) T E R B SR s σ rcv xr p r.2 (vmMsg (xs.tcbArch.tcbContext.userRegs .faultIP) va d) ⦄ := by
  have hxs := hR.at_tcb hs hks
  have hfr := hxs.faultR
  unfold FaultRel at hfr
  rw [hf] at hfr
  obtain ⟨hty, hw0, hd⟩ := hfr
  have hset := fun {s' : S} {ms : List Fl4Spec.Word} (h : MrInv (L := L) T E R B SR s σ rcv xr p s' ms) =>
    set_mr_inv (L := L) hH hP hr hkr hrw0 hmr h
  have hpc : (L.mem s (regA snd layout.reg.FAULT_IP)).bv = xs.tcbArch.tcbContext.userRegs .faultIP := by
    rw [show layout.reg.FAULT_IP = regIdx .faultIP by unfold layout.reg.FAULT_IP; rfl]; exact hxs.regs _
  unfold faults.set_mrs_fault
  step as ⟨ty, hty'⟩
  step as ⟨w0, hw0'⟩
  step as ⟨w1, hw1'⟩
  step as ⟨w2, hw2'⟩
  step as ⟨pc, hpc'⟩
  subst hty' hw0' hw1' hw2' hpc'
  rw [hty, ite_eq_right_of_eq_false _ _ (by unfold fl4_abi.consts.fault.CapFault; decide),
    ite_eq_right_of_eq_false _ _ (by unfold fl4_abi.consts.fault.UnknownSyscall; decide),
    ite_eq_right_of_eq_false _ _ (by unfold fl4_abi.consts.fault.UserException; decide),
    ite_eq_right_of_eq_false _ _ (by unfold fl4_abi.consts.fault.Timeout; decide),
    ite_eq_right_of_eq_false _ _ (by unfold fl4_abi.consts.fault.DebugException; decide),
    ite_eq_left_of_eq_true _ _ (eq_true (by unfold fl4_abi.consts.fault.VMFault; rfl))]
  refine WP.spec_bind (hset (mrInv_init hR hSR hkr p) 0#u64 rfl (by decide) _) ?_
  rintro ⟨_, s1⟩ ⟨-, hI1⟩
  refine WP.spec_bind (hset hI1 1#u64 rfl (by decide) _) ?_
  rintro ⟨_, s2⟩ ⟨-, hI2⟩
  refine WP.spec_bind (hset hI2 2#u64 rfl (by decide) _) ?_
  rintro ⟨_, s3⟩ ⟨-, hI3⟩
  refine WP.spec_mono (hset hI3 3#u64 rfl (by decide) _) ?_
  rintro ⟨k, s4⟩ ⟨hk, hI4⟩
  have hl : [(L.mem s (regA snd layout.reg.FAULT_IP)).bv] ++ [(L.mem s (tFw0A snd)).bv] ++
      [(L.mem s (tFw2A snd)).bv] ++ [(L.mem s (tFw1A snd)).bv] =
      vmMsg (xs.tcbArch.tcbContext.userRegs .faultIP) va d := by
    rw [hpc, hw0, hd]; rfl
  rw [List.nil_append, hl] at hI4
  exact ⟨by rw [← hl]; simpa using hk, hI4⟩

/-- The fault kinds whose transfer is proved: all but a timeout of a sender
with a scheduling context (whose message carries the consumed time, through
`schedcontext::update_consumed`). -/
def FaultOK (s : S) (snd : U64) (x : Fl4Spec.Tcb) : Fl4Spec.Fault → Prop
  | .timeout _ => x.tcbSchedContext = none ∧ L.mem s (scA snd) = 0#u64
  | _ => True

/-- **`do_fault_transfer`** of any fault but a timeout with a scheduling
context, into a receiver with a mapped IPC buffer, refines l4v
`do_fault_transfer`. -/
theorem do_fault_transfer_rel {A : Type} {ar : machine.Arch A} (hH : EpHyps st T E R B SR) (hP : EPlaced T E R B)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (hR : EpStateRel T E R B (L.mem s) σ) (hSR : SR s σ)
    {snd rcv : U64} (hs : snd ∈ T) (hr : rcv ∈ T) (hne : snd ≠ rcv) {xs xr : Fl4Spec.Tcb}
    (hks : σ.kheap snd.bv = some (.tcb xs)) (hkr : σ.kheap rcv.bv = some (.tcb xr))
    {f : Fl4Spec.Fault} (hf : xs.tcbFault = some f) (hok : FaultOK (L := L) s snd xs f)
    {rw : U64} {p : Fl4Spec.ObjRef} (hrw0 : rw ≠ 0#u64) (hmr : BufMap B rw p)
    (hu : ∀ k, k < 128 → Fl4Spec.inUserFrame (bufAddr p k) σ) (badge : U64) :
    ipc.do_fault_transfer st ar s a badge snd rcv rw ⦃ s' => ∃ σ',
      Fl4Spec.doFaultTransfer (Z := Unit) badge.bv snd.bv rcv.bv (some p) σ = ({((), σ')}, False) ∧
      EpStateRel T E R B (L.mem s') σ' ∧ SR s' σ' ∧
      Agree (L.mem s) (L.mem s') (fun b => ¬ RcvReg rcv b ∧ ¬ BufW B b) ∧
      (∀ q, q ≠ rcv.bv → σ'.kheap q = σ.kheap q) ∧
      ∃ x', σ'.kheap rcv.bv = some (.tcb x') ∧ x'.tcbState = xr.tcbState ⦄ := by
  have hfr := (hR.at_tcb hs hks).faultR
  unfold FaultRel at hfr
  rw [hf] at hfr
  cases f with
  | capFault c rp lf =>
    exact do_fault_transfer_full hH hP s a σ hR hs hr hne hks hkr hf (makeFaultMsg_cap hks c rp lf)
      (by have := msgFromLookupFailure_len lf; simp [capFaultMsg]; omega) hfr.1 (by rw [mask52]; decide) hmr hu
      badge (set_mrs_fault_cap (ar := ar) hH hP s a σ hR hSR hs hr hne hks hkr hf hrw0 hmr)
  | unknownSyscallException n =>
    exact do_fault_transfer_full hH hP s a σ hR hs hr hne hks hkr hf (makeFaultMsg_unknown hks n)
      (by rw [usMsg_length]; omega) hfr.1 (by rw [mask52]; decide) hmr hu badge
      (set_mrs_fault_unknown (ar := ar) hH hP s a σ hR hSR hs hr hne hks hkr hf hrw0 hmr)
  | userException e c =>
    exact do_fault_transfer_full hH hP s a σ hR hs hr hne hks hkr hf (makeFaultMsg_user hks e c)
      (by rw [ueMsg_length]; omega) hfr.1 (by rw [mask52]; decide) hmr hu badge
      (set_mrs_fault_user (ar := ar) hH hP s a σ hR hSR hs hr hne hks hkr hf hrw0 hmr)
  | timeout b =>
    exact do_fault_transfer_full hH hP s a σ hR hs hr hne hks hkr hf (makeFaultMsg_timeout hks hok.1 b)
      (by simp) hfr.1 (by rw [mask52]; decide) hmr hu badge
      (set_mrs_fault_timeout (ar := ar) hH hP s a σ hR hSR hs hr hks hkr hf hok.2 hrw0 hmr)
  | archFault af =>
    cases af with
    | vmFault va d =>
      have hd := hfr.2.2
      exact do_fault_transfer_full hH hP s a σ hR hs hr hne hks hkr hf (makeFaultMsg_vm hks va d)
        (by rw [hd]; simp [vmMsg]) hfr.1 (by rw [mask52]; decide) hmr hu badge
        (set_mrs_fault_vm (ar := ar) hH hP s a σ hR hSR hs hr hks hkr hf hrw0 hmr)

/-- **`do_ipc_transfer` of a faulted sender** into a receiver with an IPC
buffer refines l4v `do_ipc_transfer` (its `do_fault_transfer` branch). -/
theorem do_ipc_transfer_fault {A : Type} {ar : machine.Arch A} (hH : EpHyps st T E R B SR)
    (hBm : EpBufMapHyps st T E R B SR) (hP : EPlaced T E R B)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (hR : EpStateRel T E R B (L.mem s) σ) (hSR : SR s σ)
    {snd rcv : U64} (hs : snd ∈ T) (hr : rcv ∈ T) (hne : snd ≠ rcv) {xs xr : Fl4Spec.Tcb}
    (hks : σ.kheap snd.bv = some (.tcb xs)) (hkr : σ.kheap rcv.bv = some (.tcb xr))
    {f : Fl4Spec.Fault} (hf : xs.tcbFault = some f) (hok : FaultOK (L := L) s snd xs f)
    {rp : Fl4Spec.ObjRef} (hrb : ipcBufOf true xr = some rp) (ep badge : U64) (grant : Bool) :
    ipc.do_ipc_transfer st ar s a snd ep badge grant rcv ⦃ s' => ∃ σ',
      Fl4Spec.doIpcTransfer (Z := Unit) snd.bv (some ep.bv) badge.bv grant rcv.bv σ = ({((), σ')}, False) ∧
      EpStateRel T E R B (L.mem s') σ' ∧ SR s' σ' ∧
      Agree (L.mem s) (L.mem s') (fun b => ¬ RcvReg rcv b ∧ ¬ BufW B b) ∧
      (∀ q, q ≠ rcv.bv → σ'.kheap q = σ.kheap q) ∧
      ∃ x', σ'.kheap rcv.bv = some (.tcb x') ∧ x'.tcbState = xr.tcbState ⦄ := by
  have hxs := hR.at_tcb hs hks
  have hu := hBm.frame s σ rcv xr rp hR hSR hr hkr hrb
  have hspec : Fl4Spec.doIpcTransfer (Z := Unit) snd.bv (some ep.bv) badge.bv grant rcv.bv σ =
      Fl4Spec.doFaultTransfer (Z := Unit) badge.bv snd.bv rcv.bv (some rp) σ := by
    unfold Fl4Spec.doIpcTransfer
    rw [nd_bind_one (lookupIpcBuffer_eq hkr true), hrb, nd_bind_one (threadGet_eq _ hks), hf]
  unfold ipc.do_ipc_transfer
  refine WP.spec_bind (hBm.lookupMap s σ rcv xr true rp hR hSR hr hkr hrb) ?_
  rintro rw ⟨hrw0, hmr⟩
  step as ⟨ft, hft⟩
  have hft0 : ¬ ft = fl4_abi.consts.fault.NullFault := by
    intro h
    have : L.mem s (tFaultA snd) = 0#u64 := by rw [← hft, h]; unfold fl4_abi.consts.fault.NullFault; rfl
    rw [hxs.fault0.1 this] at hf; cases hf
  simp only [hft0, ↓reduceIte]
  refine WP.spec_mono (do_fault_transfer_rel hH hP s a σ hR hSR hs hr hne hks hkr hf hok hrw0 hmr hu badge) ?_
  rintro s' ⟨σ', h1, h2⟩
  exact ⟨σ', hspec.trans h1, h2⟩

end

end

end Fl4Proofs.P3.Endp
