/-
P3 (DESIGN.md §9), endpoints: the fault message of an unknown-syscall fault
(l4v `make_fault_msg (UnknownSyscallException n)`, FL4
`faults::set_mrs_fault` / `faults::copy_mrs_fault` over `SYSCALL_MESSAGE`).
-/
import Fl4Proofs.P3.EpFault
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Endp
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section Spec
open Fl4Spec

theorem mapM_getRegister (uc : UserContext) : ∀ rs : List Register,
    NonDet.mapM getRegister rs uc = ({(rs.map uc.userRegs, uc)}, False)
  | [] => rfl
  | r :: rs => by
    unfold NonDet.mapM
    rw [nd_bind_one' (show getRegister r uc = ({(uc.userRegs r, uc)}, False) from rfl),
      nd_bind_one' (mapM_getRegister uc rs)]
    rfl

/-- `as_user` of a computation that only reads the user context. -/
theorem asUser_read_eq {α : Type} {σ : State Unit} {t : ObjRef} {x : Tcb} (hk : σ.kheap t = some (.tcb x))
    {f : UserMonad α} {a : α}
    (hf : f (archTcbContextGet x.tcbArch) = ({(a, archTcbContextGet x.tcbArch)}, False)) :
    asUser (Z := Unit) t f σ = ({(a, σ)}, False) := by
  unfold asUser
  show (NonDet.getsThe _ >>= _) σ = _
  rw [nd_bind_one (getTcb_eq hk)]
  show ((pure _ : NonDet (State Unit) UserContext) >>= _) σ = _
  rw [nd_pure_bind']
  show (NonDet.selectF _ >>= _) σ = _
  rw [nd_bind_one (show NonDet.selectF (σ := State Unit) (f (archTcbContextGet x.tcbArch)) σ =
      (({((a, archTcbContextGet x.tcbArch), σ)}), False) by
    rw [hf]; simp only [NonDet.selectF]
    ext ⟨a', b⟩ <;> simp)]
  show ((pure _ : NonDet (State Unit) Tcb) >>= _) σ = _
  rw [nd_pure_bind']
  have hx : ({ x with tcbArch := archTcbContextSet (archTcbContextGet x.tcbArch) x.tcbArch } : Tcb) = x := rfl
  rw [hx]
  refine (nd_bind_one (setObject_eq (o' := KernelObject.tcb x) hk rfl) _).trans ?_
  rw [updK_self hk]; rfl

/-- The fault message of an unknown-syscall fault (l4v `make_fault_msg`):
the registers of `syscallMessage`, then the syscall number. -/
def usMsg (regs : Register → Word) (n : Word) : List Word := syscallMessage.map regs ++ [n]

theorem makeFaultMsg_unknown {σ : State Unit} {t : ObjRef} {x : Tcb} (hk : σ.kheap t = some (.tcb x)) (n : Word) :
    makeFaultMsg (Z := Unit) (.unknownSyscallException n) t σ =
      ({((2, usMsg x.tcbArch.tcbContext.userRegs n), σ)}, False) := by
  rw [makeFaultMsg, nd_bind_one (asUser_read_eq hk (mapM_getRegister _ _))]
  rfl

theorem usMsg_length (regs : Register → Word) (n : Word) : (usMsg regs n).length = 19 := by
  simp [usMsg, syscallMessage, Register.raxToR15]

end Spec

/-- FL4's `SYSCALL_MESSAGE` is l4v's `syscallMessage`. -/
theorem syscall_slice_val : (Array.to_slice faults.SYSCALL_MESSAGE).val = Fl4Spec.syscallMessage.map regIdx := by
  unfold faults.SYSCALL_MESSAGE layout.reg.RAX layout.reg.RBX layout.reg.RCX layout.reg.RDX layout.reg.RSI
    layout.reg.RDI layout.reg.RBP layout.reg.R8 layout.reg.R9 layout.reg.R10 layout.reg.R11 layout.reg.R12
    layout.reg.R13 layout.reg.R14 layout.reg.R15 layout.reg.FAULT_IP layout.reg.RSP layout.reg.FLAGS
  rfl

theorem syscall_len : (Fl4Spec.syscallMessage).length = 18 := rfl

theorem syscall_slice_len : (Slice.len (Array.to_slice faults.SYSCALL_MESSAGE)).val = 18 := by
  simp [Slice.len, syscall_slice_val, syscall_len]

theorem syscall_get (k : Nat) (hk : k < 18) :
    (Fl4Spec.syscallMessage.map regIdx)[k]! = regIdx Fl4Spec.syscallMessage[k]! := by
  interval_cases k <;> rfl

theorem syscall_take_succ (regs : Fl4Spec.Register → Fl4Spec.Word) (k : Nat) (hk : k < 18) :
    (Fl4Spec.syscallMessage.take (k + 1)).map regs =
      (Fl4Spec.syscallMessage.take k).map regs ++ [regs Fl4Spec.syscallMessage[k]!] := by
  interval_cases k <;> rfl

theorem us_lt_iff {a b : Usize} : a < b ↔ a.val < b.val := by simp [UScalar.lt_equiv]

theorem cast_us (i : Usize) (h : i.val < 2 ^ 32) : (UScalar.cast .U64 i).val = i.val := by
  rw [UScalar.cast_val_eq]; exact Nat.mod_eq_of_lt (by simp; omega)

theorem syscall_slice_length : (Array.to_slice faults.SYSCALL_MESSAGE).val.length = 18 := by
  rw [syscall_slice_val, List.length_map, syscall_len]

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {T E R : Set U64}
  {B : Set (U64 × Fl4Spec.Word)} {SR : S → Fl4Spec.State Unit → Prop}

/-- Writing message register `k < 4` of the receiver. -/
theorem set_reg_mr_inv (hH : EpHyps st T E R B SR) (hP : EPlaced T E R B) {s0 : S} {σ0 : Fl4Spec.State Unit}
    {rcv : U64} (hr : rcv ∈ T) {x0 : Fl4Spec.Tcb} {p : Fl4Spec.ObjRef} {s : S} {ms : List Fl4Spec.Word}
    (hI : MrInv (L := L) T E R B SR s0 σ0 rcv x0 p s ms) (k : Nat) (hk : k = ms.length) (hk4 : k < 4) (v : U64) :
    obj.Tcb.set_reg st rcv s (regIdx (mrIdx k)) v ⦃ s1 => MrInv (L := L) T E R B SR s0 σ0 rcv x0 p s1 (ms ++ [v.bv]) ⦄ := by
  have hra := hP.tcb rcv hr
  have hks : (mrState σ0 rcv.bv x0 p ms).kheap rcv.bv =
      some (.tcb (withRegs x0 (mrRegs x0.tcbArch.tcbContext.userRegs ms))) := by
    simp [mrState, setUm]
  refine WP.spec_mono (obj.Tcb.set_reg.spec s rcv _ v) ?_
  rintro s1 rfl
  obtain ⟨hR1, hW1, hS1⟩ := write_reg_rel hP s _ hI.1 hr hks (mrIdx k) v
  rw [mrState_snoc_lt _ _ _ _ _ _ k hk (by omega)] at hR1 hS1
  have ha := a_reg hra (mrIdx k)
  exact ⟨hR1, hH.stable _ _ _ _ hI.2.1 hW1 hS1, fun b hb hn =>
    (agree_wr (L := L) (s := s) (v := v) ha.1 b hb (fun h => hn.1 ⟨_, h⟩)).trans (hI.2.2 b hb hn)⟩

/-- Writing buffer word `j = |ms| + 1` (message word `|ms| ≥ 4`). -/
theorem buf_set_mr_inv (hH : EpHyps st T E R B SR) (hP : EPlaced T E R B) {s0 : S} {σ0 : Fl4Spec.State Unit}
    {rcv : U64} {x0 : Fl4Spec.Tcb} {rw : U64} {p : Fl4Spec.ObjRef} (hmr : BufMap B rw p) {s : S}
    {ms : List Fl4Spec.Word} (hI : MrInv (L := L) T E R B SR s0 σ0 rcv x0 p s ms) (j : U64)
    (hj : j.val = ms.length + 1) (h4 : 4 ≤ ms.length) (h120 : ms.length < 120) (v : U64) :
    msg.buf_set st s rw j v ⦃ s1 => MrInv (L := L) T E R B SR s0 σ0 rcv x0 p s1 (ms ++ [v.bv]) ⦄ := by
  refine WP.spec_mono (msg.buf_set.spec s rw j v) ?_
  rintro s1 rfl
  have hw := hmr j (by omega)
  have hal := (hP.balign _ hw).1
  have hag := agree_wr (L := L) (s := s) (v := v) hal
  have hR1 := hI.1.upd_buf hP hw v hag (rd_wr_eq hal)
  simp only [hj] at hR1
  rw [mrState_snoc_ge _ _ _ _ _ _ h4 h120] at hR1
  have hW : WritesIn st s (L.wr s (fl4BufA rw j) v) (EWrite T E R B) :=
    (writesIn_wr hal).mono fun b hb => Or.inr (Or.inr (Or.inr ⟨_, hw, hb⟩))
  have hS1 := hH.stable _ _ _ _ hI.2.1 hW (EpStep.setUm' _ (storeMem (mrState σ0 rcv.bv x0 p ms).machineState.underlyingMemory
    (bufAddr p (ms.length + 1)) v.bv))
  rw [mrState_snoc_ge _ _ _ _ _ _ h4 h120] at hS1
  exact ⟨hR1, hS1, fun b hb hn => (hag b hb (fun h => hn.2 ⟨_, hw, UScalar.eq_of_val_eq h⟩)).trans (hI.2.2 b hb hn)⟩

/-- The sender's register `SYSCALL_MESSAGE[k]` while the message is written. -/
theorem snd_sys_reg (hP : EPlaced T E R B) {s0 s : S} {snd rcv : U64} (hs : snd ∈ T) (hr : rcv ∈ T)
    (hne : snd ≠ rcv) (hA : Agree (L.mem s0) (L.mem s) (fun b => ¬ RcvReg rcv b ∧ ¬ BufW B b))
    {regs : Fl4Spec.Register → Fl4Spec.Word} (hreg : ∀ r, (L.mem s0 (regA snd (regIdx r))).bv = regs r)
    (k : Nat) (hk : k < 18) :
    (L.mem s (regA snd ((Array.to_slice faults.SYSCALL_MESSAGE).val[k]!))).bv = regs Fl4Spec.syscallMessage[k]! := by
  rw [syscall_slice_val, syscall_get k hk, snd_word_eq hP hs hr hne hA (a_reg (hP.tcb snd hs) _), hreg]

/-- The first loop of `copy_mrs_fault` over `SYSCALL_MESSAGE`: message
registers 0..3. -/
theorem copy_mrs_fault_loop0_sys (hH : EpHyps st T E R B SR) (hP : EPlaced T E R B) (s0 : S)
    (σ0 : Fl4Spec.State Unit) (hR : EpStateRel T E R B (L.mem s0) σ0) (hSR : SR s0 σ0)
    {snd rcv : U64} (hs : snd ∈ T) (hr : rcv ∈ T) (hne : snd ≠ rcv) {x0 : Fl4Spec.Tcb}
    (hk0 : σ0.kheap rcv.bv = some (.tcb x0)) {regs : Fl4Spec.Register → Fl4Spec.Word}
    (hreg : ∀ r, (L.mem s0 (regA snd (regIdx r))).bv = regs r) (p : Fl4Spec.ObjRef) :
    faults.copy_mrs_fault_loop0 st s0 snd rcv (Array.to_slice faults.SYSCALL_MESSAGE) 0#usize ⦃ r =>
      r.2.val = 4 ∧
      MrInv (L := L) T E R B SR s0 σ0 rcv x0 p r.1 ((Fl4Spec.syscallMessage.take 4).map regs) ⦄ := by
  have hN : msg.N_MSG_REGISTERS.val = 4 := by unfold msg.N_MSG_REGISTERS; rfl
  unfold faults.copy_mrs_fault_loop0
  apply loop.spec_decr_nat (measure := fun x => 4 - x.2.val)
    (inv := fun x => x.2.val ≤ 4 ∧
      MrInv (L := L) T E R B SR s0 σ0 rcv x0 p x.1 ((Fl4Spec.syscallMessage.take x.2.val).map regs))
  · rintro ⟨s', i⟩ ⟨hi4, hI⟩
    unfold faults.copy_mrs_fault_loop0.body
    simp only at hi4 hI ⊢
    have h1 : i < Slice.len (Array.to_slice faults.SYSCALL_MESSAGE) := us_lt_iff.2 (by have := syscall_slice_len; omega)
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
      have hlen : ((Fl4Spec.syscallMessage.take i.val).map regs).length = i.val := by
        simp [syscall_len]; omega
      refine WP.spec_bind (set_reg_mr_inv (L := L) hH hP hr hI i4.val (by omega) (by omega) v) ?_
      rintro s1 hI1
      step as ⟨i6, hi6⟩
      have hi6v : i6.val = i.val + 1 := by simpa using hi6
      have hvb : v.bv = regs Fl4Spec.syscallMessage[i.val]! := by
        have h := snd_sys_reg hP hs hr hne hI.2.2 hreg i.val (by omega)
        rw [getElem!_pos (Array.to_slice faults.SYSCALL_MESSAGE).val i.val (by rw [syscall_slice_length]; omega)] at h
        rw [hv, hr']; exact h
      refine ⟨by omega, ?_, by omega⟩
      rw [hi6v, syscall_take_succ regs i.val (by omega), ← hvb]
      exact hI1
    · simp only [h2, ↓reduceIte, WP.spec_ok]
      have hi : i.val = 4 := by
        have h2' : ¬ i.val < 4 := fun h => h2 ((gt_iff_val).2 (by rw [hN]; omega))
        omega
      exact ⟨hi, hi ▸ hI⟩
  · refine ⟨by simp, ?_⟩
    have := mrInv_init (L := L) (SR := SR) (B := B) hR hSR hk0 p
    simpa using this

/-- The second loop of `copy_mrs_fault` over `SYSCALL_MESSAGE`: message
words 4..17, in the receiver's IPC buffer. -/
theorem copy_mrs_fault_loop1_sys (hH : EpHyps st T E R B SR) (hP : EPlaced T E R B) {s0 : S}
    {σ0 : Fl4Spec.State Unit} {snd rcv : U64} (hs : snd ∈ T) (hr : rcv ∈ T) (hne : snd ≠ rcv) {x0 : Fl4Spec.Tcb}
    {regs : Fl4Spec.Register → Fl4Spec.Word} (hreg : ∀ r, (L.mem s0 (regA snd (regIdx r))).bv = regs r)
    {rw : U64} {p : Fl4Spec.ObjRef} (hmr : BufMap B rw p) (s1 : S) (i0 : Usize) (hi0 : i0.val = 4)
    (hI : MrInv (L := L) T E R B SR s0 σ0 rcv x0 p s1 ((Fl4Spec.syscallMessage.take 4).map regs)) :
    faults.copy_mrs_fault_loop1 st s1 snd (Array.to_slice faults.SYSCALL_MESSAGE) rw i0 ⦃ s2 =>
      MrInv (L := L) T E R B SR s0 σ0 rcv x0 p s2 (Fl4Spec.syscallMessage.map regs) ⦄ := by
  unfold faults.copy_mrs_fault_loop1
  apply loop.spec_decr_nat (measure := fun x => 18 - x.2.val)
    (inv := fun x => 4 ≤ x.2.val ∧ x.2.val ≤ 18 ∧
      MrInv (L := L) T E R B SR s0 σ0 rcv x0 p x.1 ((Fl4Spec.syscallMessage.take x.2.val).map regs))
  · rintro ⟨s', i⟩ ⟨h4, h18, hI'⟩
    unfold faults.copy_mrs_fault_loop1.body
    simp only at h4 h18 hI' ⊢
    by_cases h1 : i < Slice.len (Array.to_slice faults.SYSCALL_MESSAGE)
    · have hi : i.val < 18 := by have := us_lt_iff.1 h1; have := syscall_slice_len; omega
      simp only [h1, ↓reduceIte]
      step as ⟨r, hr'⟩
      step as ⟨v, hv⟩
      step as ⟨i3, hi3⟩
      step as ⟨i4, hi4⟩
      have hi4v : i4.val = i.val + 1 := by
        have h3v : i3.val = i.val := by rw [hi3]; exact cast_us i (by omega)
        rw [hi4]; simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits, h3v]; omega
      have hlen : ((Fl4Spec.syscallMessage.take i.val).map regs).length = i.val := by
        simp [syscall_len]; omega
      refine WP.spec_bind (buf_set_mr_inv (L := L) hH hP hmr hI' i4 (by omega) (by omega) (by omega) v) ?_
      rintro s3 hI3
      step as ⟨i5, hi5⟩
      have hi5v : i5.val = i.val + 1 := by simpa using hi5
      have hvb : v.bv = regs Fl4Spec.syscallMessage[i.val]! := by
        have h := snd_sys_reg hP hs hr hne hI'.2.2 hreg i.val hi
        rw [getElem!_pos (Array.to_slice faults.SYSCALL_MESSAGE).val i.val (by rw [syscall_slice_length]; exact hi)] at h
        rw [hv, hr']; exact h
      refine ⟨by omega, by omega, ?_, by omega⟩
      rw [hi5v, syscall_take_succ regs i.val hi, ← hvb]
      exact hI3
    · simp only [h1, ↓reduceIte, WP.spec_ok]
      have hi : i.val = 18 := by
        have : ¬ i.val < 18 := fun h => h1 (us_lt_iff.2 (by have := syscall_slice_len; omega))
        omega
      rw [hi, List.take_of_length_le (by rw [syscall_len])] at hI'
      exact hI'
  · simp only [hi0]
    exact ⟨by omega, by omega, hI⟩

/-- **`set_mrs_fault` of an unknown-syscall fault** into a receiver with a
mapped IPC buffer. -/
theorem set_mrs_fault_unknown {A : Type} {ar : machine.Arch A} (hH : EpHyps st T E R B SR) (hP : EPlaced T E R B)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (hR : EpStateRel T E R B (L.mem s) σ) (hSR : SR s σ)
    {snd rcv : U64} (hs : snd ∈ T) (hr : rcv ∈ T) (hne : snd ≠ rcv) {xs xr : Fl4Spec.Tcb}
    (hks : σ.kheap snd.bv = some (.tcb xs)) (hkr : σ.kheap rcv.bv = some (.tcb xr))
    {n : Fl4Spec.Word} (hf : xs.tcbFault = some (.unknownSyscallException n))
    {rw : U64} {p : Fl4Spec.ObjRef} (hrw0 : rw ≠ 0#u64) (hmr : BufMap B rw p) :
    faults.set_mrs_fault st ar s a snd rcv rw ⦃ r =>
      r.1.val = (usMsg xs.tcbArch.tcbContext.userRegs n).length ∧
      MrInv (L := L) T E R B SR s σ rcv xr p r.2 (usMsg xs.tcbArch.tcbContext.userRegs n) ⦄ := by
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
    ite_eq_left_of_eq_true _ _ (eq_true (by unfold fl4_abi.consts.fault.UnknownSyscall; rfl))]
  unfold lift
  apply ok_bind_spec
  have hreg : ∀ r, (L.mem s (regA snd (regIdx r))).bv = xs.tcbArch.tcbContext.userRegs r := fun r => hxs.regs r
  have hcopy : faults.copy_mrs_fault st s snd rcv (Array.to_slice faults.SYSCALL_MESSAGE) rw ⦃ s2 =>
      MrInv (L := L) T E R B SR s σ rcv xr p s2 (Fl4Spec.syscallMessage.map xs.tcbArch.tcbContext.userRegs) ⦄ := by
    unfold faults.copy_mrs_fault
    refine WP.spec_bind (copy_mrs_fault_loop0_sys (L := L) hH hP s σ hR hSR hs hr hne hkr hreg p) ?_
    rintro ⟨s1, i⟩ ⟨hi, hI⟩
    have hb : (rw != 0#u64) = true := by simp [hrw0]
    simp only [hb, ↓reduceIte]
    exact copy_mrs_fault_loop1_sys hH hP hs hr hne hreg hmr s1 i hi hI
  refine WP.spec_bind hcopy ?_
  rintro s2 hI2
  refine WP.spec_mono (set_mr_inv (L := L) hH hP hr hkr hrw0 hmr hI2 18#u64 (by simp [syscall_len]) (by decide)
    (L.mem s (tFw0A snd))) ?_
  rintro ⟨k, s3⟩ ⟨hk, hI3⟩
  rw [hw0] at hI3
  exact ⟨by rw [usMsg_length]; simpa using hk, hI3⟩

/-- **`do_fault_transfer` of an unknown-syscall fault** into a receiver with
a mapped IPC buffer refines l4v `do_fault_transfer`. -/
theorem do_fault_transfer_unknown {A : Type} {ar : machine.Arch A} (hH : EpHyps st T E R B SR)
    (hP : EPlaced T E R B) (s : S) (a : A) (σ : Fl4Spec.State Unit) (hR : EpStateRel T E R B (L.mem s) σ)
    (hSR : SR s σ) {snd rcv : U64} (hs : snd ∈ T) (hr : rcv ∈ T) (hne : snd ≠ rcv) {xs xr : Fl4Spec.Tcb}
    (hks : σ.kheap snd.bv = some (.tcb xs)) (hkr : σ.kheap rcv.bv = some (.tcb xr))
    {n : Fl4Spec.Word} (hf : xs.tcbFault = some (.unknownSyscallException n))
    {rw : U64} {p : Fl4Spec.ObjRef} (hrw0 : rw ≠ 0#u64) (hmr : BufMap B rw p)
    (hu : ∀ k, k < 128 → Fl4Spec.inUserFrame (bufAddr p k) σ) (badge : U64) :
    ipc.do_fault_transfer st ar s a badge snd rcv rw ⦃ s' => ∃ σ',
      Fl4Spec.doFaultTransfer (Z := Unit) badge.bv snd.bv rcv.bv (some p) σ = ({((), σ')}, False) ∧
      EpStateRel T E R B (L.mem s') σ' ∧ SR s' σ' ⦄ := by
  have hfr := (hR.at_tcb hs hks).faultR
  unfold FaultRel at hfr
  rw [hf] at hfr
  exact do_fault_transfer_gen hH hP s a σ hR hs hr hne hks hkr hf (makeFaultMsg_unknown hks n)
    (by rw [usMsg_length]; omega) hfr.1 (by rw [mask52]; decide) hmr hu badge
    (set_mrs_fault_unknown (ar := ar) hH hP s a σ hR hSR hs hr hne hks hkr hf hrw0 hmr)

end

end

end Fl4Proofs.P3.Endp
