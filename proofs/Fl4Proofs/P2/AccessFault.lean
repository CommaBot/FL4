/-
# P2: guarded-store lemmas for the fault message of the fault fast path

For the per-path obligation of `P2/PathObl.lean`, stated at each callee's
entry state with address-only hypotheses (they hold at every later state):

* `faults.set_fault.guardU`: an UnknownSyscall fault writes the thread's
  four fault words;
* `msg.buf_set.guard`, `msg.set_mr.guard`: a message register (receiver's
  register, or an IPC-buffer word below 128);
* `faults.copy_mrs_fault_loop0.guard`, `loop1.guard`, `copy_mrs_fault.guard`:
  reads of the sender's registers named by the list, writes of the
  receiver's message registers and buffer words;
* `faults.set_mrs_fault.guardU`: the UnknownSyscall message (sender's fault
  words and registers read, receiver's registers and buffer written).

Generic over the Arch instance. No premises.
-/
import Fl4Proofs.P2.AccessTail
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1 Fl4Proofs.P0.Consts

section
variable {S : Type} {st : machine.Store S} {R W : U64 → Prop} [L : LawfulStore st]

/-- Every register of `t` is in `P`. -/
def Regs (P : U64 → Prop) (t : U64) : Prop := ∀ r : U64, r.val < 384 → P (regA t r)

/-- The buffer's 128 words are in `P` (when there is a buffer). -/
def BufW (P : U64 → Prop) (buf : U64) : Prop :=
  buf ≠ 0#u64 → ∀ i : U64, i.val < 128 → P (core.num.U64.wrapping_add buf (core.num.U64.wrapping_mul i 8#u64))

theorem regs_of {P : U64 → Prop} {t : U64} (hT : TcbAddr t)
    (h : ∀ K : U64, 256 ≤ K.val → K.val < 3328 → P (core.num.U64.wrapping_add t K)) : Regs P t := by
  intro r hr
  obtain ⟨K, hK, e⟩ := regA_eq hT hr
  rw [e]; exact h K (by omega) (by omega)

theorem faults.set_fault.guardU (s : S) (t n : U64)
    (h0 : W (core.num.U64.wrapping_add t 3376#u64)) (h1 : W (core.num.U64.wrapping_add t 3384#u64))
    (h2 : W (core.num.U64.wrapping_add t 3392#u64)) (h3 : W (core.num.U64.wrapping_add t 3400#u64)) :
    faults.set_fault (PathObl.guard st R W) s t (error.Fault.UnknownSyscall n) =
      faults.set_fault st s t (error.Fault.UnknownSyscall n) := by
  unfold faults.set_fault
  simp only [bind_ok, Aeneas.Std.uncurry_apply_pair, obj.Tcb.set_fault_type.guard t _ _ h0,
    obj.Tcb.set_fault_w0.guard t _ _ h1, obj.Tcb.set_fault_w1.guard t _ _ h2, obj.Tcb.set_fault_w2.guard t _ _ h3]

theorem msg.buf_set.guard (s : S) (buf i v : U64)
    (h : W (core.num.U64.wrapping_add buf (core.num.U64.wrapping_mul i 8#u64))) :
    msg.buf_set (PathObl.guard st R W) s buf i v = msg.buf_set st s buf i v := by
  unfold msg.buf_set
  simp only [lift, bind_ok]
  exact guard_write h

theorem msg.set_mr.guard (s : S) (t buf i v : U64) (hi : i.val < 127) (hrw : Regs W t) (hbw : BufW W buf) :
    msg.set_mr (PathObl.guard st R W) s t buf i v = msg.set_mr st s t buf i v := by
  unfold msg.set_mr
  split
  · refine bind_guard_congr rfl fun rg hrg => ?_
    rw [obj.Tcb.set_reg.guard t s rg v (hrw rg (post_of_ok (msg.msg_register.lt _) hrg))]
  · split
    · rename_i h0
      simp only [lift, bind_ok]
      have hix : (core.num.U64.wrapping_add i 1#u64).val < 128 := by
        simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
      rw [msg.buf_set.guard s buf _ v (hbw (by simpa using h0) _ hix)]
    · rfl

theorem faults.copy_mrs_fault_loop0.guard (s : S) (snd rcv : U64) (regs : Slice U64) (i : Usize)
    (hreg : ∀ r ∈ regs.val, r.val < 384) (hsr : Regs R snd) (hrw : Regs W rcv) :
    faults.copy_mrs_fault_loop0 (PathObl.guard st R W) s snd rcv regs i =
      faults.copy_mrs_fault_loop0 st s snd rcv regs i := by
  unfold faults.copy_mrs_fault_loop0
  refine loop_guard_congr (fun _ => True) (fun y => (Slice.len regs).val - y.2.val) ?_ (s, i) trivial
  rintro ⟨s1, j⟩ -
  try dsimp only
  unfold faults.copy_mrs_fault_loop0.body
  try dsimp only
  refine ⟨?_, ?_⟩
  · split
    · rename_i hj
      have hj' : j.val < regs.length := by simpa using hj
      simp only [lift, bind_ok]
      split
      · rw [eq_ok_of_spec (Slice.index_usize_spec regs j hj')]
        simp only [bind_ok]
        rw [obj.Tcb.reg.guard snd s1 _ (hsr _ (hreg _ (List.getElem_mem _)))]
        refine bind_guard_congr rfl fun v _ => ?_
        refine bind_guard_congr rfl fun rg hrg => ?_
        rw [obj.Tcb.set_reg.guard rcv s1 rg v (hrw rg (post_of_ok (msg.msg_register.lt _) hrg))]
      · rfl
    · rfl
  · intro y hy
    split at hy
    · rename_i hj
      have hj' : j.val < regs.length := by simpa using hj
      simp only [lift, bind_ok] at hy
      split at hy
      · obtain ⟨r0, -, hy⟩ := bind_eq_ok hy
        obtain ⟨v, -, hy⟩ := bind_eq_ok hy
        obtain ⟨rg, -, hy⟩ := bind_eq_ok hy
        obtain ⟨s2, -, hy⟩ := bind_eq_ok hy
        obtain ⟨j2, hj2, hy⟩ := bind_eq_ok hy
        cases ok_inj_ff hy
        refine ⟨trivial, ?_⟩
        obtain ⟨z, hz, hv⟩ := spec_ex_fd (Usize.add_spec (x := j) (y := 1#usize) (by scalar_tac))
        rw [hz] at hj2
        cases ok_inj_ff hj2
        simp only
        scalar_tac
      · simp at hy
    · simp at hy

theorem faults.copy_mrs_fault_loop1.guard (s : S) (snd : U64) (regs : Slice U64) (buf : U64) (i : Usize)
    (hreg : ∀ r ∈ regs.val, r.val < 384) (hl : (Slice.len regs).val < 127) (h0 : buf ≠ 0#u64)
    (hsr : Regs R snd) (hbw : BufW W buf) :
    faults.copy_mrs_fault_loop1 (PathObl.guard st R W) s snd regs buf i =
      faults.copy_mrs_fault_loop1 st s snd regs buf i := by
  unfold faults.copy_mrs_fault_loop1
  refine loop_guard_congr (fun _ => True) (fun y => (Slice.len regs).val - y.2.val) ?_ (s, i) trivial
  rintro ⟨s1, j⟩ -
  try dsimp only
  unfold faults.copy_mrs_fault_loop1.body
  try dsimp only
  refine ⟨?_, ?_⟩
  · split
    · rename_i hj
      have hj' : j.val < regs.length := by simpa using hj
      have hj'' : j.val < (Slice.len regs).val := by simpa using hj
      rw [eq_ok_of_spec (Slice.index_usize_spec regs j hj')]
      simp only [bind_ok]
      rw [obj.Tcb.reg.guard snd s1 _ (hsr _ (hreg _ (List.getElem_mem _)))]
      refine bind_guard_congr rfl fun v _ => ?_
      simp only [lift, bind_ok]
      have hc : (UScalar.cast .U64 j).val = j.val := by
        have : 2 ^ System.Platform.numBits ≤ 2 ^ 64 := by
          rcases System.Platform.numBits_eq with e | e <;> simp [e]
        have := j.hBounds
        simp only [UScalar.cast_val_eq, UScalarTy.numBits]
        exact Nat.mod_eq_of_lt (by simp [Usize.size] at *; omega)
      have hix : (core.num.U64.wrapping_add (UScalar.cast .U64 j) 1#u64).val < 128 := by
        simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits, hc]; omega
      rw [msg.buf_set.guard s1 buf _ v (hbw h0 _ hix)]
    · rfl
  · intro y hy
    split at hy
    · rename_i hj
      obtain ⟨r0, -, hy⟩ := bind_eq_ok hy
      obtain ⟨v, -, hy⟩ := bind_eq_ok hy
      simp only [lift, bind_ok] at hy
      obtain ⟨s2, -, hy⟩ := bind_eq_ok hy
      obtain ⟨j2, hj2, hy⟩ := bind_eq_ok hy
      cases ok_inj_ff hy
      refine ⟨trivial, ?_⟩
      have hj'' : j.val < (Slice.len regs).val := by simpa using hj
      obtain ⟨z, hz, hv⟩ := spec_ex_fd (Usize.add_spec (x := j) (y := 1#usize) (by scalar_tac))
      rw [hz] at hj2
      cases ok_inj_ff hj2
      simp only
      scalar_tac
    · simp at hy

theorem faults.copy_mrs_fault.guard (s : S) (snd rcv : U64) (regs : Slice U64) (buf : U64)
    (hreg : ∀ r ∈ regs.val, r.val < 384) (hl : (Slice.len regs).val < 127)
    (hsr : Regs R snd) (hrw : Regs W rcv) (hbw : BufW W buf) :
    faults.copy_mrs_fault (PathObl.guard st R W) s snd rcv regs buf =
      faults.copy_mrs_fault st s snd rcv regs buf := by
  unfold faults.copy_mrs_fault
  rw [faults.copy_mrs_fault_loop0.guard s snd rcv regs _ hreg hsr hrw]
  refine bind_guard_congr rfl fun p _ => ?_
  obtain ⟨s1, i⟩ := p
  simp only [Aeneas.Std.uncurry_apply_pair]
  split
  · rename_i hne
    exact faults.copy_mrs_fault_loop1.guard s1 snd regs buf i hreg hl (by simpa using hne) hsr hbw
  · rfl

theorem syscall_message_lt : ∀ r ∈ (Array.to_slice faults.SYSCALL_MESSAGE).val, r.val < 384 := by
  simp [faults.SYSCALL_MESSAGE, Aeneas.Std.Array.make, Aeneas.Std.Array.to_slice, layout.reg.RAX,
    layout.reg.RBX, layout.reg.RCX, layout.reg.RDX, layout.reg.RSI, layout.reg.RDI, layout.reg.RBP, layout.reg.R8,
    layout.reg.R9, layout.reg.R10, layout.reg.R11, layout.reg.R12, layout.reg.R13, layout.reg.R14, layout.reg.R15,
    layout.reg.FAULT_IP, layout.reg.RSP, layout.reg.FLAGS]

theorem syscall_message_len : (Slice.len (Array.to_slice faults.SYSCALL_MESSAGE)).val < 127 := by
  simp [faults.SYSCALL_MESSAGE, Aeneas.Std.Array.make, Aeneas.Std.Array.to_slice]

/-- **The UnknownSyscall fault message** (`ty` read from the sender's
`FAULT_TYPE`). -/
theorem faults.set_mrs_fault.guardU {A : Type} (ar : machine.Arch A) (s : S) (a : A) (snd rcv buf : U64)
    (hty : L.mem s (faultA snd) = fl4_abi.consts.fault.UnknownSyscall)
    (hf0 : R (core.num.U64.wrapping_add snd 3376#u64)) (hf1 : R (core.num.U64.wrapping_add snd 3384#u64))
    (hf2 : R (core.num.U64.wrapping_add snd 3392#u64)) (hf3 : R (core.num.U64.wrapping_add snd 3400#u64))
    (hsr : Regs R snd) (hrw : Regs W rcv) (hbw : BufW W buf) :
    faults.set_mrs_fault (PathObl.guard st R W) ar s a snd rcv buf = faults.set_mrs_fault st ar s a snd rcv buf := by
  unfold faults.set_mrs_fault
  rw [obj.Tcb.fault_type.guard snd s hf0, fault_type_ok, hty]
  simp only [bind_ok]
  rw [obj.Tcb.fault_w0.guard snd s hf1, obj.Tcb.fault_w1.guard snd s hf2, obj.Tcb.fault_w2.guard snd s hf3,
    obj.Tcb.reg.guard snd s _ (hsr _ (by simp [layout.reg.FAULT_IP]))]
  simp only [us_ne_cap, ↓reduceIte, lift, bind_ok]
  rw [faults.copy_mrs_fault.guard s snd rcv _ buf syscall_message_lt syscall_message_len hsr hrw hbw]
  simp only [msg.set_mr.guard _ rcv buf 18#u64 _ (by simp) hrw hbw]

end

end Fl4Proofs.P2.PathObl
