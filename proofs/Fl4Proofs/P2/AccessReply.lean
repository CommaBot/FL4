/-
# P2: guarded-store lemmas for the reply half of the ReplyRecv fast path

For the per-path obligation of `P2/PathObl.lean`, stated at each callee's
entry state with address-only hypotheses (they hold at every later state):

* `faults.copy_mrs_fault_reply_loop0.guard`, `loop1.guard`,
  `faults.copy_mrs_fault_reply.guard`: reads of the sender's message
  registers, `IPC_BUFFER` word, buffer slot and buffer words; writes of the
  receiver's registers named by the list;
* `faults.handle_fault_reply.guardU`: the reply to an UnknownSyscall fault
  (the sender's `MSG_INFO`, the receiver's `FAULT_TYPE`, then the copy);
* `obj.Reply.next.guard`, `prev`, `next_is_head`, `set_prev`, `set_next`;
* `ipc.reply_unlink.guard`, `ipc.reply_remove.guardZ`: removing a reply
  object with no neighbours (`NEXT` and `PREV` 0 up to the head bit, as
  fl4-sync's `local_syscall` checks): its `PREV` / `NEXT` / `TCB` words and
  the thread's `set_thread_state`;
* `faults.clear_fault.guard`: the `FAULT_TYPE` word.

Generic over the Arch instance. No premises.
-/
import Fl4Proofs.P2.AccessFault
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1 Fl4Proofs.P0.Consts

section
variable {S : Type} {st : machine.Store S} {R W : U64 → Prop} [L : LawfulStore st]

theorem usize_cast_val (j : Usize) : (UScalar.cast .U64 j).val = j.val := by
  have : 2 ^ System.Platform.numBits ≤ 2 ^ 64 := by
    rcases System.Platform.numBits_eq with e | e <;> simp [e]
  have := j.hBounds
  simp only [UScalar.cast_val_eq, UScalarTy.numBits]
  exact Nat.mod_eq_of_lt (by simp [Usize.size] at *; omega)

theorem faults.copy_mrs_fault_reply_loop0.guard (s : S) (snd rcv : U64) (regs : Slice U64) (n i : Usize)
    (hreg : ∀ r ∈ regs.val, r.val < 384) (hsr : Regs R snd) (hrw : Regs W rcv) :
    faults.copy_mrs_fault_reply_loop0 (PathObl.guard st R W) s snd rcv regs n i =
      faults.copy_mrs_fault_reply_loop0 st s snd rcv regs n i := by
  unfold faults.copy_mrs_fault_reply_loop0
  refine loop_guard_congr (fun _ => True) (fun y => (Slice.len regs).val - y.2.val) ?_ (s, i) trivial
  rintro ⟨s1, j⟩ -
  try dsimp only
  unfold faults.copy_mrs_fault_reply_loop0.body
  try dsimp only
  refine ⟨?_, ?_⟩
  · split
    · split
      · rename_i _ hj
        have hj' : j.val < regs.length := by simpa using hj
        simp only [lift, bind_ok]
        split
        · rw [eq_ok_of_spec (Slice.index_usize_spec regs j hj')]
          simp only [bind_ok]
          refine bind_guard_congr rfl fun rg hrg => ?_
          rw [obj.Tcb.reg.guard snd s1 _ (hsr rg (post_of_ok (msg.msg_register.lt _) hrg))]
          refine bind_guard_congr rfl fun v _ => ?_
          refine bind_guard_congr rfl fun v' _ => ?_
          rw [obj.Tcb.set_reg.guard rcv s1 _ v' (hrw _ (hreg _ (List.getElem_mem _)))]
        · rfl
      · rfl
    · rfl
  · intro y hy
    split at hy
    · split at hy
      · rename_i _ hj
        have hj'' : j.val < (Slice.len regs).val := by simpa using hj
        simp only [lift, bind_ok] at hy
        split at hy
        · obtain ⟨r0, -, hy⟩ := bind_eq_ok hy
          obtain ⟨rg, -, hy⟩ := bind_eq_ok hy
          obtain ⟨v, -, hy⟩ := bind_eq_ok hy
          obtain ⟨v', -, hy⟩ := bind_eq_ok hy
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
    · simp at hy

theorem faults.copy_mrs_fault_reply_loop1.guard (s : S) (rcv : U64) (regs : Slice U64) (n i : Usize)
    (buf : U64) (hreg : ∀ r ∈ regs.val, r.val < 384) (hl : (Slice.len regs).val < 127) (h0 : buf ≠ 0#u64)
    (hbr : BufW R buf) (hrw : Regs W rcv) :
    faults.copy_mrs_fault_reply_loop1 (PathObl.guard st R W) s rcv regs n i buf =
      faults.copy_mrs_fault_reply_loop1 st s rcv regs n i buf := by
  unfold faults.copy_mrs_fault_reply_loop1
  refine loop_guard_congr (fun _ => True) (fun y => (Slice.len regs).val - y.2.val) ?_ (s, i) trivial
  rintro ⟨s1, j⟩ -
  try dsimp only
  unfold faults.copy_mrs_fault_reply_loop1.body
  try dsimp only
  refine ⟨?_, ?_⟩
  · split
    · split
      · rename_i _ hj
        have hj' : j.val < regs.length := by simpa using hj
        have hj'' : j.val < (Slice.len regs).val := by simpa using hj
        rw [eq_ok_of_spec (Slice.index_usize_spec regs j hj')]
        simp only [bind_ok, lift]
        have hix : (core.num.U64.wrapping_add (UScalar.cast .U64 j) 1#u64).val < 128 := by
          simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits, usize_cast_val]; omega
        rw [msg.buf_get.guard s1 buf _ (hbr h0 _ hix)]
        refine bind_guard_congr rfl fun v _ => ?_
        refine bind_guard_congr rfl fun v' _ => ?_
        rw [obj.Tcb.set_reg.guard rcv s1 _ v' (hrw _ (hreg _ (List.getElem_mem _)))]
      · rfl
    · rfl
  · intro y hy
    split at hy
    · split at hy
      · rename_i _ hj
        have hj'' : j.val < (Slice.len regs).val := by simpa using hj
        obtain ⟨r0, -, hy⟩ := bind_eq_ok hy
        simp only [lift, bind_ok] at hy
        obtain ⟨v, -, hy⟩ := bind_eq_ok hy
        obtain ⟨v', -, hy⟩ := bind_eq_ok hy
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

/-- The words `lookup_ipc_buffer t` reads: `IPC_BUFFER` and the buffer slot. -/
def RdBuf (R : U64 → Prop) (t : U64) : Prop :=
  ∃ sl, obj.Tcb.slot t layout.tcb.SLOT_BUFFER = ok sl ∧ R (core.num.U64.wrapping_add t 3512#u64) ∧ R sl ∧
    R (core.num.U64.wrapping_add sl 8#u64)

/-- **`copy_mrs_fault_reply`**: `bufR` holds the words of every buffer
`lookup_ipc_buffer` may return for the sender. -/
theorem faults.copy_mrs_fault_reply.guard (s : S) (snd rcv : U64) (regs : Slice U64) (len : U64)
    (hreg : ∀ r ∈ regs.val, r.val < 384) (hl : (Slice.len regs).val < 127)
    (hsr : Regs R snd) (hrw : Regs W rcv) (hb : RdBuf R snd)
    (hbw : ∀ X : S, ∀ buf, msg.lookup_ipc_buffer st X false snd = ok buf → BufW R buf) :
    faults.copy_mrs_fault_reply (PathObl.guard st R W) s snd rcv regs len =
      faults.copy_mrs_fault_reply st s snd rcv regs len := by
  obtain ⟨sl, hsl, h1, h2, h3⟩ := hb
  unfold faults.copy_mrs_fault_reply
  refine bind_guard_congr rfl fun _ _ => ?_
  refine bind_guard_congr rfl fun n _ => ?_
  rw [faults.copy_mrs_fault_reply_loop0.guard s snd rcv regs n _ hreg hsr hrw]
  refine bind_guard_congr rfl fun p _ => ?_
  obtain ⟨s1, i⟩ := p
  simp only [Aeneas.Std.uncurry_apply_pair]
  split
  · rw [msg.lookup_ipc_buffer.guard s1 false snd hsl h1 h2 h3]
    refine bind_guard_congr rfl fun buf hbuf => ?_
    split
    · rename_i hne
      exact faults.copy_mrs_fault_reply_loop1.guard s1 rcv regs n i buf hreg hl (by simpa using hne)
        (hbw s1 buf hbuf) hrw
    · rfl
  · rfl

/-- **`handle_fault_reply`** to an UnknownSyscall fault (`ty` read from the
receiver's `FAULT_TYPE`). -/
theorem faults.handle_fault_reply.guardU {A : Type} (ar : machine.Arch A) (s : S) (a : A) (rcv snd : U64)
    (hty : L.mem s (faultA rcv) = fl4_abi.consts.fault.UnknownSyscall)
    (hmi : R (regA snd layout.reg.MSG_INFO)) (hft : R (core.num.U64.wrapping_add rcv 3376#u64))
    (hsr : Regs R snd) (hrw : Regs W rcv) (hb : RdBuf R snd)
    (hbw : ∀ X : S, ∀ buf, msg.lookup_ipc_buffer st X false snd = ok buf → BufW R buf) :
    faults.handle_fault_reply (PathObl.guard st R W) ar s a rcv snd =
      faults.handle_fault_reply st ar s a rcv snd := by
  unfold faults.handle_fault_reply
  rw [msg.msg_info.guard s snd hmi]
  refine bind_guard_congr rfl fun tag _ => ?_
  rw [obj.Tcb.fault_type.guard rcv s hft, fault_type_ok, hty]
  simp only [bind_ok, us_ne_cap, ↓reduceIte, lift]
  rw [faults.copy_mrs_fault_reply.guard s snd rcv _ _ syscall_message_lt syscall_message_len hsr hrw hb hbw]

/-! ## Reply objects -/

theorem obj.Reply.next.guard (s : S) (r : U64) (h : R (rNextA r)) :
    obj.Reply.next (PathObl.guard st R W) r s = obj.Reply.next st r s := by
  unfold obj.Reply.next; rw [obj.Reply.next_raw.guard r s h]

theorem obj.Reply.prev.guard (s : S) (r : U64) (h : R (rPrevA r)) :
    obj.Reply.prev (PathObl.guard st R W) r s = obj.Reply.prev st r s := by
  unfold obj.Reply.prev; rw [obj.Reply.prev_raw.guard r s h]

theorem obj.Reply.next_is_head.guard (s : S) (r : U64) (h : R (rNextA r)) :
    obj.Reply.next_is_head (PathObl.guard st R W) r s = obj.Reply.next_is_head st r s := by
  unfold obj.Reply.next_is_head; rw [obj.Reply.next_raw.guard r s h]

theorem obj.Reply.set_prev.guard (s : S) (r v : U64) (h : W (rPrevA r)) :
    obj.Reply.set_prev (PathObl.guard st R W) r s v = obj.Reply.set_prev st r s v := by
  unfold obj.Reply.set_prev; simp only [lift, bind_ok]; rw [obj.Reply.set_prev_raw.guard r s _ h]

theorem obj.Reply.set_next.guard (s : S) (r v : U64) (b : Bool) (h : W (rNextA r)) :
    obj.Reply.set_next (PathObl.guard st R W) r s v b = obj.Reply.set_next st r s v b := by
  unfold obj.Reply.set_next; simp only [lift, bind_ok]
  split <;> rw [obj.Reply.set_next_raw.guard r s _ h]

theorem reply_next_ok (s : S) (r : U64) : obj.Reply.next st r s = ok (L.mem s (rNextA r) &&& ~~~1#u64) := by
  unfold obj.Reply.next obj.Reply.next_raw rNextA; simp only [lift, bind_ok, L.read_eq]

theorem reply_prev_ok (s : S) (r : U64) : obj.Reply.prev st r s = ok (L.mem s (rPrevA r) &&& ~~~1#u64) := by
  unfold obj.Reply.prev obj.Reply.prev_raw rPrevA; simp only [lift, bind_ok, L.read_eq]

theorem ipc.reply_unlink.guard (s : S) (r t : U64) (hn : NodeSt (L := L) R W s) (hrt : W (rTcbA r))
    (hw : W (stA t)) (h1 : R (stA t)) (h2 : R (scA t))
    (h3 : ∀ X : S, R (maxA (L.mem X (scA t)))) (h4 : R (inqA t)) :
    ipc.reply_unlink (PathObl.guard st R W) s r t = ipc.reply_unlink st s r t := by
  unfold ipc.reply_unlink
  rw [obj.Reply.set_tcb.guard r s _ hrt]
  refine bind_guard_congr rfl fun s1 hs1 => ?_
  have e : s1 = L.wr s (rTcbA r) 0#u64 := by
    unfold obj.Reply.set_tcb at hs1; simp only [lift, bind_ok, L.write_eq] at hs1
    exact (ok_inj_ff hs1).symm
  subst e
  exact sched.set_thread_state.guard _ t _ hn.wr hw h1 h2 (h3 _) h4

/-- **`reply_remove` of a reply object with no neighbours** (`NEXT` and
`PREV` are 0 up to the head bit). -/
theorem ipc.reply_remove.guardZ {A : Type} (ar : machine.Arch A) (s : S) (a : A) (r t : U64)
    (hz : L.mem s (rNextA r) &&& ~~~1#u64 = 0#u64 ∧ L.mem s (rPrevA r) &&& ~~~1#u64 = 0#u64)
    (hrn : R (rNextA r)) (hrp : R (rPrevA r)) (hwn : W (rNextA r)) (hwp : W (rPrevA r))
    (hn : NodeSt (L := L) R W s) (hrt : W (rTcbA r))
    (hw : W (stA t)) (h1 : R (stA t)) (h2 : R (scA t))
    (h3 : ∀ X : S, R (maxA (L.mem X (scA t)))) (h4 : R (inqA t)) :
    ipc.reply_remove (PathObl.guard st R W) ar s a r t = ipc.reply_remove st ar s a r t := by
  unfold ipc.reply_remove
  rw [obj.Reply.next.guard s r hrn, obj.Reply.prev.guard s r hrp, reply_next_ok, reply_prev_ok, hz.1, hz.2]
  simp only [bind_ok, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  rw [obj.Reply.set_prev.guard s r _ hwp]
  refine bind_guard_congr rfl fun s3 hs3 => ?_
  rw [obj.Reply.set_next.guard s3 r _ _ hwn]
  refine bind_guard_congr rfl fun s4 hs4 => ?_
  have hn4 : NodeSt (L := L) R W s4 := by
    unfold obj.Reply.set_prev obj.Reply.set_prev_raw at hs3
    simp only [lift, bind_ok, L.write_eq] at hs3
    cases ok_inj_ff hs3
    unfold obj.Reply.set_next obj.Reply.set_next_raw at hs4
    simp only [lift, bind_ok, L.write_eq, Bool.false_eq_true, ↓reduceIte] at hs4
    cases ok_inj_ff hs4
    exact hn.wr.wr
  rw [ipc.reply_unlink.guard s4 r t hn4 hrt hw h1 h2 h3 h4]

theorem faults.clear_fault.guard (s : S) (t : U64) (h : W (core.num.U64.wrapping_add t 3376#u64)) :
    faults.clear_fault (PathObl.guard st R W) s t = faults.clear_fault st s t := by
  unfold faults.clear_fault
  exact obj.Tcb.set_fault_type.guard t s _ h

end

end Fl4Proofs.P2.PathObl
