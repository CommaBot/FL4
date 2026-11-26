/-
# P2 (line slhuf, gen 11): guarded-store lemmas of the Copy / Mint decode block

For a store `gS` answering reads of `R` and writes of `W` as `st` (`GRd` / `GWr`), the calls of
`cnode.decode_copy`'s Copy / Mint arm and of the error reply, on top of stpost gen 13's leaves (`P2/InvBlk.lean`:
`obj.Slot.next.guard`, `obj.Slot.set_next.guard`, `obj.Slot.first_badged.guard`, `cspace.lookup_target_slot.guardM`):

* `cdt.ensure_empty_slot.guard` (the destination's cap words);
* `cspace.lookup_source_slot.guardM` (the masked walk from the source root, as `lookup_target_slot.guardM`);
* `obj.Slot.revocable.guard`, `cdt.is_mdb_parent_of.guard`, `cdt.ensure_no_children.guard` (run-relative: the
  slot's CDT successor), `objects.derive_cap.guard` (only an Untyped reads the store);
* `obj.Slot.set_next_flags.guard`, `cdt.set_untyped_cap_as_full.guard`, **`cdt.insert_with_cap.guard`** (the
  source's cap words and `NEXT`, the destination's cap words, `PREV`, `NEXT`, and the old successor's `PREV`);
* `cnode.copied_cap.guard` (the current thread, its registers, the buffer words `buf + 40` / `buf + 48`);
* `faults.set_mrs_lookup_failure.guard`, `syscall.error_mrs.guard`, **`syscall.reply_error.guard`** (the
  receiver's registers and IPC buffer words);
* `after_invocation` needs none here: the Copy / Mint reply passes `Ok ()` on (`syscall.after_invocation.ok_eq`).

No premises.
-/
import Fl4Proofs.P2.InvBlk
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1

section g
variable {S : Type} {st : machine.Store S} {R W : U64 → Prop} {gS : machine.Store S} [GRd gS st R] [GWr gS st W]
  [L : LawfulStore st]

theorem cdt.ensure_empty_slot.guard (s : S) (slot : obj.Slot) (h : R slot)
    (h8 : R (core.num.U64.wrapping_add slot 8#u64)) :
    cdt.ensure_empty_slot gS s slot = cdt.ensure_empty_slot st s slot := by
  unfold cdt.ensure_empty_slot
  rw [obj.Slot.cap.guard slot s h h8]

/-- **The source lookup from a CNode cap on the guarded store** (the masked walk), run-relative. -/
theorem cspace.lookup_source_slot.guardM {s : S} {cp cr cg cgb cptr depth : U64} {src : obj.Slot}
    (C : U64 → U64 → Prop) (hRc : WalkRc (st := st) R s C) (hcl : WalkCl (st := st) s C) (hC : C cp cr)
    (hRd : R src ∧ R (core.num.U64.wrapping_add src 8#u64))
    (h : cspace.lookup_source_slot st s (.CNode cp cr cg cgb) cptr depth = ok (.Ok src)) :
    cspace.lookup_source_slot gS s (.CNode cp cr cg cgb) cptr depth = ok (.Ok src) := by
  unfold cspace.lookup_source_slot cspace.lookup_slot_for_cnode_op at h ⊢
  simp only [bind_ok, ↓reduceIte] at h ⊢
  by_cases d1 : depth < 1#u64
  · rw [if_pos d1] at h; simp at h
  rw [if_neg d1] at h ⊢
  by_cases d2 : depth > cspace.WORD_BITS
  · rw [if_pos d2] at h; simp at h
  rw [if_neg d2] at h ⊢
  obtain ⟨res, eres, hl⟩ := bind_eq_ok h
  have hRf : ∀ x, res = .Ok x → R x.slot ∧ R (core.num.U64.wrapping_add x.slot 8#u64) := by
    intro x hx
    subst hx
    simp only at hl
    by_cases hb : (x.bits_left != 0#u64) = true
    · rw [if_pos hb] at hl; simp at hl
    · rw [if_neg hb] at hl
      have e := ok_inj_ff hl
      simp only [core.result.Result.Ok.injEq] at e
      rw [e]; exact hRd
  rw [rab.guardM C hRc hcl (fun p r gs g e => by cases e; exact hC) hRf eres]
  simp only [bind_ok]
  exact hl

theorem obj.Slot.revocable.guard (self : obj.Slot) (s : S) (h : R (core.num.U64.wrapping_add self layout.cte.NEXT)) :
    obj.Slot.revocable gS self s = obj.Slot.revocable st self s := by
  unfold obj.Slot.revocable
  rw [obj.Slot.next_word.guard self s h]

/-- The words of a slot `cdt.is_mdb_parent_of` reads: both cap words and `NEXT`. -/
def SlotRd (R : U64 → Prop) (q : U64) : Prop :=
  R q ∧ R (core.num.U64.wrapping_add q 8#u64) ∧ R (core.num.U64.wrapping_add q layout.cte.NEXT)

theorem cdt.is_mdb_parent_of.guard (s : S) (a b : obj.Slot) (ha : SlotRd R a) (hb : SlotRd R b) :
    cdt.is_mdb_parent_of gS s a b = cdt.is_mdb_parent_of st s a b := by
  unfold cdt.is_mdb_parent_of
  rw [obj.Slot.revocable.guard a s ha.2.2, obj.Slot.cap.guard a s ha.1 ha.2.1, obj.Slot.cap.guard b s hb.1 hb.2.1,
    obj.Slot.first_badged.guard b s hb.2.2]

theorem cdt.ensure_no_children.guard (s : S) (slot : obj.Slot) (hs : SlotRd R slot)
    (hn : ∀ nx, obj.Slot.next st slot s = ok nx → nx ≠ 0#u64 → SlotRd R nx) :
    cdt.ensure_no_children gS s slot = cdt.ensure_no_children st s slot := by
  unfold cdt.ensure_no_children
  rw [obj.Slot.next.guard slot s hs.2.2]
  refine bind_guard_congr rfl fun nx enx => ?_
  unfold obj.Slot.is_null
  simp only [bind_ok]
  by_cases h0 : nx = 0#u64
  · simp only [h0, decide_true, ↓reduceIte]
  · simp only [h0, decide_false, Bool.false_eq_true, ↓reduceIte]
    rw [cdt.is_mdb_parent_of.guard s slot nx hs (hn nx enx h0)]

/-- `derive_cap` reads the store only for an Untyped (its CDT children). -/
theorem objects.derive_cap.guard (s : S) (slot : obj.Slot) (c : capability.Cap) (hs : SlotRd R slot)
    (hn : ∀ nx, obj.Slot.next st slot s = ok nx → nx ≠ 0#u64 → SlotRd R nx) :
    objects.derive_cap gS s slot c = objects.derive_cap st s slot c := by
  unfold objects.derive_cap
  cases c <;> try rfl
  rw [cdt.ensure_no_children.guard s slot hs hn]

theorem obj.Slot.set_next_flags.guard (self : obj.Slot) (s : S) (n : obj.Slot) (rv fb : Bool)
    (hr : R (core.num.U64.wrapping_add self layout.cte.NEXT)) (hw : W (core.num.U64.wrapping_add self layout.cte.NEXT)) :
    obj.Slot.set_next_flags gS self s n rv fb = obj.Slot.set_next_flags st self s n rv fb := by
  unfold obj.Slot.set_next_flags
  rw [obj.Slot.next_word.guard self s hr]
  simp only [lift, bind_ok, gst_write hw]

theorem cdt.set_untyped_cap_as_full.guard (s : S) (src_cap new_cap : capability.Cap) (src : obj.Slot)
    (hw : W src) (hw8 : W (core.num.U64.wrapping_add src 8#u64)) :
    cdt.set_untyped_cap_as_full gS s src_cap new_cap src = cdt.set_untyped_cap_as_full st s src_cap new_cap src := by
  have e : ∀ x c, obj.Slot.set_cap gS src x c = obj.Slot.set_cap st src x c :=
    fun x c => obj.Slot.set_cap.guard src x c hw hw8
  unfold cdt.set_untyped_cap_as_full
  simp only [e]

/-- **`insert_with_cap` on the guarded store**: the source's `NEXT` (read, written) and cap words (written for an
Untyped source), the destination's cap words, `PREV`, `NEXT` (read, written), and the old successor's `PREV`. -/
theorem cdt.insert_with_cap.guard (s : S) (new_cap src_cap : capability.Cap) (src dest : obj.Slot)
    (rsn : R (core.num.U64.wrapping_add src layout.cte.NEXT)) (wsn : W (core.num.U64.wrapping_add src layout.cte.NEXT))
    (wsc : W src) (wsc8 : W (core.num.U64.wrapping_add src 8#u64))
    (wd : W dest) (wd8 : W (core.num.U64.wrapping_add dest 8#u64))
    (wdp : W (core.num.U64.wrapping_add dest layout.cte.PREV))
    (rdn : R (core.num.U64.wrapping_add dest layout.cte.NEXT)) (wdn : W (core.num.U64.wrapping_add dest layout.cte.NEXT))
    (hnx : ∀ nx, obj.Slot.next st src s = ok nx → nx ≠ 0#u64 → W (core.num.U64.wrapping_add nx layout.cte.PREV)) :
    cdt.insert_with_cap gS s new_cap src_cap src dest = cdt.insert_with_cap st s new_cap src_cap src dest := by
  have e1 : ∀ x, cdt.set_untyped_cap_as_full gS x src_cap new_cap src =
      cdt.set_untyped_cap_as_full st x src_cap new_cap src :=
    fun x => cdt.set_untyped_cap_as_full.guard x src_cap new_cap src wsc wsc8
  have e2 : ∀ x c, obj.Slot.set_cap gS dest x c = obj.Slot.set_cap st dest x c :=
    fun x c => obj.Slot.set_cap.guard dest x c wd wd8
  have e3 : ∀ x q, obj.Slot.set_prev gS dest x q = obj.Slot.set_prev st dest x q :=
    fun x q => obj.Slot.set_prev.guard dest x q wdp
  have e4 : ∀ x n rv fb, obj.Slot.set_next_flags gS dest x n rv fb = obj.Slot.set_next_flags st dest x n rv fb :=
    fun x n rv fb => obj.Slot.set_next_flags.guard dest x n rv fb rdn wdn
  have e5 : ∀ x n, obj.Slot.set_next gS src x n = obj.Slot.set_next st src x n :=
    fun x n => obj.Slot.set_next.guard src x n rsn wsn
  unfold cdt.insert_with_cap
  rw [obj.Slot.next.guard src s rsn]
  refine bind_guard_congr rfl fun rv _ => ?_
  refine bind_guard_congr rfl fun nx enx => ?_
  simp only [e1, e2, e3, e4, e5]
  refine bind_guard_congr rfl fun s1 _ => ?_
  refine bind_guard_congr rfl fun s2 _ => ?_
  refine bind_guard_congr rfl fun s3 _ => ?_
  refine bind_guard_congr rfl fun s4 _ => ?_
  refine bind_guard_congr rfl fun s5 _ => ?_
  unfold obj.Slot.is_null
  simp only [bind_ok]
  by_cases h0 : nx = 0#u64
  · simp only [h0, decide_true, ↓reduceIte]
  · simp only [h0, decide_false, Bool.false_eq_true, ↓reduceIte]
    exact obj.Slot.set_prev.guard nx s5 dest (hnx nx enx h0)

/-- **`copied_cap` on the guarded store**: the current thread, its registers, the buffer words of arguments 4 and
5 (`buf + 40`, `buf + 48`), and `derive_cap`'s words of the source. -/
theorem cnode.copied_cap.guard (s : S) (lbl length buf : U64) (src : obj.Slot) (src_cap : capability.Cap)
    (hct : R (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD)) (hrg : Regs R (L.curW s))
    (hb4 : R (core.num.U64.wrapping_add buf
      (core.num.U64.wrapping_mul (core.num.U64.wrapping_add 4#u64 1#u64) 8#u64)))
    (hb5 : R (core.num.U64.wrapping_add buf
      (core.num.U64.wrapping_mul (core.num.U64.wrapping_add 5#u64 1#u64) 8#u64)))
    (hs : SlotRd R src) (hn : ∀ nx, obj.Slot.next st src s = ok nx → nx ≠ 0#u64 → SlotRd R nx) :
    cnode.copied_cap gS s lbl length buf src src_cap = cnode.copied_cap st s lbl length buf src src_cap := by
  have hreg : ∀ i r, msg.msg_register i = ok r → R (regA (L.curW s) r) :=
    fun i r hr => hrg r (post_of_ok (msg.msg_register.lt _) hr)
  have ed : ∀ c, objects.derive_cap gS s src c = objects.derive_cap st s src c :=
    fun c => objects.derive_cap.guard s src c hs hn
  unfold cnode.copied_cap
  rw [sched.cur_thread.guard s hct, cur_thread_ok]
  simp only [bind_ok]
  rw [msg.syscall_arg.guard s _ buf 4#u64 (hreg 4#u64) hb4, msg.syscall_arg.guard s _ buf 5#u64 (hreg 5#u64) hb5]
  simp only [ed]

theorem faults.set_mrs_lookup_failure.guard (s : S) (t buf : U64) (lf : error.LookupFault) (off : U64)
    (ho : off.val < 120) (hrw : Regs W t) (hbw : BufW W buf) :
    faults.set_mrs_lookup_failure gS s t buf lf off = faults.set_mrs_lookup_failure st s t buf lf off := by
  have e : ∀ x (i v : U64), i.val < 127 → msg.set_mr gS x t buf i v = msg.set_mr st x t buf i v :=
    fun x i v hi => msg.set_mr.guard x t buf i v hi hrw hbw
  have h1 : (core.num.U64.wrapping_add off 1#u64).val < 127 := by
    simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
  have h2 : (core.num.U64.wrapping_add off 2#u64).val < 127 := by
    simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
  have h3 : (core.num.U64.wrapping_add off 3#u64).val < 127 := by
    simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
  unfold faults.set_mrs_lookup_failure
  refine bind_guard_congr rfl fun i _ => ?_
  rw [e s off i (by omega)]
  refine bind_guard_congr rfl fun ⟨i1, s1⟩ _ => ?_
  simp only [uncurry_apply_pair]
  cases lf <;> simp only [lift, bind_ok, uncurry_apply_pair]
  · rw [e s1 _ _ h1]
  · rw [e s1 _ _ h1]
    refine bind_guard_congr rfl fun ⟨j, s2⟩ _ => ?_
    simp only [uncurry_apply_pair]
    rw [e s2 _ _ h2]
  · rw [e s1 _ _ h1]
    refine bind_guard_congr rfl fun ⟨j, s2⟩ _ => ?_
    simp only [uncurry_apply_pair]
    rw [e s2 _ _ h2]
    refine bind_guard_congr rfl fun ⟨j', s3⟩ _ => ?_
    simp only [uncurry_apply_pair]
    rw [e s3 _ _ h3]

theorem syscall.error_mrs.guard (s : S) (t buf : U64) (e : error.SysError) (hrw : Regs W t) (hbw : BufW W buf) :
    syscall.error_mrs gS s t buf e = syscall.error_mrs st s t buf e := by
  have em : ∀ x (i v : U64), i.val < 127 → msg.set_mr gS x t buf i v = msg.set_mr st x t buf i v :=
    fun x i v hi => msg.set_mr.guard x t buf i v hi hrw hbw
  have el : ∀ x lf, faults.set_mrs_lookup_failure_at gS x t buf lf 1#u64 =
      faults.set_mrs_lookup_failure_at st x t buf lf 1#u64 := fun x lf => by
    unfold faults.set_mrs_lookup_failure_at
    exact faults.set_mrs_lookup_failure.guard x t buf lf 1#u64 (by simp) hrw hbw
  unfold syscall.error_mrs
  cases e <;> simp only [em _ 0#u64 _ (by simp), em _ 1#u64 _ (by simp), el]

/-- **The error reply on the guarded store**: the receiver's IPC buffer lookup (`hI`, the buffer slot's cap words),
its registers, and the words of the buffer it finds (read and written: the error MRs and the debug word). -/
theorem syscall.reply_error.guard (s : S) (t : obj.Tcb) (e : error.SysError) {sl : U64}
    (hsl : obj.Tcb.slot t layout.tcb.SLOT_BUFFER = ok sl)
    (hI : R (core.num.U64.wrapping_add t 3512#u64)) (hR0 : R sl) (hR8 : R (core.num.U64.wrapping_add sl 8#u64))
    (hrw : Regs W t)
    (hbuf : ∀ buf, msg.lookup_ipc_buffer st s true t = ok buf → BufW W buf ∧ BufW R buf) :
    syscall.reply_error gS s t e = syscall.reply_error st s t e := by
  have hrw' : W (regA t layout.reg.BADGE) := hrw _ (by simp [layout.reg.BADGE])
  have hmi : W (regA t layout.reg.MSG_INFO) := hrw _ (by simp [layout.reg.MSG_INFO])
  unfold syscall.reply_error
  rw [msg.lookup_ipc_buffer.guard s true t hsl hI hR0 hR8]
  refine bind_guard_congr rfl fun buf ebuf => ?_
  obtain ⟨hW, hR⟩ := hbuf buf ebuf
  rw [obj.Tcb.set_reg.guard t s _ _ hrw']
  refine bind_guard_congr rfl fun s1 _ => ?_
  rw [syscall.error_mrs.guard s1 t buf e hrw hW]
  refine bind_guard_congr rfl fun ⟨len, s2⟩ _ => ?_
  simp only [uncurry_apply_pair]
  have e3 : ∀ x m, msg.set_msg_info gS x t m = msg.set_msg_info st x t m := fun x m => msg.set_msg_info.guard x t m hmi
  refine bind_guard_congr ?_ fun ⟨s3, len1⟩ _ => ?_
  · by_cases hc : fl4_abi.config.KERNEL_INVOCATION_REPORT_ERROR_IPC = true
    · simp only [hc, ↓reduceIte]
      by_cases hb : (buf != 0#u64) = true
      · simp only [hb, ↓reduceIte]
        have hb0 : buf ≠ 0#u64 := by simpa using hb
        refine bind_guard_congr rfl fun i ei => ?_
        have hi : i.val = 7 := by
          have := UScalar.add_equiv syscall.DEBUG_MESSAGE_START 1#u64
          rw [ei] at this
          simp at this
          omega
        rw [msg.buf_get.guard s2 buf i (hR hb0 i (by omega))]
        refine bind_guard_congr rfl fun w _ => ?_
        simp only [lift, bind_ok]
        rw [msg.buf_set.guard s2 buf i _ (hW hb0 i (by omega))]
      · simp only [hb, Bool.false_eq_true, ↓reduceIte]
    · simp only [hc, Bool.false_eq_true, ↓reduceIte]
  · simp only [uncurry_apply_pair, e3]

end g

end Fl4Proofs.P2.PathObl
