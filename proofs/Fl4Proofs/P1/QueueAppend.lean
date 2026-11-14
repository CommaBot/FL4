/-
P1: the writes on a thread's blocking path (`set_block_obj`, `set_block_badge`,
`set_block_flags`, `set_reply_obj`) and the footprints of `ep_append` /
`ntfn_append`.
-/
import Fl4Proofs.P1.QueueCancel
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64}

/-! ## Specs -/

@[step] theorem obj.Tcb.set_block_obj.wr (s : S) (t : obj.Tcb) (v : U64) :
    obj.Tcb.set_block_obj st t s v ⦃ s' => s' = L.wr s (blockA t) v ⦄ := by
  unfold obj.Tcb.set_block_obj; step*; simp_all [blockA]
@[step] theorem obj.Tcb.set_block_badge.wr (s : S) (t : obj.Tcb) (v : U64) :
    obj.Tcb.set_block_badge st t s v ⦃ s' => s' = L.wr s (core.num.U64.wrapping_add t 3344#u64) v ⦄ := by
  unfold obj.Tcb.set_block_badge; step*; simp_all
@[step] theorem obj.Tcb.set_block_flags.wr (s : S) (t : obj.Tcb) (v : U64) :
    obj.Tcb.set_block_flags st t s v ⦃ s' => s' = L.wr s (core.num.U64.wrapping_add t 3352#u64) v ⦄ := by
  unfold obj.Tcb.set_block_flags; step*; simp_all
@[step] theorem obj.Tcb.set_reply_obj.wr (s : S) (t : obj.Tcb) (v : U64) :
    obj.Tcb.set_reply_obj st t s v ⦃ s' => s' = L.wr s (replyA t) v ⦄ := by
  unfold obj.Tcb.set_reply_obj; step*; simp_all [replyA]

/-! ## Appending -/

theorem endpoint.ep_append.foot (s : S) (ep : U64) (t : obj.Tcb) (state : U64) (xs : List U64)
    (hT : TcbPlaced T) (hE : EpPlaced T ep) (h : QueueRel (L.mem s) T .Ep (L.epQ s ep) xs)
    (ht : t ∈ T) (hn : t ∉ xs) :
    endpoint.ep_append st s ep t state ⦃ s' => WritesIn st s s' (EpFoot (t :: xs) ep) ⦄ := by
  unfold endpoint.ep_append
  step*
  subst q_post
  refine WP.spec_bind (tcbqueue.append_by_prio.rel s .Ep _ t xs hT h ht hn) ?_
  rintro ⟨q1, s1⟩ h1
  simp only [WP.uncurry'_pair] at h1
  obtain ⟨-, hf⟩ := h1
  step*
  subst_vars
  exact reorder_foot_tail hE hf.writesIn

theorem notification.ntfn_append.foot (s : S) (n : U64) (t : obj.Tcb) (xs : List U64)
    (hT : TcbPlaced T) (hE : EpPlaced T n) (h : QueueRel (L.mem s) T .Ep (L.epQ s n) xs)
    (ht : t ∈ T) (hn : t ∉ xs) :
    notification.ntfn_append st s n t ⦃ s' => WritesIn st s s' (EpFoot (t :: xs) n) ⦄ := by
  unfold notification.ntfn_append
  step*
  subst q_post
  refine WP.spec_bind (tcbqueue.append_by_prio.rel s .Ep _ t xs hT h ht hn) ?_
  rintro ⟨q1, s1⟩ h1
  simp only [WP.uncurry'_pair] at h1
  obtain ⟨-, hf⟩ := h1
  step*
  subst_vars
  exact reorder_foot_tail hE hf.writesIn


/-! ## Reads on the IPC paths -/

theorem obj.Tcb.block_badge.any (s : S) (t : obj.Tcb) : obj.Tcb.block_badge st t s ⦃ _ => True ⦄ := by
  unfold obj.Tcb.block_badge; step*
theorem obj.Tcb.block_flags.any (s : S) (t : obj.Tcb) : obj.Tcb.block_flags st t s ⦃ _ => True ⦄ := by
  unfold obj.Tcb.block_flags; step*
theorem obj.Tcb.fault_type.any (s : S) (t : obj.Tcb) : obj.Tcb.fault_type st t s ⦃ _ => True ⦄ := by
  unfold obj.Tcb.fault_type; step*
theorem obj.Ntfn.badge.any (s : S) (n : obj.Ntfn) : obj.Ntfn.badge st n s ⦃ _ => True ⦄ := by
  unfold obj.Ntfn.badge; step*
theorem obj.Sc.reply.val (s : S) (c : obj.Sc) : obj.Sc.reply st c s ⦃ v => v = L.mem s (scReplyA c) ⦄ := by
  unfold obj.Sc.reply; step*; simp_all [scReplyA]
theorem obj.Tcb.set_affinity.wr (s : S) (t : obj.Tcb) (v : U64) :
    obj.Tcb.set_affinity st t s v ⦃ s' => s' = L.wr s (affA t) v ⦄ := by
  unfold obj.Tcb.set_affinity; step*; simp_all [affA]

/-! ## Donation's queue steps on an unqueued thread -/

theorem sched.dequeue.noop (s : S) (t : obj.Tcb) (h0 : (L.mem s (inqA t) &&& sched.Q_QUEUED) = 0#u64) :
    sched.dequeue st s t ⦃ s' => s' = s ⦄ := by
  unfold sched.dequeue
  step with sched.queued.spec as ⟨b, eb⟩
  split
  · rename_i hb; rw [eb] at hb; exact absurd h0 (of_decide_eq_true hb)
  · exact (WP.spec_ok _).2 rfl

theorem sched.release_remove.noop (s : S) (t : obj.Tcb) (h0 : (L.mem s (inqA t) &&& sched.Q_RELEASE) = 0#u64) :
    sched.release_remove st s t ⦃ s' => s' = s ⦄ := by
  unfold sched.release_remove
  step with sched.in_release_queue.spec as ⟨b, eb⟩
  split
  · rename_i hb; rw [eb] at hb; exact absurd h0 (of_decide_eq_true hb)
  · exact (WP.spec_ok _).2 rfl

/-- `remote_tcb_stall` at most sets the current core's `IPI_PENDING`. -/
theorem smp.remote_tcb_stall.spec {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (t : obj.Tcb) :
    smp.remote_tcb_stall st ar s a t ⦃ s' _ =>
      s' = s ∨ ∃ v, s' = L.wr s (L.nodeAt s (L.cpu s) layout.node.IPI_PENDING) v ⦄ := by
  unfold smp.remote_tcb_stall smp.remote_reschedule
  step*
  all_goals first | (left; rfl) | (right; subst_vars; exact ⟨_, rfl⟩)

/-! ## Reply-link writes with their values -/

theorem obj.Reply.set_prev.val (s : S) (r : obj.Reply) (v : U64) :
    obj.Reply.set_prev st r s v ⦃ s' => s' = L.wr s (rPrevA r) (v &&& ~~~1#u64) ⦄ := by
  unfold obj.Reply.set_prev obj.Reply.set_prev_raw
  simp only [lift, bind_ok, L.write_eq, WP.spec_ok]; rfl
theorem obj.Reply.set_next.val0 (s : S) (r : obj.Reply) (v : U64) :
    obj.Reply.set_next st r s v false ⦃ s' => s' = L.wr s (rNextA r) ((v &&& ~~~1#u64) ||| 0#u64) ⦄ := by
  unfold obj.Reply.set_next obj.Reply.set_next_raw
  simp only [lift, bind_ok, L.write_eq, WP.spec_ok, Bool.false_eq_true, ↓reduceIte]; rfl
theorem obj.Reply.set_next.val1 (s : S) (r : obj.Reply) (v : U64) :
    obj.Reply.set_next st r s v true ⦃ s' => s' = L.wr s (rNextA r) ((v &&& ~~~1#u64) ||| 1#u64) ⦄ := by
  unfold obj.Reply.set_next obj.Reply.set_next_raw
  simp only [lift, bind_ok, L.write_eq, WP.spec_ok, ↓reduceIte]; rfl

/-! ## Notification words -/


theorem obj.Ntfn.sc.val (s : S) (n : obj.Ntfn) : obj.Ntfn.sc st n s ⦃ v => v = L.mem s (ntfnScA n) ⦄ := by
  unfold obj.Ntfn.sc; step*; simp_all [ntfnScA]

theorem obj.Ntfn.set_state.val (s : S) (n : obj.Ntfn) (v : U64) :
    obj.Ntfn.set_state st n s v ⦃ s' =>
      s' = L.wr s (epTSA n) ((L.mem s (epTSA n) &&& ~~~3#u64) ||| (v &&& 3#u64)) ⦄ := by
  unfold obj.Ntfn.set_state obj.Ntfn.tail obj.Ntfn.tail_state obj.Ntfn.set_tail_state
  step*
  subst_vars
  rw [epTSA, ← ntfn_ts_eq]
  congr 1
  apply eq_of_bv
  simp only [i1_post1, i_post1, UScalar.bv_and, UScalar.bv_or]


theorem obj.Tcb.bound_ntfn.val (s : S) (t : obj.Tcb) : obj.Tcb.bound_ntfn st t s ⦃ v => v = L.mem s (boundA t) ⦄ := by
  unfold obj.Tcb.bound_ntfn; step*; simp_all [boundA]

end

end Fl4Proofs.P1
