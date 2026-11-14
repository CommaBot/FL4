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


end

end Fl4Proofs.P1
