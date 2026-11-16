/-
P3 (DESIGN.md §9), scheduling contexts: **the SCs after the spec's
call-stack part of `reply_remove`** (`replyRemoveSc_sck`, spec side only):
every SC after it was an SC before, with the same size and `REFILL_MAX`,
and the same bound thread unless it is the reply's SC (a nonempty call
stack) donated back to the caller.

With `BlockedScActive` ([J]) this gives the reply path's activeness of the
receiver's SC after `reply_remove` (IpcRemove's `remove_top`).
-/
import Fl4Proofs.P3.ScCallRemove
import Fl4Proofs.P3.ScMaxKeep
open Classical

namespace Fl4Proofs.P3.Sched
open Fl4Spec Fl4Proofs.P3.MaxK

noncomputable section

theorem scWithReply_mem' {σ : State Unit} {r p : ObjRef} (h : scWithReply r σ = some p) :
    ∃ y n, σ.kheap p = some (.schedContext y n) ∧ r ∈ y.scReplies := by
  unfold scWithReply partialInv at h
  split_ifs at h with hex
  obtain rfl := Option.some.inj h
  have := The_spec hex
  simpa using this

theorem mk_schedContextDonate_pre (fromOpt : Option ObjRef) :
    MK (NonDet.when (σ := State Unit) (fromOpt ≠ none) (do
        let fromTptr ← NonDet.assertOpt fromOpt
        tcbSchedAction tcbSchedDequeue fromTptr
        tcbReleaseRemove fromTptr
        setTcbObjRef tcbSchedContextUpdate fromTptr none
        testReschedule (Z := Unit) fromTptr)) := by
  mk_auto

/-- The SC step of a donation: the SC's bound thread. -/
theorem setScTcb_sck {σ σ' : State Unit} {q t : ObjRef} {x : Unit × State Unit}
    (hx : x ∈ (setScObjRef (Z := Unit) scTcbUpdate q (some t) σ).1) (he : x.2 = σ') :
    ∀ p y n, σ'.kheap p = some (.schedContext y n) → ∃ y0, σ.kheap p = some (.schedContext y0 n) ∧
      y.scRefillMax = y0.scRefillMax ∧ (y.scTcb = y0.scTcb ∨ (p = q ∧ y.scTcb = some t)) := by
  obtain ⟨y0, n0, hk, e⟩ := updSc_mem hx
  subst he
  rw [e]
  intro p y n hp
  by_cases hpq : p = q
  · subst hpq
    simp only [Function.update_self, Option.some.injEq, KernelObject.schedContext.injEq] at hp
    obtain ⟨rfl, rfl⟩ := hp
    exact ⟨y0, hk, rfl, Or.inr ⟨rfl, rfl⟩⟩
  · simp only [Function.update_of_ne hpq] at hp; exact ⟨y, hp, rfl, Or.inl rfl⟩

/-- **The SCs after `replyRemoveSc`** (module docstring). -/
theorem replyRemoveSc_sck {σ σ5 : State Unit} {t r : ObjRef}
    (hsp : replyRemoveSc t r σ = ({((), σ5)}, False)) :
    ∀ p y n, σ5.kheap p = some (.schedContext y n) → ∃ y0, σ.kheap p = some (.schedContext y0 n) ∧
      y.scRefillMax = y0.scRefillMax ∧ (y.scTcb = y0.scTcb ∨ (y0.scReplies ≠ [] ∧ y.scTcb = some t)) := by
  have hm : ((), σ5) ∈ (replyRemoveSc t r σ).1 := by rw [hsp]; rfl
  unfold replyRemoveSc at hm
  obtain ⟨y1, hy1, hm⟩ := hm
  rw [Set.mem_singleton_iff.1 hy1] at hm
  dsimp only at hm
  cases hw : scWithReply r σ with
  | none =>
    rw [hw] at hm
    obtain rfl : σ5 = σ := congrArg Prod.snd (Set.mem_singleton_iff.1 hm)
    intro p y n hp; exact ⟨y, hp, rfl, Or.inl rfl⟩
  | some q =>
    rw [hw] at hm
    obtain ⟨yq, nq, hkq, hrq⟩ := scWithReply_mem' hw
    have hne : yq.scReplies ≠ [] := List.ne_nil_of_mem hrq
    dsimp only at hm
    obtain ⟨y2, hy2, hm⟩ := hm
    have h2 := (mk_liftM SchedContext.scReplies (mk_getSchedContext' q)) σ y2 hy2
    obtain ⟨y3, hy3, hm⟩ := hm
    have h3 := mk_getTcbObjRef' Tcb.tcbSchedContext t y2.2 y3 hy3
    obtain ⟨y4, hy4, hm⟩ := hm
    have h4 := mk_replyUnlinkSc' q r y3.2 y4 hy4
    have h24 := (h2.trans h3).trans h4
    unfold NonDet.when at hm
    split_ifs at hm with hc
    · unfold schedContextDonate at hm
      obtain ⟨y5, hy5, hm⟩ := hm
      have h5a := mk_getScObjRef' SchedContext.scTcb q y4.2 y5 hy5
      obtain ⟨y5', hy5', hm⟩ := hm
      have h5 := h5a.trans (mk_schedContextDonate_pre y5.1 y5.2 y5' hy5')
      obtain ⟨y6, hy6, hm⟩ := hm
      have h6 := setScTcb_sck hy6 rfl
      have h7 := mk_threadSet' _ t y6.2 _ hm
      intro p y n hp
      obtain ⟨ya, ha, ea1, ea2⟩ := h7 p y n hp
      obtain ⟨yb, hb, eb1, eb2⟩ := h6 p ya n ha
      obtain ⟨yc, hc', ec1, ec2⟩ := (h24.trans h5) p yb n hb
      refine ⟨yc, hc', ea1.trans (eb1.trans ec1), ?_⟩
      rcases eb2 with eb2 | ⟨rfl, eb2⟩
      · exact Or.inl (ea2.trans (eb2.trans ec2))
      · rw [hkq] at hc'; cases hc'
        exact Or.inr ⟨hne, ea2.trans eb2⟩
    · obtain rfl : σ5 = y4.2 := congrArg Prod.snd (Set.mem_singleton_iff.1 hm)
      intro p y n hp
      obtain ⟨yc, hc', ec1, ec2⟩ := h24 p y n hp
      exact ⟨yc, hc', ec1, Or.inl ec2⟩

end

end Fl4Proofs.P3.Sched
