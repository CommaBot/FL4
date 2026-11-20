/-
P3 (DESIGN.md §9), invariant line G1 (nq1): **NtfnQB across the queue
additions** (spec side only): a notification write whose new queue adds only a
thread BlockedOnNotification on that notification (`nq_ntfn_add`), so
`tcb_ntfn_append` / `reorder_ntfn` of such a thread, `set_priority` (a
BlockedOnNotification target is reordered in its queue; it is not in `K`),
`receive_signal_blocked` / `receive_signal` (the receiver, first in `K`,
becomes BlockedOnNotification and is appended: it leaves `K`). `nq2_auto`:
`nq_auto` with the state-read rule `nq_rds` and failing / impossible branches.
-/
import Fl4Proofs.P3.SpecInvNtfnQF6
open Classical

namespace Fl4Proofs.P3.SInv
open Fl4Spec

noncomputable section

set_option maxHeartbeats 1000000

variable {K : List ObjRef}

theorem upd_ne' {σ : State Unit} {p q : ObjRef} {o : KernelObject} (h : q ≠ p) :
    ({ σ with kheap := Function.update σ.kheap p (some o) } : State Unit).kheap q = σ.kheap q := by
  dsimp only; rw [Function.update_apply, if_neg h]

/-- `t` is a TCB BlockedOnNotification on `n`. -/
def TS (t n : ObjRef) (σ : State Unit) : Prop :=
  ∃ y, σ.kheap t = some (.tcb y) ∧ y.tcbState = .blockedOnNotification n

/-- A notification write whose new queue adds only a thread BlockedOnNotification on it. -/
theorem nq_ntfn_add {σ : State Unit} {n t : ObjRef} {x0 x' : Notification} (h : NQ K σ)
    (hn : σ.kheap n = some (.notification x0)) (ht : TS t n σ)
    (hsub : ∀ u ∈ x'.ntfnObj.ntfnQueue, u = t ∨ u ∈ x0.ntfnObj.ntfnQueue) :
    NQ K { σ with kheap := Function.update σ.kheap n (some (.notification x')) } := by
  have hne : ∀ u y, σ.kheap u = some (.tcb y) → u ≠ n := by
    rintro u y hu rfl; rw [hn] at hu; cases hu
  refine ⟨fun m x u hm hu => ?_, fun u hu => ⟨?_, fun y hy => ?_⟩⟩
  · by_cases e : m = n
    · subst e
      dsimp only at hm; rw [Function.update_apply, if_pos rfl] at hm; cases hm
      rcases hsub u hu with rfl | hu0
      · obtain ⟨y, hy, hs⟩ := ht
        exact ⟨y, (upd_ne' (hne _ _ hy)).trans hy, hs⟩
      · obtain ⟨y, hy, hs⟩ := h.1 m x0 u hn hu0
        exact ⟨y, (upd_ne' (hne _ _ hy)).trans hy, hs⟩
    · rw [upd_ne' e] at hm
      obtain ⟨y, hy, hs⟩ := h.1 m x u hm hu
      exact ⟨y, (upd_ne' (hne _ _ hy)).trans hy, hs⟩
  · rintro ⟨m, x, hm, hq⟩
    by_cases e : m = n
    · subst e
      dsimp only at hm; rw [Function.update_apply, if_pos rfl] at hm; cases hm
      rcases hsub u hq with rfl | hu0
      · obtain ⟨y, hy, hs⟩ := ht
        exact (h.2 _ hu).2 y hy (by rw [hs]; trivial)
      · exact (h.2 u hu).1 ⟨m, x0, hn, hu0⟩
    · rw [upd_ne' e] at hm; exact (h.2 u hu).1 ⟨m, x, hm, hq⟩
  · by_cases e : u = n
    · subst e; dsimp only at hy; rw [Function.update_apply, if_pos rfl] at hy; cases hy
    · rw [upd_ne' e] at hy; exact (h.2 u hu).2 y hy

/-- `tcb_append` (an ordered insert) reads only, and adds only `t`. -/
theorem nq_mem_tcbAppend {t : ObjRef} {qs : List ObjRef} {σ : State Unit} {y : List ObjRef × State Unit}
    (h : y ∈ (tcbAppend (Z := Unit) t qs σ).1) : y.2 = σ ∧ ∀ u ∈ y.1, u = t ∨ u ∈ qs := by
  have hs : y.2 = σ := (show IK (fun s => s = σ) (tcbAppend (Z := Unit) t qs) by
    unfold tcbAppend orderedInsert; repeat' (first | ik_step0 | ik_unfold)) σ rfl y h
  refine ⟨hs, ?_⟩
  unfold tcbAppend orderedInsert at h
  obtain ⟨z1, h1, h⟩ := h
  obtain ⟨z2, h2, h⟩ := h
  obtain ⟨z3, h3, h⟩ := h
  rw [Set.mem_singleton_iff.1 h3] at h
  obtain ⟨z4, h4, h⟩ := h
  rw [Set.mem_singleton_iff.1 h4] at h
  rw [Set.mem_singleton_iff.1 h]
  intro u hu
  rw [List.mem_map] at hu
  obtain ⟨⟨a, b⟩, hab, rfl⟩ := hu
  simp only [List.mem_append, List.mem_singleton] at hab
  rcases hab with (hab | hab) | hab
  · exact Or.inr (List.of_mem_zip ((List.takeWhile_sublist _).subset hab)).1
  · cases hab; exact Or.inl rfl
  · exact Or.inr (List.of_mem_zip ((List.dropWhile_sublist _).subset hab)).1

/-- `tcb_ntfn_append` of a thread BlockedOnNotification on that notification. -/
theorem nq_tcbNtfnAppend_p (t n : ObjRef) :
    HK (fun s => NQ K s ∧ TS t n s) (NQ K) (tcbNtfnAppend (Z := Unit) t n) := by
  intro σ ⟨hσ, ht⟩ y hy
  unfold tcbNtfnAppend at hy
  obtain ⟨y1, hy1, hy⟩ := hy
  obtain ⟨hk, e1⟩ := mem_getSimpleKo hy1
  obtain ⟨a, s1⟩ := y1
  simp only at hk e1; subst e1
  obtain ⟨z, hz, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 hz] at hy
  obtain ⟨z, hz, hy⟩ := hy
  obtain ⟨hzs, hzm⟩ := nq_mem_tcbAppend hz
  obtain ⟨qs', s2⟩ := z
  simp only at hzs hzm; subst hzs
  obtain ⟨o0, -, -, -, e⟩ := mem_setSimpleKo hy
  rw [e]
  exact nq_ntfn_add hσ hk ht fun u hu => hzm u hu

/-- `reorder_ntfn` of a thread BlockedOnNotification on that notification. -/
theorem nq_reorderNtfn_p (n t : ObjRef) :
    HK (fun s => NQ K s ∧ TS t n s) (NQ K) (reorderNtfn (Z := Unit) n t) := by
  intro σ ⟨hσ, ht⟩ y hy
  unfold reorderNtfn at hy
  obtain ⟨y1, hy1, hy⟩ := hy
  obtain ⟨hk, e1⟩ := mem_getSimpleKo hy1
  obtain ⟨a, s1⟩ := y1
  simp only at hk e1; subst e1
  obtain ⟨z, ⟨-, rfl⟩, hy⟩ := hy
  obtain ⟨z, hz, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 hz] at hy
  obtain ⟨z, ⟨-, rfl⟩, hy⟩ := hy
  obtain ⟨z, hz, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 hz] at hy
  obtain ⟨z, hz, hy⟩ := hy
  obtain ⟨hzs, hzm⟩ := nq_mem_tcbAppend hz
  obtain ⟨qs', s2⟩ := z
  simp only at hzs hzm; subst hzs
  obtain ⟨o0, -, -, -, e⟩ := mem_setSimpleKo hy
  rw [e]
  refine nq_ntfn_add hσ hk ht fun u hu => ?_
  rcases hzm u hu with h | h
  · exact Or.inl h
  · exact Or.inr (removeAll_sub h)

theorem kh_setThreadStateAct (t : ObjRef) (k : KHeap) :
    IK (fun s => s.kheap = k) (setThreadStateAct (Z := Unit) t) := by
  unfold setThreadStateAct setSchedulerAction
  repeat' (first | ik_step0 | ik_unfold | (unfold NonDet.when))

/-- `set_priority`: a BlockedOnNotification target is reordered in its queue. -/
theorem nq_setPriority (t : ObjRef) (prio : Priority) : NQK K (setPriority (Z := Unit) t prio) := by
  unfold setPriority getThreadState
  refine ik_threadGet_bind fun σ x hx => ?_
  cases hs : x.tcbState
  case blockedOnNotification n =>
    try dsimp only
    rw [if_neg (by simp [runnable])]
    intro hσ y hy
    obtain ⟨y1, h1, hy⟩ := hy
    unfold threadSetPriority at h1
    have hb1 : NQ K y1.2 := nq_threadSet (fun tcb => { tcb with tcbPriority := prio }) t (fun _ => rfl) σ hσ y1 h1
    obtain ⟨x1, hx1, e1⟩ := mem_threadSet h1
    rw [hx] at hx1; cases hx1
    obtain ⟨y2, h2, hy⟩ := hy
    have e2 : y2.2 = y1.2 := by
      simp only [epBlocked, NonDet.maybeM] at h2; rw [Set.mem_singleton_iff.1 h2]
    simp only [ntfnBlocked, NonDet.maybeM] at hy
    rw [e2] at hy
    exact nq_reorderNtfn_p n t y1.2 ⟨hb1, ⟨{ x with tcbPriority := prio }, by rw [e1]; simp, by simp [hs]⟩⟩ y hy
  all_goals
    simp only [runnable, epBlocked, ntfnBlocked, NonDet.maybeM, Bool.false_eq_true, ↓reduceIte]
    exact ikp_of_ik (by nq_auto) σ
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_setPriority _ _)

theorem nq_filter_of {σ : State Unit} {t : ObjRef} (h : NQ K σ) : NQ (K.filter (· ≠ t)) σ :=
  nq_mono h fun _ hu => (mem_filter_ne' hu).1

/-- `receive_signal_blocked`: the receiver (in `K`) becomes BlockedOnNotification and is appended. -/
theorem nq_receiveSignalBlocked (thread n : ObjRef) (blk : Bool) (ht : thread ∈ K) :
    HK (NQ K) (NQ (K.filter (· ≠ thread))) (receiveSignalBlocked (Z := Unit) thread n blk) := by
  unfold receiveSignalBlocked
  split
  · intro σ hσ y hy
    obtain ⟨y1, h1, hy⟩ := hy
    unfold setThreadState at h1
    obtain ⟨y0, h0, h1⟩ := h1
    obtain ⟨x, hx, e0⟩ := mem_threadSet h0
    have hK' : thread ∉ K.filter (· ≠ thread) := by simp
    have hb0 : NQ (K.filter (· ≠ thread)) y0.2 := by
      rw [e0]; exact nq_update (nq_filter_of hσ) hx (nqok_stsK (hσ.2 thread ht).1 hK')
    have hk1 : y1.2.kheap = y0.2.kheap := kh_setThreadStateAct thread _ y0.2 rfl y1 h1
    have hb1 : NQ (K.filter (· ≠ thread)) y1.2 := nq_setThreadStateAct' thread y0.2 hb0 y1 h1
    have hts : TS thread n y1.2 := ⟨{ x with tcbState := .blockedOnNotification n }, by rw [hk1, e0]; simp, rfl⟩
    obtain ⟨y2, h2, hy⟩ := hy
    have hb2 := nq_tcbNtfnAppend_p thread n y1.2 ⟨hb1, hts⟩ y2 h2
    exact (nq_maybeReturnSc (Kq := K.filter (· ≠ thread)) n thread) y2.2 hb2 y hy
  · exact fun σ hσ y hy => nq_filter_of (nq_doNbrecvFailedTransfer _ σ hσ y hy)

theorem hk_getSimpleKo_bind {P Q : State Unit → Prop} {α β : Type} [Nonempty α] {C : α → KernelObject}
    {p : ObjRef} {k : α → NonDet (State Unit) β} (h : ∀ a, HK P Q (k a)) : HK P Q (getSimpleKo (Z := Unit) C p >>= k) := by
  intro σ hσ y ⟨z, hz, hy⟩
  obtain ⟨-, e⟩ := mem_getSimpleKo hz
  obtain ⟨a, s⟩ := z
  simp only at e; subst e
  exact h a _ hσ y hy

/-- `receive_signal`: an active notification is consumed; otherwise the receiver blocks. -/
theorem nq_receiveSignal (thread : ObjRef) (cap : Cap) (blk : Bool) (ht : thread ∈ K) :
    HK (NQ K) (NQ (K.filter (· ≠ thread))) (receiveSignal (Z := Unit) thread cap blk) := by
  unfold receiveSignal
  split
  · refine hk_bind (hk_of_ik (ik_pure _)) fun p => ?_
    refine hk_getSimpleKo_bind fun a => ?_
    (try dsimp only)
    split
    · exact hk_post (hk_of_ik (by nq_auto)) fun s h => nq_filter_of h
    · exact nq_receiveSignalBlocked thread _ blk ht
  · intro σ hσ y hy
    obtain ⟨y1, h1, -⟩ := hy
    exact h1.elim

/-- `nq_auto`, with the state-read rule, closing failing and impossible branches. -/
macro "nq2_auto" : tactic => `(tactic| repeat' (first | nq_leaf | (with_reducible exact ik_fail_bind) | nq_rds | (with_reducible apply ike_ite) | (with_reducible apply ike_whenE) | (with_reducible apply ike_unlessE) | (with_reducible apply ike_liftE) | (show IK _ (ite _ _ _); split <;> try (rename_i hsplit; simp at hsplit; done)) | (show IK _ (ite _ _ _ >>= _); split <;> try (rename_i hsplit; simp at hsplit; done)) | ik_step0 | ik_unfold | (unfold NonDetE.whenE) | (unfold NonDetE.unlessE) | (unfold NonDet.when) | (unfold NonDet.unless) | (exfalso; contradiction)))

end

end Fl4Proofs.P3.SInv
