/-
P3 (DESIGN.md §9), scheduling contexts: **the scheduler invariant** `Inv`
of the spec state (fragments of l4v `valid_sched`, `valid_refills`,
`heap_refs_inv`, `valid_objs`):

* `rq`: ready-queue members are runnable and bound to an SC (`valid_ready_qs`);
* `rel`, `sorted`: release-queue members are runnable and bound to an
  active SC, and the queue is sorted by ready time (`valid_release_q`,
  `sorted_release_q`);
* `rd`: a thread that is runnable or blocked on a notification has a
  released SC if bound to an active one and not in the release queue
  (`valid_ready_qs`, `valid_sched_action`, `released_ipc_queues`);
* `refills`: an active SC's refills are non-empty with positive amounts,
  summing below `2 ^ 64`, the head holding at least `MIN_BUDGET`
  (`valid_refills`);
* `back`: a TCB's SC points back to it (`heap_refs_inv`);
* `ntfnSc`: a notification's SC is an SC (`valid_objs`).

`Inv.actReady`: `ActReady` follows. `Inv.stable`, `Inv.block`: the
notification code's own steps keep `Inv`.
-/
import Fl4Proofs.P3.ScBudgetTop
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section Spec
open Fl4Spec

/-- An active SC's refills. -/
def RefOK (y : SchedContext) : Prop :=
  y.scRefills ≠ [] ∧ (∀ r ∈ y.scRefills, 0 < r.rAmount.toNat) ∧
    (y.scRefills.map fun r => r.rAmount.toNat).sum < 2 ^ 64 ∧ MIN_BUDGET ≤ (refillHd y).rAmount

/-- The scheduler invariant (see the module docstring). -/
structure Inv (σ : State Unit) : Prop where
  rq : ∀ d p u, u ∈ σ.readyQueues d p → ∃ x scp, σ.kheap u = some (.tcb x) ∧ x.tcbSchedContext = some scp ∧
    runnable x.tcbState = true
  rel : ∀ u ∈ σ.releaseQueue, ∃ x scp y n, σ.kheap u = some (.tcb x) ∧ x.tcbSchedContext = some scp ∧
    runnable x.tcbState = true ∧ σ.kheap scp = some (.schedContext y n) ∧ scActive y = true
  sorted : σ.releaseQueue.Pairwise (fun a b => specRt σ a ≤ specRt σ b)
  rd : ∀ u x, σ.kheap u = some (.tcb x) → inClass x.tcbState → RelIfBound σ u
  refills : ∀ p y n, σ.kheap p = some (.schedContext y n) → scActive y = true → RefOK y
  back : ∀ u x p, σ.kheap u = some (.tcb x) → x.tcbSchedContext = some p →
    ∃ y n, σ.kheap p = some (.schedContext y n) ∧ y.scTcb = some u
  ntfnSc : ∀ q x p, σ.kheap q = some (.notification x) → x.ntfnSc = some p →
    ∃ y n, σ.kheap p = some (.schedContext y n)
  ne : ∀ p y n, σ.kheap p = some (.schedContext y n) → y.scRefills ≠ []

theorem schedulable_inv {σ : State Unit} {t : ObjRef} (h : schedulable t σ = true) :
    ∃ x scp y n, σ.kheap t = some (.tcb x) ∧ x.tcbSchedContext = some scp ∧ runnable x.tcbState = true ∧
      σ.kheap scp = some (.schedContext y n) ∧ scActive y = true ∧ t ∉ σ.releaseQueue := by
  unfold schedulable at h
  simp only [decide_eq_true_eq] at h
  obtain ⟨h1, h2, h3⟩ := h
  cases hk : σ.kheap t with
  | none => simp [optPred, optMapSome, optMap, tcbsOfKh, hk] at h1
  | some ko =>
    cases ko with
    | tcb x =>
      simp only [optPred, optMapSome, optMap, tcbsOfKh, hk, tcbOf] at h1 h2
      cases hsc : x.tcbSchedContext with
      | none => simp [hsc] at h2
      | some scp =>
        simp only [hsc, scsOfKh, optMap] at h2
        cases hkp : σ.kheap scp with
        | none => simp [hkp] at h2
        | some ko' =>
          cases ko' with
          | schedContext y n =>
            simp only [hkp, scOf] at h2
            exact ⟨x, scp, y, n, rfl, hsc, h1, hkp, h2, h3⟩
          | _ => simp [hkp, scOf] at h2
    | _ => simp [optPred, optMapSome, optMap, tcbsOfKh, hk, tcbOf] at h1

/-- **`ActReady` from the invariant.** -/
theorem Inv.actReady {σ : State Unit} (h : Inv σ) : ActReady σ := by
  intro t _ hs
  obtain ⟨x, scp, y, n, hk, hsc, hrun, hky, hact, hnr⟩ := schedulable_inv hs
  have hrel := h.rd t x hk (Or.inl hrun) x scp y n hk hsc hky hact hnr
  have hne := (h.refills scp y n hky hact).1
  refine ⟨x, scp, hk, hsc, ?_, ?_⟩
  · rw [getScRefillSufficient_eq hky hne, hrel.2]
  · rw [getScRefillReady_eq hky hne, hrel.1]

theorem specRt_eq {σ : State Unit} {u scp : ObjRef} {x : Tcb} {y : SchedContext} {n : Nat}
    (hk : σ.kheap u = some (.tcb x)) (hsc : x.tcbSchedContext = some scp)
    (hky : σ.kheap scp = some (.schedContext y n)) (hne : y.scRefills ≠ []) :
    specRt σ u = (refillHd y).rTime := by
  unfold specRt; rw [readTcbReadyTime_eq hk hsc hky hne]; rfl

/-- `released` only reads the current time. -/
theorem released_congr {σ σ' : State Unit} (h : σ'.curTime = σ.curTime) (y : SchedContext) :
    released σ' y ↔ released σ y := by unfold released; rw [h]

/-- The invariant only reads the heap, the queues and the current time. -/
theorem Inv.congr' {σ σ' : State Unit} (h : Inv σ) (hk : σ'.kheap = σ.kheap)
    (hq : ∀ d p u, u ∈ σ'.readyQueues d p → ∃ x scp, σ.kheap u = some (.tcb x) ∧ x.tcbSchedContext = some scp ∧
      runnable x.tcbState = true)
    (hr : σ'.releaseQueue = σ.releaseQueue) (ht : σ'.curTime = σ.curTime) :
    Inv σ' := by
  refine ⟨fun d p u hu => ?_, fun u hu => ?_, ?_, fun u x hx hc => ?_, fun p y n hy => ?_,
    fun u x p hx hp => ?_, fun q x p hx hp => ?_, fun p y n hy => ?_⟩
  · rw [hk]; exact hq d p u hu
  · rw [hr] at hu; rw [hk]; exact h.rel u hu
  · rw [hr]
    refine List.Pairwise.imp_of_mem (fun {a b} ha hb hab => ?_) h.sorted
    obtain ⟨xa, pa, ya, na, h1, h2, -, h4, h5⟩ := h.rel a ha
    obtain ⟨xb, pb, yb, nb, g1, g2, -, g4, g5⟩ := h.rel b hb
    have nea := (h.refills _ _ _ h4 h5).1
    have neb := (h.refills _ _ _ g4 g5).1
    rw [specRt_eq (by rw [hk]; exact h1) h2 (by rw [hk]; exact h4) nea,
      specRt_eq (by rw [hk]; exact g1) g2 (by rw [hk]; exact g4) neb]
    rw [specRt_eq h1 h2 h4 nea, specRt_eq g1 g2 g4 neb] at hab
    exact hab
  · rw [hk] at hx
    intro x' scp y n h1 h2 h3 h4 h5
    rw [hk] at h1 h3; rw [hr] at h5
    rw [released_congr ht]
    exact h.rd u x hx hc x' scp y n h1 h2 h3 h4 h5
  · rw [hk] at hy; exact h.refills p y n hy
  · rw [hk] at hx ⊢; exact h.back u x p hx hp
  · rw [hk] at hx ⊢; exact h.ntfnSc q x p hx hp
  · rw [hk] at hy; exact h.ne p y n hy

theorem Inv.congr {σ σ' : State Unit} (h : Inv σ) (hk : σ'.kheap = σ.kheap)
    (hq : σ'.readyQueues = σ.readyQueues) (hr : σ'.releaseQueue = σ.releaseQueue) (ht : σ'.curTime = σ.curTime) :
    Inv σ' := h.congr' hk (fun d p u hu => h.rq d p u (hq ▸ hu)) hr ht

/-! ## The notification code's steps -/

theorem NtfnStep.tcb_back {σ σ' : State Unit} (h : NtfnStep σ σ') {p : ObjRef} {y : Tcb}
    (hk : σ'.kheap p = some (.tcb y)) : ∃ x, σ.kheap p = some (.tcb x) ∧ y.tcbSchedContext = x.tcbSchedContext := by
  rcases h.2.2 p with e | ⟨a, b, -, hb, -, -⟩ | ⟨a, b, ha, hb, e⟩
  · exact ⟨y, e ▸ hk, rfl⟩
  · rw [hk] at hb; cases hb
  · rw [hk] at hb; cases hb; exact ⟨a, ha, by rw [e]⟩

theorem NtfnStep.sc_back {σ σ' : State Unit} (h : NtfnStep σ σ') {p : ObjRef} {y : SchedContext} {n : Nat}
    (hk : σ'.kheap p = some (.schedContext y n)) : σ.kheap p = some (.schedContext y n) := by
  rcases h.2.2 p with e | ⟨a, b, -, hb, -, -⟩ | ⟨a, b, -, hb, -⟩
  · rw [← e]; exact hk
  · rw [hk] at hb; cases hb
  · rw [hk] at hb; cases hb

theorem NtfnStep.ntfn_back {σ σ' : State Unit} (h : NtfnStep σ σ') {p : ObjRef} {y : Notification}
    (hk : σ'.kheap p = some (.notification y)) : ∃ x, σ.kheap p = some (.notification x) ∧ y.ntfnSc = x.ntfnSc := by
  rcases h.2.2 p with e | ⟨a, b, ha, hb, -, h2⟩ | ⟨a, b, -, hb, -⟩
  · exact ⟨y, e ▸ hk, rfl⟩
  · rw [hk] at hb; cases hb; exact ⟨a, ha, h2⟩
  · rw [hk] at hb; cases hb

theorem NtfnStep.relIfBound {σ σ' : State Unit} (h : NtfnStep σ σ') {u : ObjRef} (hr : RelIfBound σ u) :
    RelIfBound σ' u := by
  obtain ⟨-, e2, -, -, -, e6, -⟩ := NtfnStep.abs h
  intro x scp y n h1 h2 h3 h4 h5
  obtain ⟨x0, h1', hs⟩ := NtfnStep.tcb_back h h1
  rw [released_congr e6]
  exact hr x0 scp y n h1' (hs ▸ h2) (NtfnStep.sc_back h h3) h4 (by rw [← e2]; exact h5)

/-- A step that keeps every TCB's SC and every SC keeps the invariant, given
what it does to the states: `hst` for the queued threads, `hrd` for the
threads of `inClass`. -/
theorem Inv.step {σ σ' : State Unit} (h : Inv σ) (hn : NtfnStep σ σ')
    (hst : ∀ u x y, σ.kheap u = some (.tcb x) → σ'.kheap u = some (.tcb y) →
      ((∃ d p, u ∈ σ.readyQueues d p) ∨ u ∈ σ.releaseQueue) → runnable x.tcbState = true →
      runnable y.tcbState = true)
    (hrd : ∀ u x y, σ.kheap u = some (.tcb x) → σ'.kheap u = some (.tcb y) → inClass y.tcbState →
      RelIfBound σ u) : Inv σ' := by
  obtain ⟨e1, e2, -, -, -, e6, -⟩ := NtfnStep.abs hn
  refine ⟨fun d p u hu => ?_, fun u hu => ?_, ?_, fun u y hy hc => ?_, fun p y n hy => ?_,
    fun u y p hy hp => ?_, fun q y p hy hp => ?_, fun p y n hy => h.ne p y n (NtfnStep.sc_back hn hy)⟩
  · rw [e1] at hu
    obtain ⟨x, scp, h1, h2, h3⟩ := h.rq d p u hu
    obtain ⟨y, hy, -, hs, -⟩ := NtfnStep.tcbSched hn h1
    exact ⟨y, scp, hy, hs.trans h2, hst u x y h1 hy (Or.inl ⟨d, p, hu⟩) h3⟩
  · rw [e2] at hu
    obtain ⟨x, scp, yc, n, h1, h2, h3, h4, h5⟩ := h.rel u hu
    obtain ⟨y, hy, -, hs, -⟩ := NtfnStep.tcbSched hn h1
    exact ⟨y, scp, yc, n, hy, hs.trans h2, hst u x y h1 hy (Or.inr hu) h3, NtfnStep.sc hn h4, h5⟩
  · rw [e2]
    refine List.Pairwise.imp_of_mem (fun {a b} ha hb hab => ?_) h.sorted
    obtain ⟨xa, pa, ya, na, h1, h2, -, h4, h5⟩ := h.rel a ha
    obtain ⟨xb, pb, yb, nb, g1, g2, -, g4, g5⟩ := h.rel b hb
    have nea := (h.refills _ _ _ h4 h5).1
    have neb := (h.refills _ _ _ g4 g5).1
    obtain ⟨ya', hya, -, hsa, -⟩ := NtfnStep.tcbSched hn h1
    obtain ⟨yb', hyb, -, hsb, -⟩ := NtfnStep.tcbSched hn g1
    rw [specRt_eq hya (hsa.trans h2) (NtfnStep.sc hn h4) nea, specRt_eq hyb (hsb.trans g2) (NtfnStep.sc hn g4) neb]
    rw [specRt_eq h1 h2 h4 nea, specRt_eq g1 g2 g4 neb] at hab
    exact hab
  · obtain ⟨x, hx, -⟩ := NtfnStep.tcb_back hn hy
    exact NtfnStep.relIfBound hn (hrd u x y hx hy hc)
  · exact h.refills p y n (NtfnStep.sc_back hn hy)
  · obtain ⟨x, hx, hs⟩ := NtfnStep.tcb_back hn hy
    obtain ⟨yc, n, h1, h2⟩ := h.back u x p hx (hs ▸ hp)
    exact ⟨yc, n, NtfnStep.sc hn h1, h2⟩
  · obtain ⟨x, hx, hs⟩ := NtfnStep.ntfn_back hn hy
    obtain ⟨yc, n, h1⟩ := h.ntfnSc q x p hx (hs ▸ hp)
    exact ⟨yc, n, NtfnStep.sc hn h1⟩

/-- **A step that blocks no thread keeps the invariant.** -/
theorem Inv.stable {σ σ' : State Unit} (h : Inv σ) (hn : NtfnStep σ σ') (hb : NoBlock σ σ') : Inv σ' := by
  refine h.step hn (fun u x y h1 h2 _ hr => ?_) (fun u x y h1 h2 hc => ?_)
  · rcases hb u x y h1 h2 with e | ⟨hr', -⟩
    · rw [e]; exact hr
    · exact hr'
  · rcases hb u x y h1 h2 with e | ⟨-, hc' | hr⟩
    · exact h.rd u x h1 (e ▸ hc)
    · exact h.rd u x h1 hc'
    · exact hr

/-- **Blocking a thread in no queue keeps the invariant**, if its SC is
released. -/
theorem Inv.block {σ σ' : State Unit} {t : ObjRef} (h : Inv σ) (hn : NtfnStep σ σ') (hq : NotQueued σ t)
    (hrt : RelIfBound σ t)
    (hoth : ∀ p x y, σ.kheap p = some (.tcb x) → σ'.kheap p = some (.tcb y) → p ≠ t → y.tcbState = x.tcbState) :
    Inv σ' := by
  refine h.step hn (fun u x y h1 h2 hm hr => ?_) (fun u x y h1 h2 hc => ?_)
  · have hut : u ≠ t := by
      rintro rfl
      rcases hm with ⟨d, p, hm⟩ | hm
      · exact hq.1 d p hm
      · exact hq.2 hm
    rw [hoth u x y h1 h2 hut]; exact hr
  · by_cases hut : u = t
    · subst hut; exact hrt
    · exact h.rd u x h1 (hoth u x y h1 h2 hut ▸ hc)

end Spec

end

end Fl4Proofs.P3.Sched
