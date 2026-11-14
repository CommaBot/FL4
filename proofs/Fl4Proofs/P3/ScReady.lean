/-
P3 (DESIGN.md §9), scheduling contexts: the refill hypothesis `ActReady`
(SchedSwitch.lean) transfers to states that differ only in ways that do not
affect it: the same scheduler action, current time and release queue,
TCBs unchanged or without an SC, SCs with the same refills and refill max
(`ActReady.transfer`).
-/
import Fl4Proofs.P3.ScReturn
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section Spec
open Fl4Spec

theorem scsOf_eq (σ : State Unit) (p : ObjRef) :
    scsOf σ p = match σ.kheap p with | some (.schedContext y _) => some y | _ => none := by
  simp only [scsOfKh, optMap, scOf]
  cases σ.kheap p with
  | none => rfl
  | some ko => cases ko <;> rfl

theorem tcbsOf_eq (σ : State Unit) (p : ObjRef) :
    tcbsOf σ p = match σ.kheap p with | some (.tcb x) => some x | _ => none := by
  simp only [tcbsOfKh, optMap, tcbOf]
  cases σ.kheap p with
  | none => rfl
  | some ko => cases ko <;> rfl

theorem tcbsOf_some {σ : State Unit} {p : ObjRef} {x : Tcb} (h : tcbsOf σ p = some x) :
    σ.kheap p = some (.tcb x) := by
  rw [tcbsOf_eq] at h
  cases hk : σ.kheap p with
  | none => rw [hk] at h; cases h
  | some ko => rw [hk] at h; cases ko <;> simp at h; rw [h]

theorem schedulable_congr {σ σ' : State Unit} {u : ObjRef} (h1 : tcbsOf σ' u = tcbsOf σ u)
    (h2 : ∀ p, Option.map scActive (scsOf σ' p) = Option.map scActive (scsOf σ p))
    (h3 : σ'.releaseQueue = σ.releaseQueue) : schedulable u σ' = schedulable u σ := by
  unfold schedulable
  apply decide_eq_decide.2
  rw [h3]
  simp only [optPred, optMapSome, optMap, h1]
  cases tcbsOf σ u with
  | none => simp
  | some x =>
    cases hsc : x.tcbSchedContext with
    | none => simp [hsc]
    | some p =>
      have := h2 p
      simp only [hsc]
      cases e1 : scsOf σ' p <;> cases e2 : scsOf σ p <;> simp_all

theorem schedulable_none {σ : State Unit} {u : ObjRef} {x : Tcb} (h : tcbsOf σ u = some x)
    (hn : x.tcbSchedContext = none) : schedulable u σ = false := by
  unfold schedulable
  simp [optPred, optMapSome, optMap, h, hn]

theorem schedulable_notcb {σ : State Unit} {u : ObjRef} (h : tcbsOf σ u = none) : schedulable u σ = false := by
  unfold schedulable
  simp [optPred, optMapSome, optMap, h]

theorem readSuff_eq (σ : State Unit) (p : ObjRef) (u : Ticks) :
    readScRefillSufficient (Z := Unit) p u σ = match σ.kheap p with
      | some (.schedContext y _) => if y.scRefills = [] then none else some (refillSufficient u (refillHd y))
      | _ => none := by
  show Option.bind (Option.bind (Option.bind (σ.kheap p) fun k => (match k with
      | .schedContext sc _ => Lookup.oreturn sc
      | _ => Lookup.ofail) σ) fun sc => Option.bind (Lookup.oassert (sc.scRefills ≠ []) σ)
        fun _ => Lookup.oreturn (refillHd sc) σ) (fun h => Lookup.oreturn (refillSufficient u h) σ) = _
  cases σ.kheap p with
  | none => rfl
  | some ko =>
    cases ko with
    | schedContext y n =>
      by_cases e : y.scRefills = []
      · simp [Lookup.oreturn, Lookup.oassert, e, Lookup.ofail]
      · simp [Lookup.oreturn, Lookup.oassert, e]
    | _ => rfl

theorem suff_inv {σ : State Unit} {p : ObjRef} {u : Ticks} {b : Bool}
    (h : getScRefillSufficient (Z := Unit) p u σ = ({(b, σ)}, False)) :
    ∃ y n, σ.kheap p = some (.schedContext y n) ∧ y.scRefills ≠ [] ∧ refillSufficient u (refillHd y) = b := by
  have hf : ∀ (o : Option Bool), readScRefillSufficient (Z := Unit) p u σ = o →
      getScRefillSufficient (Z := Unit) p u σ = NonDet.assertOpt o σ := fun o e => by
    simp [getScRefillSufficient, NonDet.getsThe, e]
  have key := readSuff_eq σ p u
  cases hk : σ.kheap p with
  | none =>
    rw [hk] at key; rw [hf none key] at h; simp [NonDet.assertOpt, NonDet.fail] at h
  | some ko =>
    cases ko with
    | schedContext y n =>
      rw [hk] at key
      by_cases hne : y.scRefills = []
      · simp only [hne, ↓reduceIte] at key
        rw [hf none key] at h; simp [NonDet.assertOpt, NonDet.fail] at h
      · refine ⟨y, n, rfl, hne, ?_⟩
        rw [getScRefillSufficient_eq hk hne] at h
        have := congrArg Prod.fst h
        simpa using this
    | _ => rw [hk] at key; rw [hf none key] at h; simp [NonDet.assertOpt, NonDet.fail] at h

theorem ready_inv {σ : State Unit} {p : ObjRef} {b : Bool}
    (h : getScRefillReady (Z := Unit) p σ = ({(b, σ)}, False)) {y : SchedContext} {n : Nat}
    (hk : σ.kheap p = some (.schedContext y n)) (hne : y.scRefills ≠ []) :
    refillReady σ.curTime (refillHd y) = b := by
  rw [getScRefillReady_eq hk hne] at h
  have := congrArg Prod.fst h
  simpa using this

theorem ActReady.transfer {σ σ' : State Unit} (h : ActReady σ)
    (hact : σ'.schedulerAction = σ.schedulerAction) (hct : σ'.curTime = σ.curTime)
    (hrq : σ'.releaseQueue = σ.releaseQueue)
    (htcb : ∀ p x, tcbsOf σ' p = some x → x.tcbSchedContext = none ∨ tcbsOf σ p = some x)
    (hsc : ∀ p y n, σ.kheap p = some (.schedContext y n) → ∃ y', σ'.kheap p = some (.schedContext y' n) ∧
      y'.scRefills = y.scRefills ∧ y'.scRefillMax = y.scRefillMax)
    (hscm : ∀ p, Option.map scActive (scsOf σ' p) = Option.map scActive (scsOf σ p)) :
    ActReady σ' := by
  intro u hu hs
  cases hx : tcbsOf σ' u with
  | none => rw [schedulable_notcb hx] at hs; cases hs
  | some x =>
    rcases htcb u x hx with h0 | hx0
    · rw [schedulable_none hx h0] at hs; cases hs
    have hs0 : schedulable u σ = true := by
      rw [← schedulable_congr (by rw [hx, hx0]) hscm hrq]; exact hs
    obtain ⟨x0, scp, hk1, hsc1, h1, h2⟩ := h u (by rw [← hact]; exact hu) hs0
    rw [tcbsOf_some hx0] at hk1; cases hk1
    obtain ⟨y, n, hky, hne, hsuff⟩ := suff_inv h1
    have hrdy := ready_inv h2 hky hne
    obtain ⟨y', hky', hrf, -⟩ := hsc scp y n hky
    have hne' : y'.scRefills ≠ [] := by rw [hrf]; exact hne
    have hd : refillHd y' = refillHd y := by unfold refillHd; rw [hrf]
    refine ⟨x, scp, tcbsOf_some hx, hsc1, ?_, ?_⟩
    · rw [getScRefillSufficient_eq hky' hne', hd, hsuff]
    · rw [getScRefillReady_eq hky' hne', hd, hct, hrdy]

end Spec

end

end Fl4Proofs.P3.Sched
