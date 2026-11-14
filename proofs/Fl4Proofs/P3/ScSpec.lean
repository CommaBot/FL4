/-
P3 (DESIGN.md §9), scheduling contexts: the spec's SC accessors on a state
where `p` is `.schedContext x n` (single outcomes), and the ring list.
-/
import Fl4Proofs.P3.ScFrame
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section Spec
open Fl4Spec
variable {σ : State Unit} {p : ObjRef} {x : SchedContext} {n : Nat}

theorem getSchedContext_eq (hk : σ.kheap p = some (.schedContext x n)) :
    getSchedContext (Z := Unit) p σ = ({(x, σ)}, False) := by
  unfold getSchedContext
  rw [nd_bind_one (getObject_eq hk)]; rfl

theorem readSchedContext_eq (hk : σ.kheap p = some (.schedContext x n)) :
    readSchedContext (Z := Unit) p σ = some x := by
  show Option.bind (readObject p σ) (fun k => (match k with
    | .schedContext sc _ => Lookup.oreturn sc
    | _ => Lookup.ofail) σ) = _
  simp [readObject, hk, Lookup.oreturn]

theorem isRoundRobin_eq (hk : σ.kheap p = some (.schedContext x n)) :
    isRoundRobin (Z := Unit) p σ = ({(decide (x.scPeriod = 0), σ)}, False) := by
  unfold isRoundRobin
  rw [nd_bind_one (getSchedContext_eq hk)]; rfl

theorem readRefillHead_eq (hk : σ.kheap p = some (.schedContext x n)) (hne : x.scRefills ≠ []) :
    readRefillHead (Z := Unit) p σ = some (refillHd x) := by
  show Option.bind (readSchedContext p σ) (fun sc => Option.bind (Lookup.oassert (sc.scRefills ≠ []) σ)
    (fun _ => Lookup.oreturn (refillHd sc) σ)) = _
  rw [readSchedContext_eq hk]
  simp [Lookup.oassert, hne, Lookup.oreturn]

theorem getRefillHead_eq (hk : σ.kheap p = some (.schedContext x n)) (hne : x.scRefills ≠ []) :
    getRefillHead (Z := Unit) p σ = ({(refillHd x, σ)}, False) := by
  simp [getRefillHead, NonDet.getsThe, readRefillHead_eq hk hne, NonDet.assertOpt]; rfl

theorem getScRefillReady_eq (hk : σ.kheap p = some (.schedContext x n)) (hne : x.scRefills ≠ []) :
    getScRefillReady (Z := Unit) p σ = ({(refillReady σ.curTime (refillHd x), σ)}, False) := by
  have : readScRefillReady (Z := Unit) p σ = some (refillReady σ.curTime (refillHd x)) := by
    show Option.bind (readRefillHead p σ) (fun h => Option.bind (Lookup.asks (fun s : State Unit => s.curTime) σ)
      (fun ct => Lookup.oreturn (refillReady ct h) σ)) = _
    rw [readRefillHead_eq hk hne]; rfl
  simp [getScRefillReady, NonDet.getsThe, this, NonDet.assertOpt]; rfl

theorem getScRefillSufficient_eq (hk : σ.kheap p = some (.schedContext x n)) (hne : x.scRefills ≠ [])
    (u : Ticks) :
    getScRefillSufficient (Z := Unit) p u σ = ({(refillSufficient u (refillHd x), σ)}, False) := by
  have : readScRefillSufficient (Z := Unit) p u σ = some (refillSufficient u (refillHd x)) := by
    show Option.bind (readRefillHead p σ) (fun h => Lookup.oreturn (refillSufficient u h) σ) = _
    rw [readRefillHead_eq hk hne]; rfl
  simp [getScRefillSufficient, NonDet.getsThe, this, NonDet.assertOpt]; rfl

theorem updateSchedContext_eq (hk : σ.kheap p = some (.schedContext x n)) (f : SchedContext → SchedContext) :
    updateSchedContext (Z := Unit) p f σ = ({((), updSc σ p (f x) n)}, False) := by
  unfold updateSchedContext
  rw [nd_bind_one (getObject_eq hk)]
  exact setObject_eq hk rfl

theorem updateRefillHd_eq (hk : σ.kheap p = some (.schedContext x n)) (f : Refill → Refill) :
    updateRefillHd (Z := Unit) p f σ =
      ({((), updSc σ p { x with scRefills := f (the x.scRefills.head?) :: x.scRefills.tail } n)}, False) :=
  updateSchedContext_eq hk _

theorem refillPopHead_eq (hk : σ.kheap p = some (.schedContext x n)) (hne : x.scRefills ≠ []) :
    refillPopHead (Z := Unit) p σ =
      ({(refillHd x, updSc σ p { x with scRefills := x.scRefills.tail } n)}, False) := by
  unfold refillPopHead
  rw [nd_bind_one (getRefillHead_eq hk hne), nd_bind_one (updateSchedContext_eq hk _)]; rfl

theorem refillHeadOverlapping_eq (hk : σ.kheap p = some (.schedContext x n)) :
    refillHeadOverlapping (Z := Unit) p σ = some (decide (x.scRefills.length > 1 ∧
      (the x.scRefills.tail.head?).rTime ≤ (refillHd x).rTime + (refillHd x).rAmount)) := by
  show Option.bind (readSchedContext p σ) (fun sc => Lookup.oreturn _ σ) = _
  rw [readSchedContext_eq hk]; rfl

end Spec

/-! ## The ring as a list -/

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]

theorem refills_length (s : S) (sc : obj.Sc) : (L.refills s sc).length = L.size s sc := by
  simp [LawfulStore.refills]

theorem refills_cons {s : S} {sc : obj.Sc} {sb : Nat} (hW : RefillsWF st s sc sb) :
    L.refills s sc = L.rf s sc 0 :: (List.range (L.size s sc - 1)).map (fun k => L.rf s sc (k + 1)) := by
  unfold LawfulStore.refills
  obtain ⟨m, hm⟩ : ∃ m, L.size s sc = m + 1 := ⟨L.size s sc - 1, by have := hW.size_pos; omega⟩
  rw [hm, List.range_succ_eq_map]
  simp

theorem refills_ne {s : S} {sc : obj.Sc} {sb : Nat} (hW : RefillsWF st s sc sb) :
    (L.refills s sc).map toRefill ≠ [] := by
  rw [refills_cons hW]; simp

theorem refillHd_eq {s : S} {sc : obj.Sc} {sb : Nat} (hW : RefillsWF st s sc sb) {x : Fl4Spec.SchedContext}
    (hx : x.scRefills = (L.refills s sc).map toRefill) : Fl4Spec.refillHd x = toRefill (L.rf s sc 0) := by
  unfold Fl4Spec.refillHd; rw [hx, refills_cons hW]; rfl

theorem rf0_eq {s : S} {sc : obj.Sc} {sb : Nat} (hW : RefillsWF st s sc sb) :
    L.rf s sc 0 = L.refill s sc (L.rhead s sc) := by rw [LawfulStore.rf, hW.ix_zero]

end

end

end Fl4Proofs.P3.Sched
