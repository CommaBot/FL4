/-
P3 (DESIGN.md §9), scheduling contexts: **the notification proofs'
scheduling-context hypotheses, discharged** from state facts.

* `ActReady.block`: `ActReady` survives blocking a thread on a notification
  (`BlockStep`, NtfnRecv.lean).
* `returnSc_of`: `RecvHyps.returnSc` (with `SR := SchedRel`), from
  `maybe_return_refines` and `ActReady.block`; no hypothesis.
* `DonatePre`: what the donation branch needs at a donation point (l4v
  invariants and the platform's `MIN_BUDGET`; ScDonateRef.lean).
* `donateHyp_of`: `DonateHyp` (hence `RecvHyps.recvTail` and
  `.completeTail`, ScTails.lean) from `DonatePre` at the donation points.
* `wakeHyps_of'`: `WakeHyps` from `DonatePre` and `ActReady` at a wake-up's
  donation point.
-/
import Fl4Proofs.P3.ScDonateRef
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section Spec
open Fl4Spec

/-- **`ActReady` survives blocking a thread on a notification.** -/
theorem _root_.Fl4Proofs.P3.Notif.ActReady.block {σ σ' : State Unit} {t n : ObjRef} (h : ActReady σ)
    (hb : BlockStep σ σ' t n) : ActReady σ' := by
  obtain ⟨hact, hct, hrq, hkd, ⟨xn, yn, hkn, hkn'⟩, ⟨xt, yt, hkt, hkt', -, hrun⟩⟩ := hb
  intro u hu hs
  have hu0 : σ.schedulerAction = .switchThread u := by
    rcases hact with e | e
    · rw [← e]; exact hu
    · rw [e] at hu; cases hu
  have hut : u ≠ t := by
    rintro rfl
    unfold schedulable at hs
    simp [optPred, optMapSome, optMap, tcbsOfKh, tcbOf, hkt', hrun] at hs
  have hun : u ≠ n := by
    rintro rfl
    rw [schedulable_notcb (by rw [tcbsOf_eq, hkn'])] at hs; cases hs
  have hscm : ∀ p, Option.map scActive (scsOf σ' p) = Option.map scActive (scsOf σ p) := by
    intro p
    rw [scsOf_eq, scsOf_eq]
    by_cases et : p = t
    · subst et; rw [hkt, hkt']
    · by_cases en : p = n
      · subst en; rw [hkn, hkn']
      · rw [hkd p et en]
  have hs0 : schedulable u σ = true := by
    rw [← schedulable_congr (by rw [tcbsOf_eq, tcbsOf_eq, hkd u hut hun]) hscm hrq]; exact hs
  obtain ⟨x, scp, hkx, hsc, h1, h2⟩ := h u hu0 hs0
  obtain ⟨y, m, hky, hne, hsuff⟩ := suff_inv h1
  have hrdy := ready_inv h2 hky hne
  have hst : scp ≠ t := by rintro rfl; rw [hkt] at hky; cases hky
  have hsn : scp ≠ n := by rintro rfl; rw [hkn] at hky; cases hky
  have hky' : σ'.kheap scp = some (.schedContext y m) := by rw [hkd scp hst hsn]; exact hky
  refine ⟨x, scp, by rw [hkd u hut hun]; exact hkx, hsc, ?_, ?_⟩
  · rw [getScRefillSufficient_eq hky' hne, hsuff]
  · rw [getScRefillReady_eq hky' hne, hct, hrdy]

end Spec

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]

/-- **`RecvHyps.returnSc`, discharged** for `SchedRel`. -/
theorem returnSc_of {N T C : Set U64} {c : U64} (s : S) (σ0 σ : Fl4Spec.State Unit) (t n : U64)
    (hR : NtfnStateRel N T (L.mem s) σ) (hS : SchedRel st N T C c s σ) (ht : t ∈ T) (hn : n ∈ N)
    (hA : ActReady σ0) (hb : BlockStep σ0 σ t.bv n.bv) :
    TailRef st N T (SchedRel st N T C c) id s σ (notification.maybe_return_sched_context st s n t)
      (Fl4Spec.maybeReturnSc n.bv t.bv) :=
  maybe_return_refines s σ hR hS (hA.block hb) t n ht hn

/-- What the donation branch of `maybe_donate_sched_context` needs (see
ScDonateRef.lean): `RelOK`, the platform's `MIN_BUDGET`, the notification's
SC in `C`, and a thread without SC in no ready queue. -/
structure DonatePre (st : machine.Store S) (ar : machine.Arch A) [L : LawfulStore st] (C : Set U64)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (t n : U64) : Prop where
  rel : RelOK σ
  minBudget : sporadic.min_budget ar a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄
  ntfnSc : L.mem s (nScA n) ≠ 0#u64 → L.mem s (nScA n) ∈ C
  notQueued : L.mem s (scA t) = 0#u64 → ∀ x, σ.kheap t.bv = some (.tcb x) →
    t.bv ∉ σ.readyQueues x.tcbDomain x.tcbPriority

/-- **`DonateHyp` from `DonatePre`** at the donation points. -/
theorem donateHyp_of {N T C : Set U64} {c : U64}
    (hI : ∀ s (a : A) σ (t n : U64), NtfnStateRel N T (L.mem s) σ → SchedRel st N T C c s σ → t ∈ T → n ∈ N →
      DonatePre st ar C s a σ t n) :
    DonateHyp st ar N T C c := by
  intro s a σ t n hR hS ht hn
  have hp := hI s a σ t n hR hS ht hn
  refine WP.spec_mono (maybe_donate_refines s a σ hR hS hp.rel hp.minBudget t n ht hn hp.ntfnSc hp.notQueued) ?_
  rintro r ⟨σ1, h1, h2, h3, h4, -⟩
  exact ⟨σ1, h1, h2, h3, h4⟩

/-- **`WakeHyps` from `DonatePre` and `ActReady`** at a wake-up's donation
point. -/
theorem wakeHyps_of' {N T C : Set U64} {c : U64}
    (hI : ∀ s (a : A) σ (t n : U64) (x : Fl4Spec.Tcb), NtfnStateRel N T (L.mem s) σ → SchedRel st N T C c s σ →
      t ∈ T → n ∈ N → σ.kheap t.bv = some (.tcb x) → x.tcbState = .running →
      DonatePre st ar C s a σ t n ∧ ActReady σ) :
    WakeHyps st ar N T C c := by
  refine wakeHyps_of (fun s a σ t n x hR hS ht hn hk hx => ?_)
  obtain ⟨hp, hA⟩ := hI s a σ t n x hR hS ht hn hk hx
  refine WP.spec_mono (maybe_donate_refines s a σ hR hS hp.rel hp.minBudget t n ht hn hp.ntfnSc hp.notQueued) ?_
  rintro r ⟨σ1, h1, h2, h3, h4, h5⟩
  exact ⟨σ1, h1, h2, h3, h4, h5 hA⟩

end

end

end Fl4Proofs.P3.Sched
