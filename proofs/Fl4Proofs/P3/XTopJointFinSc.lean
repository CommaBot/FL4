/-
P3 (DESIGN.md §9), CSpace: **a final SC cap's finalisation at `J`**: its
premises and the readiness of its slot after (toward `jFinAt_sc`,
XTopJointDelR).

FL4's `finalise_cap_object` of a final SC cap runs `unbind_all_tcbs`,
`unbind_ntfn`, `unbind_reply`, the yielder's `complete_yield_to`, then
clears `REFILL_MAX` and `SPORADIC`; it never writes the current-SC word.

* `JAtZ.sc_ready`: an SC cap's slot is ready (`EmptyReady`) once the SC is
  dead (P1's `fin_cap_sc.dead`: its `TCB`, `REPLY` and `NTFN` words null),
  given the cap's size is the SC's (`JScCapHyp`) and the SC is not the
  current SC (`EmptyReady`'s current-SC clause: no other cap covers the SC
  of a final cap).

Named premises:

* `JScCapHyp` [J]: an SC cap in a slot names an SC of P1's heap of the
  cap's size (l4v `valid_cap`'s `obj_bits`, P1's `CapTyped` lacks SC caps),
  whose bound thread, if any, is neither the scheduler action nor the idle
  thread (P1's `fin_cap_sc` preconditions; l4v `valid_sched_action`,
  `valid_global_refs`; the CSpace side's `JState.sc`/`JState.act`).
* `JScCurHyp` [J]: a final SC cap's SC is not the current SC word. **Not an
  l4v invariant** (a thread may delete the last cap to its own SC; seL4 and
  FL4 leave `ksCurSC` dangling, inactive, until the next `schedule`). It is
  what `JAtZ` needs as it stands: `JKern.cscH`/`cscLive` keep the current
  SC in `H` and out of the dead set, so `EmptyReady` asks another cap to
  cover it, which a final cap's SC lacks. Dropping it needs `JKern` to
  accept an uncovered inactive current SC (and `schedule`'s side to read
  no field of it but `REFILL_MAX`).
* `JScFinHyp` [J], **a whole-operation premise (undone work)**: from
  `JAtZ`, FL4's `finalise_cap` of a final SC cap (not the current SC)
  against the spec's `finalise_cap`, `JAtZ` after at fresh VSpace sets,
  the slots and the kernel-state base kept. Proved at `XTop` only
  (XTopFinSc's `xFinSc_of`, with `ScYieldFinHyp`); the `JAtZ` lift across
  the five steps is not: the `JRest` fields (`JAtZ.sc_frame` for the three
  unbinds and the inactive SC, but `CallW'` words for `unbind_reply`; the
  yielder's `complete_yield_to` writes registers outside `TFoot` and its
  `IRel` proof asks `YieldRel` at every `IRel` state), the scheduler
  fields (`CurOwnW`, `OffOK`, `CurInv` when the SC's thread is the current
  thread: the spec reschedules), the dead set and P1's `BlkOK` per step
  (P1 proves it for the whole, `fin_cap_sc.slots`).
-/
import Fl4Proofs.P3.XTopJointEmpty
import Fl4Proofs.P3.ScDeadStep
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **Hypothesis: an SC cap's object at `J`** [J] (module docstring). -/
def JScCapHyp (AR : A → Fl4Spec.Cr3 → Prop) (th : TypedHeap) : Prop :=
  ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64) (s : S) (a : A)
    (σ : Fl4Spec.State Unit), Z.th = th → JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ →
    ∀ (sl : Fl4Spec.CslotPtr) (p sb : U64), AbsSlot Z.th sl →
      capAt (L.mem s) (cslotAddr sl) = ok (.SchedContext p sb) →
      H p = some (.sc sb.val) ∧
      (L.mem s (P1.scTcbA p) ≠ 0#u64 → L.actionW s ≠ L.mem s (P1.scTcbA p)) ∧
      (L.mem s (P1.scTcbA p) ≠ 0#u64 → L.idleW s ≠ L.mem s (P1.scTcbA p))

/-- **Hypothesis: a final SC cap's SC is not the current SC** [J] (module
docstring: not an l4v invariant, a gap of `JKern`'s current SC). -/
def JScCurHyp (AR : A → Fl4Spec.Cr3 → Prop) (th : TypedHeap) : Prop :=
  ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64) (s : S) (a : A)
    (σ : Fl4Spec.State Unit), Z.th = th → JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ →
    ∀ (sl : Fl4Spec.CslotPtr) (p sb : U64), AbsSlot Z.th sl →
      capAt (L.mem s) (cslotAddr sl) = ok (.SchedContext p sb) →
      Fl4Spec.isFinalCap' (absCap (.SchedContext p sb)) σ → L.cscW s ≠ p

/-- **Hypothesis: a final SC cap's finalisation at `J`** [J] (module
docstring: a whole-operation premise, undone work; asked of an SC other
than the current one). -/
def JScFinHyp (AR : A → Fl4Spec.Cr3 → Prop) (th : TypedHeap) : Prop :=
  ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64) (s : S) (a : A)
    (σ : Fl4Spec.State Unit), Z.th = th → JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ →
    ∀ (sl : Fl4Spec.CslotPtr) (p sb : U64), AbsSlot Z.th sl →
      capAt (L.mem s) (cslotAddr sl) = ok (.SchedContext p sb) →
      Fl4Spec.isFinalCap' (absCap (.SchedContext p sb)) σ → L.cscW s ≠ p →
      objects.finalise_cap st arI s a (.SchedContext p sb) true false ⦃ res =>
        res.1 = (capability.Cap.Null, capability.Cap.Null) ∧
        ∃ σ' V' Ac' Lst' D', ((absCap res.1.1, absCap res.1.2), σ') ∈
            (Fl4Spec.finaliseCap (Z := Unit) (absCap (.SchedContext p sb)) true σ).1 ∧
          JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' res.2.1 res.2.2 σ' ∧
          SlotsSame Z.th (L.mem s) (L.mem res.2.1) ∧ L.ksb res.2.1 = L.ksb s ⦄

/-- **An SC cap's slot is ready once the SC is dead** (as `JAtZ.ep_ready`),
the cap of the SC's size and the SC not the current one. -/
theorem JAtZ.sc_ready {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {x : U64} {p sb : U64}
    (hcv : capV (L.mem s) x = .SchedContext p sb) (hHp : H p = some (.sc sb.val)) (hd : DeadP (L := L) H s p)
    (hcur : L.cscW s ≠ p) :
    EmptyReady (L := L) H Z.G s x := by
  have hpfit : p.val + 2 ^ sb.val ≤ 2 ^ 64 := by
    have := J.kern.heap.fits p _ hHp
    simpa only [P1.HKind.bits] using this
  have hp0 : p ≠ 0#u64 := fun e => by rw [e, J.kern.h0] at hHp; cases hHp
  have hp1 : 1 ≤ p.val := by
    rcases Nat.eq_zero_or_pos p.val with h | h
    · exact absurd (UScalar.eq_of_val_eq (by rw [h]; rfl)) hp0
    · exact h
  have hsb : sb.val < 64 := by
    by_contra hge
    have : 2 ^ 64 ≤ 2 ^ sb.val := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  obtain ⟨e1, e2⟩ := range_sc p sb hsb hpfit
  unfold EmptyReady
  rw [hcv, e1, e2]
  intro _ _
  have hout : ∀ q k, H q = some k → q ≠ p → q.val + 2 ^ k.bits ≤ p.val ∨ p.val + 2 ^ sb.val ≤ q.val := by
    intro q k hq hne
    have := J.kern.heap.disj q k p (.sc sb.val) hq hHp hne
    simpa only [P1.HKind.bits] using this
  have hpos : 1 ≤ 2 ^ sb.val := Nat.one_le_two_pow
  refine ⟨fun lo hi hlh h1 h2 => ?_, fun z hz h1 h2 => ?_⟩
  · right
    intro q hq
    by_cases e : q = p
    · subst e; exact hd
    · cases hk : H q with
      | none => exact deadP_none hk
      | some k =>
        exfalso
        have : 1 ≤ 2 ^ k.bits := Nat.one_le_two_pow
        rcases hout q k hk e with h | h <;> omega
  · exfalso
    have : 1 ≤ 2 ^ (P1.HKind.sc z).bits := Nat.one_le_two_pow
    rcases hout _ _ hz hcur with h | h <;> omega

end

end

end Fl4Proofs.P3
