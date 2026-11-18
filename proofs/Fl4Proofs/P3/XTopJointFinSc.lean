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
  `valid_global_refs`; the CSpace side's `JState.sc`/`JState.act`), an SC
  of the spec's heap other than the idle SC (JProducers' `ScCapJ`: l4v
  `valid_cap`, `valid_global_refs`).
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
import Fl4Proofs.P3.XTopJointFinThread
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
      (L.mem s (P1.scTcbA p) ≠ 0#u64 → L.idleW s ≠ L.mem s (P1.scTcbA p)) ∧
      (∃ y n, σ.kheap p.bv = some (.schedContext y n)) ∧ p.bv ≠ Fl4Spec.idleScPtr

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

/-- **Hypothesis: the yielder's `complete_yield_to` at `J`** [J-step]: the
statement of XTopJointFinThread's `JThreadFinHyps.yieldTo` (one premise
shared by the thread and the SC finalisations; XTop: `ScYieldFinHyp`). -/
def JYieldToHyp (AR : A → Fl4Spec.Cr3 → Prop) (th : TypedHeap) : Prop :=
  ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64) (s : S)
    (a : A) (σ : Fl4Spec.State Unit), Z.th = th → JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ →
    ∀ q : U64, L.mem s (scYieldFromA q) ≠ 0#u64 →
      schedcontext.complete_yield_to st arI s a (L.mem s (scYieldFromA q)) ⦃ r => ∃ σ',
        Fl4Spec.completeYieldTo (Z := Unit) (L.mem s (scYieldFromA q)).bv σ = ({((), σ')}, False) ∧
        JTP (L := L) arI AR Z H Cs r.1 r.2 σ' ⦄

theorem JThreadFinHyps.yieldToH {AR : A → Fl4Spec.Cr3 → Prop} {th : TypedHeap}
    (h : JThreadFinHyps (L := L) arI AR th) : JYieldToHyp (L := L) arI AR th := h.yieldTo

/-- **The SC steps of a final SC cap's finalisation at `J`** [J-step], each
one FL4 step at a `JAtZ` state against the spec's, `JAtZ` after (`JTP`);
asked of an SC `p` of the SCs, not null, not the idle SC, not the current SC
word, with the SC's links cleared by the earlier steps (P1's
`unbind_all_tcbs.blk`, `unbind_ntfn.blk`, `unbind_reply.blk`). XTop:
`xFinSc_of`'s steps (`unbind_all_tcbs_refines`, `unbind_ntfn_refines`,
`unbind_reply_refines`, `SchedRel.set_inactive`, each with `xtop_sc_step`
or `xtop_sc_stepCW`). -/
structure JScFinSteps (AR : A → Fl4Spec.Cr3 → Prop) (th : TypedHeap) : Prop where
  /-- `unbind_all_tcbs` at `J` (its thread neither the scheduler action nor
  idle, P1's `unbind_all_tcbs.blk` preconditions). -/
  unbindAll : ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64) (s : S)
    (a : A) (σ : Fl4Spec.State Unit), Z.th = th → JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ →
    ∀ p : U64, p ∈ Z.C → p ≠ 0#u64 → p.bv ≠ Fl4Spec.idleScPtr → L.cscW s ≠ p →
      (L.mem s (P1.scTcbA p) ≠ 0#u64 → L.actionW s ≠ L.mem s (P1.scTcbA p)) →
      (L.mem s (P1.scTcbA p) ≠ 0#u64 → L.idleW s ≠ L.mem s (P1.scTcbA p)) →
      schedcontext.unbind_all_tcbs st arI s a p ⦃ r => ∃ σ',
        Fl4Spec.schedContextUnbindAllTcbs (Z := Unit) p.bv σ = ({((), σ')}, False) ∧
        JTP (L := L) arI AR Z H Cs r.1 r.2 σ' ⦄
  /-- `unbind_ntfn` at `J`, the SC's thread unbound. -/
  unbindNtfn : ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64) (s : S)
    (a : A) (σ : Fl4Spec.State Unit), Z.th = th → JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ →
    ∀ p : U64, p ∈ Z.C → p ≠ 0#u64 → p.bv ≠ Fl4Spec.idleScPtr → L.cscW s ≠ p →
      L.mem s (P1.scTcbA p) = 0#u64 →
      schedcontext.unbind_ntfn st s p ⦃ s' => ∃ σ',
        Fl4Spec.schedContextUnbindNtfn (Z := Unit) p.bv σ = ({((), σ')}, False) ∧
        JTP (L := L) arI AR Z H Cs s' a σ' ⦄
  /-- `unbind_reply` at `J`, the SC's thread and notification unbound (its
  writes: the head reply's `NEXT` word, a call-stack word `CallW'`). -/
  unbindReply : ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64) (s : S)
    (a : A) (σ : Fl4Spec.State Unit), Z.th = th → JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ →
    ∀ p : U64, p ∈ Z.C → p ≠ 0#u64 → p.bv ≠ Fl4Spec.idleScPtr → L.cscW s ≠ p →
      L.mem s (P1.scTcbA p) = 0#u64 → L.mem s (P1.scNtfnA p) = 0#u64 →
      schedcontext.unbind_reply st s p ⦃ s' => ∃ σ',
        Fl4Spec.schedContextUnbindReply (Z := Unit) p.bv σ = ({((), σ')}, False) ∧
        JTP (L := L) arI AR Z H Cs s' a σ' ⦄
  /-- The SC made inactive (`REFILL_MAX` and `SPORADIC` cleared) at `J`, its
  thread, notification and reply unbound. -/
  setInactive : ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64) (s : S)
    (a : A) (σ : Fl4Spec.State Unit), Z.th = th → JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ →
    ∀ p : U64, p ∈ Z.C → p ≠ 0#u64 → p.bv ≠ Fl4Spec.idleScPtr → L.cscW s ≠ p →
      L.mem s (P1.scTcbA p) = 0#u64 → L.mem s (P1.scNtfnA p) = 0#u64 → L.mem s (P1.scReplyA p) = 0#u64 →
      ∃ σ', Fl4Spec.schedContextSetInactive (Z := Unit) p.bv σ = ({((), σ')}, False) ∧
        JTP (L := L) arI AR Z H Cs (L.wr (L.wr s (maxA p) 0#u64) (scW p 64#u64) 0#u64) a σ'

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

set_option maxHeartbeats 16000000 in
/-- **`JAtZ` across a final SC cap's finalisation** (as XTop's `xFinSc_of`),
from the SC steps `JScFinSteps` and the yielder's `JYieldToHyp`; the SC's
links cleared and the current SC word kept along the way by P1's per-step
lemmas (`unbind_all_tcbs.blk`, `unbind_ntfn.blk`, `unbind_reply.blk`,
`complete_yield_to.blkS`) at each step's `BlkOK`. -/
theorem JAtZ.finScJ {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (hT : P0.ArchTotal arI) (hS : JScFinSteps (L := L) arI AR Z.th) (hY : JYieldToHyp (L := L) arI AR Z.th)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {p sb : U64} (hpC : p ∈ Z.C) (hp0 : p ≠ 0#u64)
    (hpi : p.bv ≠ Fl4Spec.idleScPtr) (hcur : L.cscW s ≠ p) (hpS : p ∈ P1.Heap.scs H)
    (hna : L.mem s (P1.scTcbA p) ≠ 0#u64 → L.actionW s ≠ L.mem s (P1.scTcbA p))
    (hidle : L.mem s (P1.scTcbA p) ≠ 0#u64 → L.idleW s ≠ L.mem s (P1.scTcbA p)) :
    objects.finalise_cap st arI s a (.SchedContext p sb) true false ⦃ r => ∃ σ',
      ((Fl4Spec.Cap.nullCap, Fl4Spec.Cap.nullCap), σ') ∈
        (Fl4Spec.finaliseCap (Z := Unit) (absCap (.SchedContext p sb)) true σ).1 ∧
      JTP (L := L) arI AR Z H Cs r.2.1 r.2.2 σ' ⦄ := by
  rw [P1.fin_cap_eq_obj (by simp)]
  unfold objects.finalise_cap_object
  simp only [↓reduceIte]
  -- `unbind_all_tcbs`
  refine WP.spec_bind (WP.spec_and (hS.unbindAll Z H Cs Ac Lst D s a σ rfl J p hpC hp0 hpi hcur hna hidle)
    (P1.schedcontext.unbind_all_tcbs.blk hT s a p J.blk hpS hp0 hna hidle)) ?_
  rintro ⟨s1, a1⟩ ⟨⟨σ1, he1, V1, Ac1, Lst1, D1, J1⟩, hP1⟩
  try simp only [WP.uncurry'_pair] at hP1
  obtain ⟨-, -, -, -, t1, c1⟩ := hP1
  have hcur1 : L.cscW s1 ≠ p := by rw [c1]; exact hcur
  -- `unbind_ntfn`
  refine WP.spec_bind (WP.spec_and (hS.unbindNtfn (Z.mv Z.G V1) H Cs Ac1 Lst1 D1 s1 a1 σ1 rfl J1 p hpC hp0 hpi hcur1 t1)
    (P1.schedcontext.unbind_ntfn.blk s1 p J1.blk fun _ => hpS)) ?_
  rintro s2 ⟨⟨σ2, he2, V2, Ac2, Lst2, D2, J2⟩, -, -, t2, c2, n2⟩
  have hcur2 : L.cscW s2 ≠ p := by rw [c2]; exact hcur1
  have t2' : L.mem s2 (P1.scTcbA p) = 0#u64 := by rw [t2, t1]
  -- `unbind_reply`
  refine WP.spec_bind (WP.spec_and
    (hS.unbindReply (Z.mv Z.G V2) H Cs Ac2 Lst2 D2 s2 a1 σ2 rfl J2 p hpC hp0 hpi hcur2 t2' (n2 hp0))
    (P1.schedcontext.unbind_reply.blk s2 p p J2.blk (fun _ => hpS) hpS)) ?_
  rintro s3 ⟨⟨σ3, he3, V3, Ac3, Lst3, D3, J3⟩, -, -, k3, r3⟩
  have hcur3 : L.cscW s3 ≠ p := by rw [k3.2.2.1]; exact hcur2
  have t3 : L.mem s3 (P1.scTcbA p) = 0#u64 := by rw [k3.1, t2']
  have n3 : L.mem s3 (P1.scNtfnA p) = 0#u64 := by rw [k3.2.1, n2 hp0]
  have r3' : L.mem s3 (P1.scReplyA p) = 0#u64 := r3 hp0
  obtain ⟨Q3, R3, hc3, hs3⟩ := J3.xtop.fin.1.1.1.lists
  obtain ⟨y3, n3', hk3, hx3⟩ := hs3.scs p hpC
  -- the inactive SC and the post
  have fin5 : ∀ (s4 : S) (a4 : A) (σ4 : Fl4Spec.State Unit) (V4 : XVs) (Ac4 : Set U64) (Lst4 : U64 → List U64)
      (D4 : Set U64), JAtZ (L := L) arI AR (Z.mv Z.G V4) H Cs Ac4 Lst4 D4 s4 a4 σ4 → L.cscW s4 ≠ p →
      L.mem s4 (P1.scTcbA p) = 0#u64 → L.mem s4 (P1.scNtfnA p) = 0#u64 → L.mem s4 (P1.scReplyA p) = 0#u64 →
      Fl4Spec.schedContextUnbindYieldFrom (Z := Unit) p.bv σ3 = ({((), σ4)}, False) →
      (do
        let s5 ← obj.Sc.set_refill_max st p s4 0#u64
        let s6 ← obj.Sc.set_sporadic st p s5 0#u64
        ok ((capability.Cap.Null, capability.Cap.Null), s6, a4)) ⦃ r => ∃ σ',
          ((Fl4Spec.Cap.nullCap, Fl4Spec.Cap.nullCap), σ') ∈
            (Fl4Spec.finaliseCap (Z := Unit) (absCap (.SchedContext p sb)) true σ).1 ∧
          JTP (L := L) arI AR Z H Cs r.2.1 r.2.2 σ' ⦄ := by
    intro s4 a4 σ4 V4 Ac4 Lst4 D4 J4 hcur4 t4 n4 r4 he4
    step with obj.Sc.set_refill_max.spec as ⟨s5, hs5⟩
    step with obj.Sc.set_sporadic.spec2 as ⟨s6, hs6⟩
    subst hs5 hs6
    obtain ⟨σ5, he5, V5, Ac5, Lst5, D5, J5⟩ :=
      hS.setInactive (Z.mv Z.G V4) H Cs Ac4 Lst4 D4 s4 a4 σ4 rfl J4 p hpC hp0 hpi hcur4 t4 n4 r4
    exact ⟨σ5, finSc_mem he1 he2 he3 he4 he5, V5, Ac5, Lst5, D5, J5⟩
  -- the yielder
  step with obj.Sc.yield_from.spec' as ⟨i, hi⟩
  step with obj.Tcb.is_null.spec as ⟨b0, hb0⟩
  by_cases h0 : i = 0#u64
  · have hb : b0 = true := by rw [hb0, h0]; rfl
    simp only [hb, ↓reduceIte, bind_ok]
    refine fin5 s3 a1 σ3 V3 Ac3 Lst3 D3 J3 hcur3 t3 n3 r3' (unbindYieldFrom_none hk3 ?_)
    rw [hx3.yieldFrom, ← scYieldFromA_eq, ← hi, h0, Notif.optRef_zero]
  · have hb : b0 = false := by rw [hb0]; simp [h0]
    simp only [hb, Bool.false_eq_true, ↓reduceIte]
    rw [hi]
    have hy : L.mem s3 (scYieldFromA p) ≠ 0#u64 → L.mem s3 (scYieldFromA p) ∈ P1.Heap.tcbs H := fun hy0 =>
      J3.blk.2.2.1.2.2.yt.2.2 p hpS hy0
    refine WP.spec_bind (WP.spec_and (hY (Z.mv Z.G V3) H Cs Ac3 Lst3 D3 s3 a1 σ3 rfl J3 p (by rw [← hi]; exact h0))
      (P1.schedcontext.complete_yield_to.blkS hT s3 a1 _ p J3.blk hy hpS)) ?_
    rintro ⟨s4, a4⟩ ⟨⟨σ4, e4, V4, Ac4, Lst4, D4, J4⟩, hP4⟩
    try simp only [WP.uncurry'_pair] at hP4
    obtain ⟨-, -, -, k4⟩ := hP4
    refine fin5 s4 a4 σ4 V4 Ac4 Lst4 D4 J4 (by rw [k4.2.2.1]; exact hcur3) (by rw [k4.1, t3])
      (by rw [k4.2.1, n3]) (k4.2.2.2 r3') (unbindYieldFrom_some hk3 ?_ e4)
    rw [hx3.yieldFrom, ← scYieldFromA_eq, Notif.optRef_ne (by rw [← hi]; exact h0)]

/-- **`JScFinHyp` from the SC steps** (`JAtZ.finScJ`), the slots and the
kernel-state base kept by P1's `fin_cap_sc.slots`. -/
theorem jScFin_of {AR : A → Fl4Spec.Cr3 → Prop} {th : TypedHeap} (hT : P0.ArchTotal arI)
    (hS : JScFinSteps (L := L) arI AR th) (hY : JYieldToHyp (L := L) arI AR th) (hC : JScCapHyp (L := L) arI AR th) :
    JScFinHyp (L := L) arI AR th := by
  intro Z H Cs Ac Lst D s a σ hth J sl p sb hA hc _ hcur
  obtain ⟨hHp, hna, hidle, ⟨y0, n0, hk0⟩, hpi⟩ := hC Z H Cs Ac Lst D s a σ hth J sl p sb hA hc
  subst hth
  have hpC : p ∈ Z.C := by
    obtain ⟨q, hq, hqp⟩ := J.obj.sc _ y0 n0 hk0
    rw [← P1.eq_of_bv hqp]; exact hq
  have hpS : p ∈ P1.Heap.scs H := ⟨_, hHp⟩
  have hp0 : p ≠ 0#u64 := fun e => by rw [e, J.kern.h0] at hHp; cases hHp
  refine WP.spec_mono (WP.spec_and (JAtZ.finScJ arI hT hS hY J hpC hp0 hpi hcur hpS hna hidle)
    (P1.fin_cap_sc.slots (ar := arI) hT s a p sb true false J.blk hpS hp0 hna hidle)) ?_
  rintro ⟨⟨rem, cl⟩, s1, a1⟩ ⟨⟨σ1, hm1, V1, Ac1, Lst1, D1, J1⟩, e, -, f, hW1⟩
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  have hSS1 : SlotsSame Z.th (L.mem s) (L.mem s1) :=
    slotsSame_of_capw J.xtop.rel.1 (J.slotCapW (tLowSlots_all _)) hW1
  exact ⟨rfl, σ1, V1, Ac1, Lst1, D1, hm1, J1, hSS1, f.1⟩

end

end

end Fl4Proofs.P3
