/-
P3 (DESIGN.md §9), CSpace: **the deletion's object work and preemption
points at `XTop`**, the named premises of CNode Delete and Revoke at the
composite relation, in the plain `XTopAt` shape (no CSpace-internal types
beyond `DState`'s), so that the IPC, scheduler and VSpace sides can prove
them.

The spec's finalisation and preemption point are nondeterministic (the
time stamp, the active IRQ, the work-unit choice), so the composite side
chooses the spec outcome: each premise is a WP statement giving, beside
the CSpace facts of its CSpace-level counterpart, `XTopAt` at its chosen
outcome. The deletion loops thread `XTop` as an invariant through these
(the `W`-carrying versions of `FinObjHyp`, `PPHypD`, `PostDelHyp`).

* `FinXPost`, `XFinAt K`: `FinWorkAt K`'s post with `XTopAt` after.
* `XFinHyps`: one field per kind of `finWorkHyp_split` (notification,
  reply, endpoint, thread, scheduling context, IRQ handler, VCPU/EPT, IO
  port, the native VSpace caps); `XFinHyps.at` dispatches.
* `XPreemptHyp`: the preemption point, the cap slots kept, `XTopAt` after.
-/
import Fl4Proofs.P3.XTopCaps
import Fl4Proofs.P3.DelObjK
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **`FinWorkAt`'s post with `XTopAt` after**, at sets `Z` with the
ghost changed. -/
def FinXPost (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (s : S) (σ : Fl4Spec.State Unit)
    (sl : Fl4Spec.CslotPtr) (c : capability.Cap) (r : (capability.Cap × capability.Cap) × S × A) : Prop :=
  r.1.1 = finRem c (decide (Fl4Spec.isFinalCap' (absCap c) σ)) ∧ CleanCap r.1.2 ∧ CapWf r.1.2 ∧
  ∃ σ' G', ((absCap r.1.1, absCap r.1.2), σ') ∈
      (Fl4Spec.finaliseCap (Z := Unit) (absCap c) (decide (Fl4Spec.isFinalCap' (absCap c) σ)) σ).1 ∧
    DState (L := L) Z.th r.2.1 σ' G' ∧ capV (L.mem r.2.1) (cslotAddr sl) = c ∧
    (∀ y, IsSlot Z.th y → y ≠ cslotAddr sl → capV (L.mem r.2.1) y = capV (L.mem s) y ∨
      (capV (L.mem r.2.1) y = .Null ∧ isZb (capV (L.mem s) y) = false)) ∧
    MdbStep (L.mem s) Z.G (L.mem r.2.1) G' ∧
    XTopAt (L := L) AR { Z with G := G' } r.2.1 r.2.2 σ' ∧ L.ksb r.2.1 = L.ksb s

/-- **Hypothesis: the finalisation of a cap of kind `K` at `XTop`**: from
`XTopAt` (with `KsApart`, the typed heap's TCBs among the sets') and
`FinWorkAt`'s premises, `FinXPost`. -/
def XFinAt (K : capability.Cap → Prop) (AR : A → Fl4Spec.Cr3 → Prop) (th : TypedHeap) : Prop :=
  ∀ (Z : XSets) (s : S) (a : A) (σ : Fl4Spec.State Unit) (sl : Fl4Spec.CslotPtr) (c : capability.Cap),
    Z.th = th → XTopAt (L := L) AR Z s a σ → KsApart Z.N Z.T Z.E Z.R Z.B (L.ksb s) →
    (∀ t, th t = some .tcb → t ∈ Z.T) →
    K c → DState (L := L) th s σ Z.G → AbsSlot th sl → capAt (L.mem s) (cslotAddr sl) = ok c → FinObjKind c →
    FinWork c (decide (Fl4Spec.isFinalCap' (absCap c) σ)) →
    objects.finalise_cap st arI s a c (decide (Fl4Spec.isFinalCap' (absCap c) σ)) false ⦃ r =>
      FinXPost (L := L) AR Z s σ sl c r ⦄

/-- **The finalisation premises at `XTop`**, one per kind (the kinds of
`finWorkHyp_split`). The IPC side proves `ntfn`, `reply`, `ep`; the
scheduler side `thread` and `sc`; the VSpace side `rest`; `irq`, `vm` and
`io` are the composite forms of `IrqFinHyp`, `VmFinHyp`, `IoPortFinHyp`. -/
structure XFinHyps (AR : A → Fl4Spec.Cr3 → Prop) (th : TypedHeap) : Prop where
  ntfn : XFinAt (L := L) arI FinNtfnK AR th
  reply : XFinAt (L := L) arI FinReplyK AR th
  ep : XFinAt (L := L) arI FinEpK AR th
  thread : XFinAt (L := L) arI FinThreadK AR th
  sc : XFinAt (L := L) arI FinScK AR th
  irq : XFinAt (L := L) arI FinIrqK AR th
  vm : XFinAt (L := L) arI FinVmK AR th
  io : XFinAt (L := L) arI FinIoK AR th
  rest : XFinAt (L := L) arI FinRestK AR th

/-- **Any object cap's finalisation at `XTop`**, by its kind. -/
theorem XFinHyps.at {AR : A → Fl4Spec.Cr3 → Prop} {th : TypedHeap} (h : XFinHyps (L := L) arI AR th) :
    XFinAt (L := L) arI (fun _ => True) AR th := by
  intro Z s a σ sl c hth hX hK hTh _
  by_cases h1 : FinNtfnK c
  · exact h.ntfn Z s a σ sl c hth hX hK hTh h1
  by_cases h2 : FinReplyK c
  · exact h.reply Z s a σ sl c hth hX hK hTh h2
  by_cases h3 : FinEpK c
  · exact h.ep Z s a σ sl c hth hX hK hTh h3
  by_cases h4 : FinThreadK c
  · exact h.thread Z s a σ sl c hth hX hK hTh h4
  by_cases h5 : FinScK c
  · exact h.sc Z s a σ sl c hth hX hK hTh h5
  by_cases h6 : FinIrqK c
  · exact h.irq Z s a σ sl c hth hX hK hTh h6
  by_cases h7 : FinVmK c
  · exact h.vm Z s a σ sl c hth hX hK hTh h7
  by_cases h8 : FinIoK c
  · exact h.io Z s a σ sl c hth hX hK hTh h8
  exact h.rest Z s a σ sl c hth hX hK hTh ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

/-- **`XFinAt` gives `FinWorkAt`'s post** (forgetting `XTopAt`). -/
theorem FinXPost.fin {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {s : S} {σ : Fl4Spec.State Unit}
    {sl : Fl4Spec.CslotPtr} {c : capability.Cap} {r : (capability.Cap × capability.Cap) × S × A}
    (h : FinXPost (L := L) AR Z s σ sl c r) :
    r.1.1 = finRem c (decide (Fl4Spec.isFinalCap' (absCap c) σ)) ∧ CleanCap r.1.2 ∧ CapWf r.1.2 ∧
      ∃ σ' G', ((absCap r.1.1, absCap r.1.2), σ') ∈
          (Fl4Spec.finaliseCap (Z := Unit) (absCap c) (decide (Fl4Spec.isFinalCap' (absCap c) σ)) σ).1 ∧
        DState (L := L) Z.th r.2.1 σ' G' ∧ capV (L.mem r.2.1) (cslotAddr sl) = c ∧
        (∀ y, IsSlot Z.th y → y ≠ cslotAddr sl → capV (L.mem r.2.1) y = capV (L.mem s) y ∨
          (capV (L.mem r.2.1) y = .Null ∧ isZb (capV (L.mem s) y) = false)) ∧
        MdbStep (L.mem s) Z.G (L.mem r.2.1) G' := by
  obtain ⟨h1, h2, h3, σ', G', h4, h5, h6, h7, h8, -⟩ := h
  exact ⟨h1, h2, h3, σ', G', h4, h5, h6, h7, h8⟩

/-- **Hypothesis: the preemption point at `XTop`** (the scheduler's): from
`XTopAt` (with `KsApart`, the typed heap's TCBs among the sets'), FL4's
`preemption_point` keeps the cap slots and the kernel-global base, and has a
spec outcome of the same kind (Ok, or preempted) with `XTopAt` after, at
the same sets. -/
def XPreemptHyp (AR : A → Fl4Spec.Cr3 → Prop) (th : TypedHeap) : Prop :=
  ∀ (Z : XSets) (s : S) (a : A) (σ : Fl4Spec.State Unit),
    Z.th = th → XTopAt (L := L) AR Z s a σ → KsApart Z.N Z.T Z.E Z.R Z.B (L.ksb s) →
    (∀ t, th t = some .tcb → t ∈ Z.T) →
    sched.preemption_point st arI s a ⦃ r =>
      SlotsSame th (L.mem s) (L.mem r.2.1) ∧ L.ksb r.2.1 = L.ksb s ∧ ∃ σ',
        ((r.1 = .Ok () ∧ (.ok (), σ') ∈ ((Fl4Spec.preemptionPoint (Z := Unit)).run σ).1) ∨
          (r.1 = .Err .Preempted ∧ (.error (), σ') ∈ ((Fl4Spec.preemptionPoint (Z := Unit)).run σ).1)) ∧
        XTopAt (L := L) AR Z r.2.1 r.2.2 σ' ⦄

/-- **`XPreemptHyp` gives `PPHypD`'s post** at an `XTopAt` state, with
`XTopAt` after. -/
theorem XPreemptHyp.pp {AR : A → Fl4Spec.Cr3 → Prop} {th : TypedHeap} (h : XPreemptHyp (L := L) arI AR th)
    {Z : XSets} {s : S} {a : A} {σ : Fl4Spec.State Unit} (hth : Z.th = th) (hX : XTopAt (L := L) AR Z s a σ)
    (hK : KsApart Z.N Z.T Z.E Z.R Z.B (L.ksb s)) (hTh : ∀ t, th t = some .tcb → t ∈ Z.T) :
    sched.preemption_point st arI s a ⦃ r =>
      SlotsSame th (L.mem s) (L.mem r.2.1) ∧ ∃ σ',
        ((r.1 = .Ok () ∧ (.ok (), σ') ∈ ((Fl4Spec.preemptionPoint (Z := Unit)).run σ).1) ∨
          (r.1 = .Err .Preempted ∧ (.error (), σ') ∈ ((Fl4Spec.preemptionPoint (Z := Unit)).run σ).1)) ∧
        CRel th (L.mem r.2.1) σ' Z.G ∧ XTopAt (L := L) AR Z r.2.1 r.2.2 σ' ∧ L.ksb r.2.1 = L.ksb s ⦄ := by
  refine WP.spec_mono (h Z s a σ hth hX hK hTh) ?_
  rintro r ⟨hS, hk, σ', ho, hX'⟩
  subst hth
  exact ⟨hS, σ', ho, hX'.rel.2.1, hX', hk⟩

end

end

end Fl4Proofs.P3
