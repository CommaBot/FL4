/-
P3 (DESIGN.md §9), kernel entry (KENTRY-PLAN.md sch10 (2)): **`kernel_entryJ6`:
`kernel_entryJ5` with the IRQ case of `KPreFinRestHyp` [W] closed for the
covered preemption path**.

XTopJointIrqZR gives `handle_interrupt` from `JAt` with `JAt` after
(`jIrqHypJ_of`), so the covered preemption path (`PPCov ∨ PPCovT ∨ PPCovI`)
ends in `PPQJ` (spec failure or `JAt`) and the invoking dispatch in `PPQC`
(`dispatch_invokeJEPZEC`). Here:

* `DispPostR`: `DispPost` with `JAtZR` at an ok outcome (sch9's note: the
  finish only uses `JAtZR`).
* `KDispHypsR`: `KDispHypsS` with `mid` [W] ending in `DispPostR` with `PPQC`
  (relaxed at an ok outcome: `JAtZR` instead of `JAtZS`; the preempted outcome
  as for the invoking syscalls: `PPQC`, which `hPre_ofZKC` gives for every
  invocation followed by `after_invocation`).
* `dispatch_allR`: `dispatch_allS` over `dispatch_invokeJEPZEC`.
* `KPreFinRestHypC` [W]: `KPreFinRestHyp` over `PPQC` states. The `XTopAt`
  disjunct of `PPQ` (a handled line) is left only at `RestE` holes (the
  output of `JPreemptRestHypE`, kp line). What
  is left: (a) a `RestE` hole (`JHoleAt` or the IRQ's `XTopAt`, both from
  `JPreemptRestHypE`'s post, kp14), (b) a failing spec preemption path.
* `kPreFinHypC_of`, `kernel_entryJ6`: as `kPreFinHyp_of` / `kernel_entryJ4`
  with `KDispHypsR` and `KPreFinRestHypC`.
-/
import Fl4Proofs.P3.XTopJointIrqZR
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **`DispPost` with `JAtZR` at an ok outcome** (module docstring). -/
def DispPostR (AR : A → Fl4Spec.Cr3 → Prop) (Q : Fl4Spec.State Unit → S × A → Prop) (m : Fl4Spec.PMonad Unit Unit)
    (σ : Fl4Spec.State Unit) (r : S × A) : Prop :=
  ∃ y ∈ (m.run σ).1,
    (y.1 = .ok () ∧ RelTopM (L := L) r.1 y.2 ∧ ∃ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64)
      (Lst : U64 → List U64) (D : Set U64), JAtZR (L := L) arI AR Z H Cs Ac Lst D r.1 r.2 y.2 ∧ VxE Z) ∨
    (y.1 = .error () ∧ Q y.2 r)

variable {arI}

theorem JAt.toRE {AR : A → Fl4Spec.Cr3 → Prop} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (h : JAt (L := L) arI AR s a σ) : ∃ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64)
      (Lst : U64 → List U64) (D : Set U64), JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ ∧ VxE Z :=
  let ⟨Z, H, Cs, Ac, Lst, D, J, _⟩ := h; ⟨Z, H, Cs, Ac, Lst, D, J.toR, inferInstance⟩

theorem DispPost.toR {AR : A → Fl4Spec.Cr3 → Prop} {Q : Fl4Spec.State Unit → S × A → Prop}
    {m : Fl4Spec.PMonad Unit Unit} {σ : Fl4Spec.State Unit} {r : S × A}
    (h : DispPost (L := L) arI AR Q m σ r) : DispPostR (L := L) arI AR Q m σ r :=
  let ⟨y, hy, hh⟩ := h; ⟨y, hy, hh.imp (fun ⟨h1, h2, h3⟩ => ⟨h1, h2, h3.toRE⟩) id⟩

variable {AR : A → Fl4Spec.Cr3 → Prop}

end

end

end Fl4Proofs.P3
