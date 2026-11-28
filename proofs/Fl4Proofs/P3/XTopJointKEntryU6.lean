/-
P3 (issue #16, g7a): **`kernel_entry_reachU6`** = g6a's `kernel_entry_reachU4`
without the finish bundle's `hd` (INV-PLAN §1.U3L D1): `σ.domainTime ≠ 0 ∨
NdOK s σ` at every pre-finish outcome is now a theorem.

* DomDecode's `DomRel` (carried in `RelTopM` / `XTopAt`) gained the
  `DOM_SCHED_IDX` word 0 (g7a): FL4 writes it only in `domain_set_start` (0)
  and `next_domain` (back to the start index 0, entry 1 being the end marker;
  SchedIdx's `sched.schedule.idx`).
* `JAtZR.hdOK`: at a `JAtZR` state whose spec state is `DomListOK`, `NdOK`:
  `DomRel` from `XTopAt`, the index word 0 and `domain_index = 0`
  (`DomListOK.idx0` with `DomRel`'s two entries).
* `DomListOK` at every outcome where the bundle is asked: SpecInvDom's `DP`
  family (`dp_specFront`: the FaultIP write and the event's handling with the
  preemption path; `dpe_handleE`/`dpe_fl4HandleEvent` for `KFinEv`), from
  `SInvX`'s `SInvA.dom` at the entry.
* `KFinAtR31N` (`KFinAtR31` without `hd`), `KFinEvN`, `.toR31`, `.toEv`.
-/
import Fl4Proofs.P3.XTopJointKEntryU4
import Fl4Proofs.P3.SchedIdx
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.SInvR.G5
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4

noncomputable section

/-- `specFront` keeps `DomListOK` (SpecInvDom's `DP` family). -/
theorem dp_specFront (hnd : Fl4Spec.numDomains = 1) (c : Fl4Spec.Syscall) {σ : Fl4Spec.State Unit}
    (hV : DomListOK σ) : ∀ x ∈ (specFront c σ).1, DomListOK x.2 := fun x hx =>
  SInvDom.dp_bind (SInvDom.dp_of_dl (SInvDom.dl_fl4SyscallFaultIP σ.curThread)) (fun _ =>
    SInvDom.dpe_handleE (SInvDom.dpe_fl4HandleEvent hnd true _) fun _ => SInvDom.dpe_of_dle (by dl_auto)) σ x hV hx

/-- The event handling keeps `DomListOK`. -/
theorem dp_event (hnd : Fl4Spec.numDomains = 1) (ev : Fl4Spec.Event) {σ : Fl4Spec.State Unit}
    (hV : DomListOK σ) : ∀ x ∈ ((Fl4Spec.NonDetE.handleE (Fl4Spec.fl4HandleEvent (Z := Unit) true ev)
      (fun _ => Fl4Spec.withoutPreemption Fl4Spec.preemptionPath)).run σ).1, DomListOK x.2 := fun x hx =>
  SInvDom.dpe_handleE (SInvDom.dpe_fl4HandleEvent hnd true ev) (fun _ => SInvDom.dpe_of_dle (by dl_auto)) σ x hV hx

/-- `SInvX`'s `DomListOK`. -/
theorem sinvX_dom {σ : Fl4Spec.State Unit} (hX : SInvX σ) : DomListOK σ := hX.1.1.1.1.1.1.1.1.dom

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

variable {arI}

/-- **`hd` at a `JAtZR` state with `DomListOK`** (module docstring). -/
theorem _root_.Fl4Proofs.P3.JAtZR.hdOK {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ) (hV : DomListOK σ) :
    σ.domainTime ≠ 0 ∨ NdOK (L := L) s σ := by
  have hD : DomRel (L.mem s) (L.ksb s) σ := J.xtop.rel.2.2.2.1
  refine Or.inr ⟨hD, hV, ?_⟩
  rw [hD.2.2.2, hV.idx0 hD.1]; rfl

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)

end

end

end Fl4Proofs.P3.SInvR.G5
