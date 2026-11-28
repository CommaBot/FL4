/-
P3 (DESIGN.md §9), untyped: **FL4's `reset_untyped` at `J`** (handoff utj.md
Round 12, item 3d, the reset part).

From a `JAtZ` state whose invoked CNode slot holds a childless used RAM
untyped cap `Untyped p sb fi false` (`fi ≠ 0`), FL4's `reset_untyped`
against l4v `reset_untyped_cap` exactly: the spec's `delete_objects` is
`delSt` (UtResetSpecJ), at which UtDropJ2's `JAtZ.drop` re-establishes
`JAtZ` at the dropped sets (same FL4 state); then either the small case
(`sb < 16`: FL4 clears the region, `JAtZ.zeroRg`, and writes the free index
0, `JAtZ.setFiJ`; spec `reset_smallX`) or the chunk loop
(UtResetLoopJ's `JAtZ.reset_loopJ` from offset `(fi - 1) / 2^16 * 2^16`,
spec `reset_initX`).

* `JAtZ.rgClear_drop`: the dropped sets are clear of the region (`RgClear`):
  the dropped heap by `RegionD`, the pruned VSpace sets by `FrMiss`, the kept
  IPC-buffer words by `KBOf`, the kernel-state block, nodes and ASID area by
  `UtKsApart` (`JCovD.ks`) of the source cap.
* `JAtZ.reset_untypedJ`: the composition, ending in `ResetJPost`.

Premises: those of `JAtZ.drop` (`KeptRefsP3`/`DbgTimerKept`, `ArchFitHyp`,
`VsReachMiss` [J]), `PPPlat` [P] (the preemption points), `PPR0` at the start
(as the deletion loop's `WJR`), one core (`Z.c = 0`, `JUtPath.core0` [P]).
No new named premise.
-/
import Fl4Proofs.P3.UtResetLoopJ
import Fl4Proofs.P3.UntypedResetRefine
import Fl4Proofs.P3.UtDropJ2
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

/-- **The dropped sets are clear of the region** (module docstring). -/
theorem JAtZ.rgClear_drop (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {sl : Fl4Spec.CslotPtr}
    (hsl : AbsSlot Z.th sl) {p sb fi : U64} (hcap : capAt (L.mem s) (cslotAddr sl) = ok (.Untyped p sb fi false)) :
    RgClear ((Z.keep (KOff (RgOf p sb)) (KBOf p sb)).dropV p.val (p.val + 2 ^ sb.val) (L.mem s))
      (H.drop (P1.RegionD H p.val (p.val + 2 ^ sb.val))) Cs (L.ksb s) p sb := by
  obtain ⟨-, ⟨-, -, hML, -, -⟩, -⟩ := J.xtop.rel
  have hx : cslotAddr sl ∈ Z.G.chains.flatten := (hML.members _).2 ⟨hsl.isSlot, _, hcap, by simp⟩
  obtain ⟨hks, hnd, has⟩ := J.jcov.ks (cslotAddr sl) hx p sb fi (capV_of_capAt hcap)
  refine ⟨fun r k hr => ?_, fun x hx => ?_, fun wp hw => hw.2.2, hks, fun c hc => hnd c hc, UtKsApart.asidOf has⟩
  · rw [P1.Heap.drop_eq_some] at hr
    obtain ⟨hnr, hr⟩ := hr
    unfold P1.RegionD P1.MeetsR at hnr
    rw [hr] at hnr
    simp only [Option.elim, not_not] at hnr
    omega
  · rcases hx with h | h | h | h | h
    · rcases h.2.1 with e | e <;> omega
    · rcases h.2.1 with e | e <;> omega
    · rcases h.2.1 with e | e <;> omega
    · rcases h.2.1 with e | e <;> omega
    · rcases h.2 with e | e <;> omega

end

/-! ## The spec's retype with a reset, split at the reset -/

section SpecSplit
open Fl4Spec

/-- **The spec's retype with a reset**, a done reset: the retype without one
from the reset's outcome. -/
theorem invoke_reset_ok (bitsApi : ApiObjectType → Nat → Nat) (sl : CslotPtr) (base rb : Word) (t : ApiObjectType)
    (us : Nat) (slots : List CslotPtr) (dev : Bool) {σ σr : State Unit}
    (hr : ((.ok (), σr) : Except Unit Unit × State Unit) ∈ ((resetUntypedCap (Z := Unit) sl).run σ).1)
    {y : Except Unit Unit × State Unit}
    (hy : y ∈ ((invokeUntypedWith (Z := Unit) bitsApi (.retype sl false base rb t us slots dev)).run σr).1) :
    y ∈ ((invokeUntypedWith (Z := Unit) bitsApi (.retype sl true base rb t us slots dev)).run σ).1 := by
  unfold invokeUntypedWith at hy ⊢
  simp only [NonDetE.whenE, ↓reduceIte, Bool.false_eq_true, ndE_pure_bind] at hy ⊢
  exact memE_bind hr rfl hy

/-- **The spec's retype with a reset**, a preempted reset. -/
theorem invoke_reset_err (bitsApi : ApiObjectType → Nat → Nat) (sl : CslotPtr) (base rb : Word) (t : ApiObjectType)
    (us : Nat) (slots : List CslotPtr) (dev : Bool) {σ σr : State Unit}
    (hr : ((.error (), σr) : Except Unit Unit × State Unit) ∈ ((resetUntypedCap (Z := Unit) sl).run σ).1) :
    ((.error (), σr) : Except Unit Unit × State Unit) ∈
      ((invokeUntypedWith (Z := Unit) bitsApi (.retype sl true base rb t us slots dev)).run σ).1 := by
  unfold invokeUntypedWith
  simp only [NonDetE.whenE, ↓reduceIte]
  exact memE_bind_err hr rfl

end SpecSplit

end

end Fl4Proofs.P3
