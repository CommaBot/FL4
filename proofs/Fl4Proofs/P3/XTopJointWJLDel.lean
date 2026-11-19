/-
P3 (DESIGN.md §9), CSpace: **the deletion at `WJL`** (XTopJointWJL), the
named steps assembled.

* `finJLZ`: `FinObjHypWRcZ` at `WJL`, `RdLO`, `RzJ` (as XTopJointDelR's
  `finJ`/`finJL`, each kind by its `JFinAtL` lemma: XTopJointWJLFin,
  XTopJointWJLFinT; a non-final cap by `jFin_nonfinalLO`; the frame and IO
  port caps by `jFinAtL_frio`, their remainder null).
* `delHypsJL`: `DelHypsWRZ` at `WJL`/`WJP` from `finJLZ`, `rdTrivJLO`,
  `jPreemptHypL`, `jPostDelHypL`, `jZombieHypL`, `jSwapHypL`, `emptyHypJL`.
* `JDelHypL`: XTopJointDelR's `JDelHyp` at `WJL` (the deletion from a state
  with `LiveJ`, `DbgWF` and `NullOrig`, which it keeps), proved
  (`JDelParts.jDelHypL`, DelFull's `delHyp_fullWRZ`) from `JDelParts`'
  platform and scope facts only: no `LiveJHyp`.
-/
import Fl4Proofs.P3.XTopJointWJLFinT
import Fl4Proofs.P3.XTopJointWJLSwap
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {AR : A → Fl4Spec.Cr3 → Prop} {th : TypedHeap}

set_option maxHeartbeats 4000000 in
/-- **The object caps' finalisation at `WJL`** (module docstring). -/
theorem finJLZ [Fl4Proofs.P1.PlainStore st] (hT : P0.ArchTotal arI) (hAR : ArchRefines arI AR)
    (hK : ARKeep arI AR) (hV : JVtHyps (L := L) arI AR th) (hF : JThreadFinHypsU (L := L) arI AR th)
    (Z : XSets) (H : P1.Heap) (Cs : Set U64) (kb : U64) (hth : Z.th = th) :
    FinObjHypWRcZ (L := L) arI (WJL (L := L) arI AR Z H Cs kb) (RdLO (L := L) (A := A) th H)
      (RzJ (L := L) (A := A) H) th := by
  intro s a σ G sl c hDS hW hA hc hk _
  by_cases hfi : FrIoK c
  · refine WP.spec_mono (jFinAtL_frio arI hAR hK (jVsApartHyp arI) hV Z H Cs kb hth s a σ G sl c hDS hW hA hc hk
      hfi) ?_
    rintro r ⟨h1, h2, h3, σ', G', h4, h5, h6, h7, h8, h9, h10⟩
    refine ⟨h1, h2, h3, σ', G', h4, h5, h6, h7, h8, h9, fun _ => h10, fun p zt n e => ?_⟩
    obtain ⟨e1, -⟩ := finRem_zombie (h1.symm.trans e)
    subst e1
    exfalso
    rcases hfi with h | ⟨f, l, o, e⟩
    · simp [isFrame] at h
    · cases e
  by_cases hfin : Fl4Spec.isFinalCap' (absCap c) σ
  · by_cases hn : NtfnK c
    · exact jFinAtL_ntfn arI Z H Cs kb hth s a σ G sl c hDS hW hA hc hk hn hfin
    by_cases hq : IrqK c
    · exact jFinAtL_irq arI Z H Cs kb hth s a σ G sl c hDS hW hA hc hk hq hfin
    by_cases he : EpK c
    · exact jFinAtL_ep arI Z H Cs kb hth s a σ G sl c hDS hW hA hc hk he hfin
    by_cases hr : RpK c
    · exact jFinAtL_reply arI hT Z H Cs kb hth s a σ G sl c hDS hW hA hc hk hr hfin
    by_cases hvs : VsK c
    · exact jFinAtL_vs arI hAR (jVsApartHyp arI) Z H Cs kb hth s a σ G sl c hDS hW hA hc hk hvs hfin
    by_cases hsc : ScK c
    · exact jFinAtL_sc arI hT hF.ticks Z H Cs kb hth s a σ G sl c hDS hW hA hc hk hsc hfin
    by_cases ht : TcbK c
    · exact jFinAtL_thread arI hT hK hF Z H Cs kb hth s a σ G sl c hDS hW hA hc hk ht hfin
    by_cases hvt : EptK c ∨ VcpuK c
    · exact jFinAtL_vt arI hAR hK hV Z H Cs kb hth s a σ G sl c hDS hW hA hc hk hvt hfin
    by_cases hrt : EptRootK c
    · exact jFinAtL_eptRoot arI hAR (jVsApartHyp arI) Z H Cs kb hth s a σ G sl c hDS hW hA hc hk hrt hfin
    · exact (finObjKind_covered hk hn hfi hq he hr hvs hsc ht hvt hrt).elim
  · exact jFin_nonfinalLO arI Z H Cs kb hth s a σ G sl c hDS hW hA hc hk hfi hfin

/-- **The deletion loop's named steps at `WJL`** (module docstring). -/
theorem delHypsJL [Fl4Proofs.P1.PlainStore st] (hT : P0.ArchTotal arI) (hAR : ArchRefines arI AR)
    (hK : ARKeep arI AR) (hV : JVtHyps (L := L) arI AR th) (hF : JThreadFinHypsU (L := L) arI AR th)
    (hnd : Fl4Spec.numDomains = 1) (hPP : PPPlat arI AR) (hAM : ARMask arI AR)
    (Z : XSets) (H : P1.Heap) (Cs : Set U64) (kb : U64) (hth : Z.th = th) :
    DelHypsWRZ (L := L) arI (WJL (L := L) arI AR Z H Cs kb) (WJP (L := L) arI AR Z H Cs kb)
      (RdLO (L := L) (A := A) th H) (RzJ (L := L) (A := A) H) th := by
  have hmask : ∀ (a : A) (irq : U64) (b : Bool), ∃ a', arI.mask_irq a irq b = ok a' := fun a i m => by
    obtain ⟨a', h, -⟩ := spec_exists (hT.mask_irq a i m); exact ⟨a', h⟩
  have hfree : ∀ (a : A) (irq : U64), ∃ a', arI.irq_free a irq = ok a' := fun a i => by
    obtain ⟨a', h, -⟩ := spec_exists (hT.irq_free a i); exact ⟨a', h⟩
  exact ⟨finJLZ arI hT hAR hK hV hF Z H Cs kb hth, rdTrivJLO arI Z H Cs kb hth,
    jPreemptHypL arI hK hT hnd hPP Z H Cs kb hth, jPostDelHypL arI hAM hmask hfree Z H Cs kb hth,
    jZombieHypL arI Z H Cs kb hth, jSwapHypL arI Z H Cs kb hth, emptyHypJL arI Z H Cs kb hth⟩

/-- **The deletion at `WJL`** (module docstring): `JDelHyp` from a state with
`WJL`, keeping it. -/
def JDelHypL (AR : A → Fl4Spec.Cr3 → Prop) (th : TypedHeap) : Prop :=
  ∀ (Z : XSets) (H : P1.Heap) (Cs : Set U64) (kb : U64) (K : Nat), Z.th = th →
    (∀ p r, th p = some (.cnode r) → 2 ^ r ≤ K) → 6 ≤ K →
    DelHypW (L := L) arI psiD th
      (fun s a σ G => DelE (L := L) Z.th K s σ ∧ WJL (L := L) arI AR Z H Cs kb s a σ G)
      (EJP (L := L) arI AR Z H Cs kb K)

/-- **`JDelHypL` from `JDelParts`' platform and scope facts** (module
docstring). -/
theorem JDelParts.jDelHypL [Fl4Proofs.P1.PlainStore st] (h : JDelParts (L := L) arI AR th)
    (hT : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hPP : PPPlat arI AR) (hAM : ARMask arI AR) :
    JDelHypL (L := L) arI AR th := by
  intro Z H Cs kb K hth hK hK6 s a σ G c hCR hE hA hxm
  obtain ⟨⟨V, Ac, Lst, D, J, -⟩, -⟩ := hE.2
  have hP : Placed th := hth ▸ J.xtop.rel.1
  have hH := delHypsJL arI hT h.archRef h.arKeep h.vt h.thr hnd hPP hAM Z H Cs kb hth
  subst hth
  exact delHyp_fullWRZ arI _ _ _ _ Z.th hP (finalHyp_full Z.th hP) hH K hK hK6 s a σ G c hCR hE hA hxm

end

end

end Fl4Proofs.P3
