/-
P3 (DESIGN.md §9), CSpace: **the finalisations at `WJL`**, toward
`FinObjHypWRcZ` at `WJL` (`RdLO`, `RzJ`; XTopJointWJL, XTopJointWJLRd).

* `JFinAtL Kd`: a final cap's finalisation of a kind `Kd` at `WJL`, the
  loop's post (`FinObjHypWRcZ`'s) at `WJL`, `RdLO`, `RzJ`.
* `wjl_keep`: a finalisation keeping every slot, the MDB ghost, the debug
  words, and landing at a `JAtZ` whose dead set holds the TCB zombies' TCBs
  before, keeps `LiveJ` (`LiveJ.of_sameZ`), `DbgWF` (`JAtZ.dbgWF_keep`) and
  `NullOrig` (`orig_eq_of_slots`, `NullOrig.of_same`).
* `rdLO_noRef`: `RdLO` at a slot whose cap names no container, from `RdJ`
  and `LiveJ` (`JAtZ.readyLive_noRef`, `LiveJ.liveOther_noRef`).
* `jFinAtL_ep`: XTopJointDelR's `jFinAt_ep` at `WJL` (`JAtZ.finEpJ` from the
  dead set grown by the TCB zombies' TCBs, P1's `fin_endpoint.dbgKeep`).
-/
import Fl4Proofs.P3.XTopJointWJLPP
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {AR : A → Fl4Spec.Cr3 → Prop} {th : TypedHeap}

/-- **A final cap's finalisation of a kind `Kd` at `WJL`** (module docstring). -/
def JFinAtL (AR : A → Fl4Spec.Cr3 → Prop) (th : TypedHeap) (Kd : capability.Cap → Prop) : Prop :=
  ∀ (Z : XSets) (H : P1.Heap) (Cs : Set U64) (kb : U64), Z.th = th →
  ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (sl : Fl4Spec.CslotPtr) (c : capability.Cap),
    DState (L := L) th s σ G → WJL (L := L) arI AR Z H Cs kb s a σ G → AbsSlot th sl →
    capAt (L.mem s) (cslotAddr sl) = ok c → FinObjKind c → Kd c → Fl4Spec.isFinalCap' (absCap c) σ →
    objects.finalise_cap st arI s a c (decide (Fl4Spec.isFinalCap' (absCap c) σ)) false ⦃ r =>
      r.1.1 = finRem c (decide (Fl4Spec.isFinalCap' (absCap c) σ)) ∧ CleanCap r.1.2 ∧ CapWf r.1.2 ∧
      ∃ σ' G', ((absCap r.1.1, absCap r.1.2), σ') ∈
          (Fl4Spec.finaliseCap (Z := Unit) (absCap c) (decide (Fl4Spec.isFinalCap' (absCap c) σ)) σ).1 ∧
        DState (L := L) th r.2.1 σ' G' ∧ capV (L.mem r.2.1) (cslotAddr sl) = c ∧
        (∀ y, IsSlot th y → y ≠ cslotAddr sl → capV (L.mem r.2.1) y = capV (L.mem s) y ∨
          (capV (L.mem r.2.1) y = .Null ∧ isZb (capV (L.mem s) y) = false)) ∧
        MdbStep (L.mem s) G (L.mem r.2.1) G' ∧ WJL (L := L) arI AR Z H Cs kb r.2.1 r.2.2 σ' G' ∧
        (RmOK r.1.1 (cslotAddr sl) → RdLO (L := L) (A := A) th H r.2.1 r.2.2 σ' G' (cslotAddr sl)) ∧
        RzJ (L := L) (A := A) H r.2.1 r.2.2 σ' G' (cslotAddr sl) ⦄

/-- **A slot-keeping finalisation keeps `LiveJ`, `DbgWF` and `NullOrig`**
(module docstring). -/
theorem wjl_keep {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64}
    {s : S} {a : A} {σ : Fl4Spec.State Unit} {G : MdbGhost} {V : XVs}
    (J : JAtZ (L := L) arI AR (Z.mv G V) H Cs Ac Lst D s a σ) (hDS : DState (L := L) Z.th s σ G)
    (hL : LiveJ (L := L) Z.th H G s σ) (hDW : DbgWF (P1.Heap.tcbs H) Cs (L.mem s) (dbgHd (L := L) s))
    (hN : NullOrig Z.th (L.mem s) σ)
    {V1 : XVs} {Ac1 : Set U64} {Lst1 : U64 → List U64} {D1 : Set U64} {s1 : S} {a1 : A} {σ1 : Fl4Spec.State Unit}
    (J1 : JAtZ (L := L) arI AR (Z.mv G V1) H Cs Ac1 Lst1 D1 s1 a1 σ1) (hE : ZTcb (L := L) Z.th s ⊆ D1)
    (hSS : SlotsSame Z.th (L.mem s) (L.mem s1)) (hDS1 : DState (L := L) Z.th s1 σ1 G)
    (hK : P1.DbgKeep st (P1.Heap.tcbs H) Cs s s1) :
    LiveJ (L := L) Z.th H G s1 σ1 ∧ DbgWF (P1.Heap.tcbs H) Cs (L.mem s1) (dbgHd (L := L) s1) ∧
      NullOrig Z.th (L.mem s1) σ1 := by
  have horig : σ1.isOriginalCap = σ.isOriginalCap :=
    orig_eq_of_slots hDS.1.2.2.2.1 hDS1.1.2.2.2.1 J.kern.orig J1.kern.orig hSS
  have hmem : ∀ y ∈ G.chains.flatten, IsSlot Z.th y := fun y hy => ((hDS.1.2.2.1.members y).1 hy).1
  have hTz : P1.DbgTz st (P1.Heap.tcbs H) Cs s :=
    ⟨J.blk.2.2.1.2.2.tm.dn, J.blk.2.2.1.2.2.tm.dp, J.blk.2.2.1.2.2.tm.dh⟩
  obtain ⟨lst, hDW⟩ := hDW
  exact ⟨hL.of_sameZ hSS hmem horig hK J.kern.cs0 hTz fun p hp => J1.jcov.dead p (hE hp),
    ⟨lst, J.dbgWF_keep J1 rfl rfl hDW hK⟩, hN.of_same (fun y hy => hSS.capV hy) horig⟩

/-- **`RdLO` at a slot whose cap names no container** (module docstring). -/
theorem rdLO_noRef {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64}
    {s : S} {a : A} {σ : Fl4Spec.State Unit} {G : MdbGhost} {V : XVs}
    (J : JAtZ (L := L) arI AR (Z.mv G V) H Cs Ac Lst D s a σ) (hL : LiveJ (L := L) Z.th H G s σ) {x : U64}
    (hRd : EmptyReady (L := L) H G s x) (hn : ∀ q, ¬ RefsObj q (capV (L.mem s) x)) :
    RdLO (L := L) (A := A) Z.th H s a σ G x :=
  ⟨⟨hRd, J.readyLive_noRef hL hn⟩, hL.liveOther_noRef hn⟩

set_option maxHeartbeats 4000000 in
/-- **A final endpoint cap's finalisation at `WJL`** (module docstring). -/
theorem jFinAtL_ep : JFinAtL (L := L) arI AR th EpK := by
  intro Z H Cs kb hth s a σ G sl c hDS hW hA hc hk ⟨e, b, x1, x2, x3, x4, hce⟩ hfin
  subst hce hth
  obtain ⟨⟨V, Ac, Lst, D, J, hkb, hns, hsg, hp0⟩, hL, hDW, hN⟩ := hW
  have J0 := J.addDeadSet (E := ZTcb (L := L) Z.th s) hL.ztcb
  have hcv := capV_of_capAt hc
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hHe : H e = some .ep := (hJ.typed _ hA.isSlot).1 e b x1 x2 x3 x4 hcv
  have heE : e ∈ (Z.mv G V).E := J.hset.1 e hHe
  have hpp := jFinPPHyp arI (Z.mv G V) H Cs Ac Lst D s a σ rfl J sl _ hA hc hk
  rw [decide_eq_true hfin] at hpp ⊢
  refine WP.spec_mono (WP.spec_and (WP.spec_and (J0.finEpJ heE)
    (P1.fin_cap_ep.dead (ar := arI) s a e b x1 x2 x3 x4 false J.blk hHe))
    (P1.fin_endpoint.dbgKeep (ar := arI) s a e b x1 x2 x3 x4 true false J.blk hHe)) ?_
  rintro ⟨⟨rem, cl⟩, s1, a1⟩ ⟨⟨⟨e1, e2, σ1, V1, hmem1, J1, -, hSS1, hks1⟩, d1⟩, hK⟩
  simp only at e1 e2 hmem1 J1 hSS1 hks1 d1 hK
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj e1
  subst e2
  have hdp : DeadP (L := L) H s1 e :=
    ⟨fun h => (by rw [hHe] at h; cases h), fun _ => d1, fun h => (by rw [hHe] at h; cases h),
      fun h => (by rw [hHe] at h; cases h), fun z h => (by rw [hHe] at h; cases h)⟩
  have hcv1 : capV (L.mem s1) (cslotAddr sl) = .Endpoint e b x1 x2 x3 x4 := by
    rw [hSS1.capV hA.isSlot, hcv]
  have hDS1 : DState (L := L) Z.th s1 σ1 G := ⟨J1.xtop.rel.2.1, J1.del, J1.xtop.rel.2.2.1⟩
  obtain ⟨hL1, hDW1, hN1⟩ := wjl_keep arI J hDS hL hDW hN J1 (fun p hp => Or.inr hp) hSS1 hDS1 hK
  have hn : ∀ q, ¬ RefsObj q (capV (L.mem s1) (cslotAddr sl)) := fun q h => by rw [hcv1] at h; exact h
  exact ⟨rfl, trivial, trivial, σ1, G, hmem1, hDS1, hcv1,
    fun y hy _ => Or.inl (hSS1.capV hy), (MdbStep.refl hDS.1.2.2.1).same_right hDS.1.2.2.1 hSS1,
    ⟨⟨V1, Ac, Lst, _, J1, hks1.trans hkb, ak_finaliseCap_ns hmem1 hns, SpecGlob.fin hmem1 hsg, hpp _ _ hmem1 hp0⟩,
      hL1, hDW1, hN1⟩,
    fun _ => rdLO_noRef arI J1 hL1 (JAtZ.ep_ready arI J1 hA.isSlot hcv1 hdp) hn,
    fun q h => by rw [hcv1] at h; cases h⟩

end

end

end Fl4Proofs.P3
