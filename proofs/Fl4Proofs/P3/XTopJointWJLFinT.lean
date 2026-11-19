/-
P3 (DESIGN.md §9), CSpace: **the reply's, the thread's and the IRQ
handler's finalisations at `WJL`** (XTopJointWJLFin's `JFinAtL`, the kinds
left there).

* `jFinAtL_reply`: XTopJointDelR's `jFinAt_reply` at `WJL`
  (`JAtZ.finReplyJD` from the dead set grown by the TCB zombies' TCBs, its
  `reply_remove` case by `JAtZ.replyRemoveJD` at that set; P1's
  `fin_reply.dbgKeep`, its caller-core premise by `JAtZ.rmCore`).
-/
import Fl4Proofs.P3.XTopJointWJLFin
import Fl4Proofs.P3.XTopJointFinThreadU
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {AR : A → Fl4Spec.Cr3 → Prop} {th : TypedHeap}

set_option maxHeartbeats 4000000 in
/-- **A final reply cap's finalisation at `WJL`** (module docstring). -/
theorem jFinAtL_reply [Fl4Proofs.P1.PlainStore st] (hT : P0.ArchTotal arI) : JFinAtL (L := L) arI AR th RpK := by
  intro Z H Cs kb hth s a σ G sl c hDS hW hA hc hk ⟨p, g, hce⟩ hfin
  subst hce hth
  obtain ⟨⟨V, Ac, Lst, D, J, hkb, hns, hsg, hp0⟩, hL, hDW, hN⟩ := hW
  have J0 := J.addDeadSet (E := ZTcb (L := L) Z.th s) hL.ztcb
  have hcv := capV_of_capAt hc
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hHp : H p = some .reply := (hJ.typed _ hA.isSlot).2.2 p g hcv
  have hpR : p ∈ (Z.mv G V).R := J.hset.2.2 p hHp
  have hrH : p ∈ P1.Heap.replies H := J.zH.2.2.1 p hpR
  have hpp := jFinPPHyp arI (Z.mv G V) H Cs Ac Lst D s a σ rfl J sl _ hA hc hk
  have hdc : ∀ t ∈ P1.Heap.tcbs H, headBit (L.mem s (rNextA p)) = true →
      L.mem s (P1.affA t) = L.mem s (P1.scCoreA (L.mem s (rNextA p) &&& ~~~1#u64)) := fun t ht =>
    J.rmCore hpR (by rw [J.tcbs_eq.1]; exact ht)
  rw [decide_eq_true hfin] at hpp ⊢
  refine WP.spec_mono (WP.spec_and (WP.spec_and
    (J0.finReplyJD hT (fun r t x hr ht hk hst => WP.spec_mono (J0.replyRemoveJD hT hr ht hk hst)
      fun res ⟨h1, σ', V', Ac', Lst', D', e, J', hSS, hks, hD, _⟩ => by
        subst hD; exact ⟨h1, σ', V', Ac', Lst', e, J', hSS, hks⟩) hpR)
    (P1.fin_cap_reply.dead (ar := arI) hT s a p g false J.blk hHp))
    (P1.fin_reply.dbgKeep (ar := arI) hT s a p g true false J.blk hrH hdc)) ?_
  rintro ⟨⟨rem, cl⟩, s1, a1⟩ ⟨⟨⟨e1, e2, σ1, V1, Ac1, Lst1, hmem1, J1, hSS1, hks1⟩, d1⟩, hK⟩
  simp only at e1 e2 hmem1 J1 hSS1 hks1 d1 hK
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj e1
  subst e2
  have hdp : DeadP (L := L) H s1 p :=
    ⟨fun h => (by rw [hHp] at h; cases h), fun h => (by rw [hHp] at h; cases h),
      fun h => (by rw [hHp] at h; cases h), fun _ => d1, fun z h => (by rw [hHp] at h; cases h)⟩
  have hcv1 : capV (L.mem s1) (cslotAddr sl) = .Reply p g := by
    rw [hSS1.capV hA.isSlot, hcv]
  have hDS1 : DState (L := L) Z.th s1 σ1 G := ⟨J1.xtop.rel.2.1, J1.del, J1.xtop.rel.2.2.1⟩
  obtain ⟨hL1, hDW1, hN1⟩ := wjl_keep arI J hDS hL hDW hN J1 (fun p hp => Or.inr hp) hSS1 hDS1 hK
  have hn : ∀ q, ¬ RefsObj q (capV (L.mem s1) (cslotAddr sl)) := fun q h => by rw [hcv1] at h; exact h
  exact ⟨rfl, trivial, trivial, σ1, G, hmem1, hDS1, hcv1,
    fun y hy _ => Or.inl (hSS1.capV hy), (MdbStep.refl hDS.1.2.2.1).same_right hDS.1.2.2.1 hSS1,
    ⟨⟨V1, Ac1, Lst1, _, J1, hks1.trans hkb, ak_finaliseCap_ns hmem1 hns, SpecGlob.fin hmem1 hsg, hpp _ _ hmem1 hp0⟩,
      hL1, hDW1, hN1⟩,
    fun _ => rdLO_noRef arI J1 hL1 (JAtZ.reply_ready arI J1 hA.isSlot hcv1 hdp) hn,
    fun _ _ _ _ q h => by rw [hcv1] at h; cases h⟩

end

end

end Fl4Proofs.P3
