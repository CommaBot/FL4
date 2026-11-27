/-
P3 (line mmuAD, gen 36): **`possible_switch_to` of a thread that may be the current thread, at `JAtZB` and
`JAtZV3`** (toward gen 35's [J] `SigVmTailJ3`: in `send_signal`'s `RunningVM` branch the reported thread may be
the current thread).

* `Sched.mkn_possibleSwitchToC`: P3/ScMidKeep's `mkn_possibleSwitchTo` without its hypothesis (the thread neither
  idle nor current): the proof never reads it (verbatim copy). `possibleSwitchTo` of the current thread changes
  only the ready queues and the scheduler action (`switchThread cur` when a resumption was pending), which is
  `MidKn`.
* **`JAtZB.switchJc`**: P3/JAtZBSched's `JAtZB.switchJ` without `hti`/`htc` (proof verbatim, `mkn_possibleSwitchToC`
  in place of `mkn_possibleSwitchTo ⟨hti, htc⟩`, its only use of them).
* **`JAtZV3.switchJc`**: P3/JAtZV3's `JAtZV3.switchJ` without `hti`/`htc` (proof verbatim, over `JAtZB.switchJc`).

No named premise. No existing statement changed.
-/
import Fl4Proofs.P3.JAtZV3
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open Fl4Spec Classical

noncomputable section

/-- **`possible_switch_to` of any thread: `MidKn`** (module docstring; `mkn_possibleSwitchTo` verbatim). -/
theorem mkn_possibleSwitchToC {t : ObjRef} {σ : State Unit} :
    ∀ x ∈ (possibleSwitchTo (Z := Unit) t σ).1, MidKn σ x.2 := by
  intro x hx
  unfold possibleSwitchTo getTcbObjRef setSchedulerAction at hx
  obtain ⟨y1, hy1, hx⟩ := hx
  rw [RdO.ofRdN (rdn_threadGet _ _) σ y1 hy1] at hx
  obtain ⟨y2, hy2, hx⟩ := hx
  rw [rdo_gets _ σ y2 hy2] at hx
  unfold NonDet.when at hx
  dsimp only at hx
  split at hx
  · obtain ⟨y3, hy3, hx⟩ := hx
    rw [rdo_gets _ σ y3 hy3] at hx
    obtain ⟨y4, hy4, hx⟩ := hx
    rw [RdO.ofRdN (rdn_threadGet _ _) σ y4 hy4] at hx
    obtain ⟨y5, hy5, hx⟩ := hx
    obtain ⟨e5, hv5⟩ := rdn_gets (fun s : State Unit => s.schedulerAction) σ y5 hy5
    rw [e5] at hx
    dsimp only at hx
    split at hx
    · exact (mka_tcbSchedAction (P := fun _ => True) _ _ σ trivial x hx).toN
    · split at hx
      · exact ((mka_bind midkStable_true (mka_rescheduleRequired midkStable_true) fun _ => mka_tcbSchedAction _ _)
          σ trivial x hx).toN
      · rename_i hres
        rw [Set.mem_singleton_iff.1 hx]
        have hr : σ.schedulerAction = .resumeCurThread := by rw [← hv5]; simpa using hres
        refine ⟨rfl, rfl, rfl, rfl, rfl, Or.inl rfl, fun h => (by rw [hr] at h; cases h), MidT.refl _ _, MidT.refl _ _,
          fun y _ h => ⟨y, h, rfl, id, fun _ => rfl⟩, fun _ h => Or.inl h⟩
  · rw [Set.mem_singleton_iff.1 hx]; exact (MidK.refl σ).toN

end

end Fl4Proofs.P3.Sched

namespace Fl4Proofs.P3
open fl4_core

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {V X : Set U64}

open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

set_option maxHeartbeats 16000000 in
/-- **`possible_switch_to` at `JAtZB` of a schedulable thread, possibly the current or idle one** (module
docstring). -/
theorem JAtZB.switchJc (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T)
    (hs : Fl4Spec.schedulable t.bv σ = true) :
    sched.possible_switch_to st s t ⦃ s' => ∃ σ', Fl4Spec.possibleSwitchTo (Z := Unit) t.bv σ = ({((), σ')}, False) ∧
      ∃ Lst' : U64 → List U64, JAtZB (L := L) arI AR Z H Cs Ac Lst' D s' a σ' ⦄ := by
  have hX := J.xtop
  have hS := hX.fin.1.1.1
  have hR := hX.fin.1.1.2.2.1
  have htH : t ∈ P1.Heap.tcbs H := J.zH.1 t ht
  have hwd := (schedulable_eq hR hS ht).trans hs
  obtain ⟨hrw, -, hmx, -⟩ := of_decide_eq_true hwd
  have hrun : P1.Runnable (L.mem s (P1.stA t)) := by rw [stA_tStA]; exact hrw
  refine WP.spec_mono (WP.spec_and (WP.spec_and (possible_switch_to_refines s σ hR hS J.inv.actReady t ht)
    (possible_switch_to_sfoot hR hS J.inv.actReady ht))
    (P1.sched.possible_switch_to.blk (Es := P1.EH H) s t J.blk htH hrun (fun _ e => by
      rw [e] at hmx; simp at hmx))) ?_
  rintro s' ⟨⟨⟨σ', he, hke, hfe, hS'⟩, hw⟩, hblk, hfoot⟩
  have mem : ((), σ') ∈ (Fl4Spec.possibleSwitchTo (Z := Unit) t.bv σ).1 := by rw [he]; exact Set.mem_singleton _
  have hR' : NtfnStateRel Z.N Z.T (L.mem s') σ' := hR.frame hS.placed hfe (KView.of_kheap hke)
  have hwK : P1.WritesIn st s s' (KFoot st Z.T Z.N Z.C Z.c s σ) := WritesIn.kfoot_of_sfoot hw
  have hwT := WritesIn.tfoot_of_kfoot hwK
  have hK : ScTKw (fun _ => False) σ σ' := nkt_possibleSwitchTo t.bv σ _ mem
  have hX' : XTopAt (L := L) AR Z s' a σ' := xtop_sc_step hX J.ip J.nk hwT (hK.ofFalse (P := fun p => p = t.bv)) hS' hR' id
  have hq := possibleSwitchTo_qchange J.inv hs he
  have hc := possibleSwitchTo_calm J.inv hs he
  have hI' : Inv σ' := J.inv.qchange hq
  have hL : LK (fun _ => False) σ σ' := lkm_possibleSwitchTo t.bv σ _ mem
  have hN' : NSC Z.N Z.C σ' := nsc_of_lk J.nsc hK hL
  have hsok : SOK (true, true) σ σ' := pres_possibleSwitchTo (f := (true, true)) t.bv σ _ mem
  obtain ⟨-, hY', hM', ⟨Lst', hCR', hRF'⟩, hRP', -⟩ :=
    ScAll.of_k hS J.rp J.yld J.mcp J.call J.rfree ⟨⟨hS', hR', hN', hI'⟩, hwK, hsok⟩
  have hF : FK σ σ' := ⟨hc.2.2.1, hc.2.2.2.2.2.1, hK.isc⟩
  have hMK := mkn_possibleSwitchToC _ mem
  have hAI : ActIdle σ' := J.act.possibleSwitchTo J.inv hs he
  have hBK : BK σ σ' := bkm_of (nkt_possibleSwitchTo t.bv) (MaxK.mk_possibleSwitchTo' t.bv) σ _ mem
  have hbsa : BlockedScActive σ' := J.bsa.bk hBK hsok
  have hcur : σ'.schedulerAction = .chooseNewThread ∨ CurInv σ' := by
    rcases J.cur with e | hC
    · exact Or.inl (possibleSwitchTo_cn J.inv hs he e)
    · exact (hMK.mid3 hC J.off J.inv ⟨L.curW s, J.thT _ J.kern.curT, J.kern.cur.symm⟩).1
  have hown : CurOwnW Z.T Z.C σ' := J.own.sub hc (fun u hu => by rw [hq.2.1] at hu; exact hu)
  have hoff : OffOK σ' := by
    intro h0 y n hy ha
    rw [hc.2.2.2.2.1] at h0 ⊢
    rw [hc.2.2.2.1]
    rw [hc.1, hc.2.2.1] at hy
    rw [hc.2.2.1, hc.2.2.2.2.2.2.2.2] at ha
    exact J.off h0 y n hy ha
  have hcr : CurRunM σ' := by
    by_cases hr : σ'.schedulerAction = .resumeCurThread
    · have h0 : σ.schedulerAction = .resumeCurThread := by
        by_contra h
        exact possibleSwitchTo_nr J.inv hs he h hr
      right
      rcases J.curRun.resolve_left (fun h => h h0) with h | h
      · left
        intro y hy
        rw [hc.2.1, hc.1] at hy
        exact h y hy
      · right; rw [hc.2.1, hc.2.2.2.2.2.1]; exact h
    · exact Or.inl hr
  have hdead : ∀ q ∈ D, DeadP (L := L) H s' q := fun q hq =>
    J.deadP_sc_stepQ hX' hwT hK (fun _ hp => hp.elim) hL hF hAI.1 hY' ((hsok.ykeep rfl).dk q.bv) (fun h => h) (J.jcov.dead q hq)
  have hDbg := J.kw_dbg hfoot
  have hKd := J.kw_dbgKeep hfoot
  exact ⟨σ', he, Lst', J.sc_frame hwT hK hX' hCR' hRF' hY' hM' (J.sc_buf hwT hK) hRP' (J.sc_apart hwT hK)
    (J.sc_jpl hwT hK (J.idleW_keep hX'.fin.1.1.1 hF.2.1 hF.2.2).2) (J.sc_jcov hwT hdead (fun q hq hn => absurd hq hn) (J.idleW_keep hX'.fin.1.1.1 hF.2.1 hF.2.2) hKd subset_rfl)
    (J.sc_kern hwT hK hF hX' hDbg fun _ h => h) (J.sc_utc hwT hK hDbg) hN' hI' hcur hown hoff hAI hbsa hcr hblk hKd (J.idleW_keep hX'.fin.1.1.1 hF.2.1 hF.2.2).1 J.zD⟩


section
open Fl4Proofs.P1

set_option maxHeartbeats 4000000 in
/-- **`possible_switch_to` at `JAtZV3` of a schedulable thread, possibly the current or idle one** (module
docstring). -/
theorem JAtZV3.switchJc (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T)
    (hs : Fl4Spec.schedulable t.bv σ = true) :
    sched.possible_switch_to st s t ⦃ s' => ∃ σ', Fl4Spec.possibleSwitchTo (Z := Unit) t.bv σ = ({((), σ')}, False) ∧
      ∃ Lst' : U64 → List U64, JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst' D s' a σ' ⦄ := by
  have B := J.z2.zv.base
  have hS := B.xtop.fin.1.1.1
  have hR := B.xtop.fin.1.1.2.2.1
  refine WP.spec_mono (WP.spec_and (WP.spec_and (B.switchJc ht hs)
    (possible_switch_to_refines s σ hR hS B.inv.actReady t ht)) (possible_switch_to_sfoot hR hS B.inv.actReady ht)) ?_
  rintro s' ⟨⟨⟨σ1, he1, Lst', B'⟩, ⟨σ2, he2, hke, -, -⟩⟩, hw⟩
  have e12 : σ2 = σ1 := by
    rw [he1] at he2
    have h := congrArg Prod.fst he2
    simp only [Set.singleton_eq_singleton_iff, Prod.mk.injEq, true_and] at h
    exact h.symm
  subst e12
  have hwT : P1.WritesIn st s s' (TFoot st Z.T Z.N Z.C Z.c s σ) :=
    WritesIn.tfoot_of_kfoot (WritesIn.kfoot_of_sfoot hw)
  have hv : VKeep (L := L) Z.th s s' := VKeep.of_tfoot hS B.thT hwT
  have hh : ∀ b, SFoot st Z.T Z.c s b → b ≠ P1.vHeadA st s := by
    intro b hb e
    subst e
    have hvh : (P1.vHeadA st s).val = (L.ksb s).val + 80 := vHead_val B.kern.ksbFit
    rcases SFoot.range hS.placed.tcb hb with ⟨y, hy, g1, g2⟩ | ⟨g1, g2⟩
    · have d := B.kern.hks y _ (B.zH.1 y hy) (fun _ h => by cases h)
      simp only [P1.HKind.bits, Nat.reducePow] at d
      omega
    · have hnb : L.nodeBase s Z.c = (L.ksb s).val + 13568 + Z.c.val * 4288 := rfl
      omega
  exact ⟨σ2, he1, Lst', J.ofB B' hw (fun b h => tfoot_oobj hS (Or.inl (Or.inl h))) hh hv hke⟩

end

end

end

end Fl4Proofs.P3
