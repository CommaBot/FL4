/-
P3 (DESIGN.md §9), TCB: **`sched::restart` at `J`** (`JAtZ.restartTcbJ`,
for Resume, WriteRegisters and CopyRegisters at `JAt`).

* `restartTail_specJ`: the spec side of `restart`'s tail after `cancel_ipc`
  (`Restart`, the sporadic unblock check, the SC's resume, the switch) from
  an `Inactive` thread neither current nor idle, no switch pending, `CurInv`:
  the SC step's frame (`ScTKw` at the thread, `LK` cutting no link, `FK`,
  `SOK`, `BK`), `MidKn` (so `MidKn.mid3`) and `ActIdle` after.
* `JAtZ.undead`: a thread whose cap is in a slot leaves the dead set
  (`cover_cap` at the same state).
* `JAtZ.restartTailJ`: the tail as one SC step (`JAtZ.sc_frame`), FL4's side
  RestartTail's `restart_tail_kfoot`; the dead stay dead
  (`deadP_sc_stepQ`: the thread, set to `Restart`, is not among them).
* `JAtZ.restartTcbJ`: `sched::restart` at `J`. A running thread: nothing. A
  stopped one: first out of the dead set by its cap (`undead`), `cancel_ipc`
  by the four `JCancelAt` steps (the dead set kept), then the tail; P1's
  `BlkOK` and the node-0 debug word over the whole restart
  (`sched.restart.allK`). Premises at the start: `CurInv`, no switch
  pending, the current thread runnable (`CurRun`), the platform's
  `MIN_BUDGET` [P].
-/
import Fl4Proofs.P3.RestartTail
import Fl4Proofs.P3.ScDeadStep
import Fl4Proofs.P3.ScJointRest
import Fl4Proofs.P3.ScBsaOps
import Fl4Proofs.P3.ScJointKeep
import Fl4Proofs.P3.SpecNoSwitch
import Fl4Proofs.P3.SpecPPR
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section Spec
open Fl4Spec

/-- `NSC` across an `ScTKw` step cutting no link. -/
theorem nsc_of_lk {N C : Set U64} {P : ObjRef → Prop} {σ σ' : State Unit} (h : NSC N C σ)
    (hK : ScTKw P σ σ') (hL : LK (fun _ => False) σ σ') : NSC N C σ' := by
  intro n hn y p hy hp
  obtain ⟨ko, hko, hn1, -⟩ := hK.kind_back hy
  obtain ⟨x, rfl⟩ := hn1 ⟨y, rfl⟩
  rcases hL n.bv with h0 | hl
  · exact h0.elim
  rw [hko, hy] at hl
  have hl' : LObj (.notification x) (.notification y) := hl
  obtain ⟨y', e, hsc⟩ := hl'.2.2 x rfl
  cases e
  rcases hsc with e | e
  · exact h n hn x p hko (e ▸ hp)
  · rw [e] at hp; cases hp

set_option maxHeartbeats 4000000 in
/-- **The spec side of `restart`'s tail** (module docstring). -/
theorem restartTail_specJ {σ σb σc σd σ' : State Unit} {t : ObjRef} {x : Tcb}
    (hk : σ.kheap t = some (.tcb x)) (hin : x.tcbState = .inactive)
    (hti : t ≠ σ.idleThread) (htc : t ≠ σ.curThread) (hns : ∀ u, σ.schedulerAction ≠ .switchThread u)
    (hI : Inv σ) (hA : ActIdle σ) (hC : CurInv σ)
    (hb : setThreadState (Z := Unit) t .restart σ = ({((), σb)}, False))
    (hc : ifSporadicCurScTestRefillUnblockCheck (Z := Unit) x.tcbSchedContext σb = ({((), σc)}, False))
    (hd : NonDet.maybeM (schedContextResume (Z := Unit)) x.tcbSchedContext σc = ({((), σd)}, False))
    (he : testPossibleSwitchTo (Z := Unit) t σd = ({((), σ')}, False)) (hId : Inv σd) :
    ScTKw (fun p => p = t) σ σ' ∧ LK (fun _ => False) σ σ' ∧ FK σ σ' ∧ SOK (true, true) σ σ' ∧ BK σ σ' ∧
      MidKn σ σ' ∧ ActIdle σ' := by
  have mb : ((), σb) ∈ (setThreadState (Z := Unit) t .restart σ).1 := by rw [hb]; exact Set.mem_singleton _
  have mc : ((), σc) ∈ (ifCondRefillUnblockCheck (Z := Unit) x.tcbSchedContext (some false) (some false) σb).1 := by
    show ((), σc) ∈ (ifSporadicCurScTestRefillUnblockCheck (Z := Unit) x.tcbSchedContext σb).1
    rw [hc]; exact Set.mem_singleton _
  have md : ((), σd) ∈ (NonDet.maybeM (schedContextResume (Z := Unit)) x.tcbSchedContext σc).1 := by
    rw [hd]; exact Set.mem_singleton _
  have me : ((), σ') ∈ (testPossibleSwitchTo (Z := Unit) t σd).1 := by rw [he]; exact Set.mem_singleton _
  have hσb : σb = updK σ t (.tcb { x with tcbState := .restart }) := by
    have e := the_result (Notif.setThreadState_eq (Z := Unit) .restart hk) hb
    rw [e]; exact stsAct_eq_self (fun h => htc h.1)
  have hf0 : IpcFree x.tcbState := by rw [hin]; exact ⟨rfl, rfl, fun _ e => by cases e⟩
  -- the frame of the SC step
  have nc : NKT (ifCondRefillUnblockCheck (Z := Unit) x.tcbSchedContext (some false) (some false)) :=
    nkt_ifCondRefillUnblockCheck _ _ _
  have nd : NKT (NonDet.maybeM (schedContextResume (Z := Unit)) x.tcbSchedContext) :=
    nkt_maybeM nkt_schedContextResume _
  have ne : NKT (testPossibleSwitchTo (Z := Unit) t) := by
    unfold testPossibleSwitchTo; exact nkt_bind (nkt_gets _) fun _ => nkt_when _ (nkt_possibleSwitchTo _)
  have hK : ScTKw (fun p => p = t) σ σ' :=
    (tk_setThreadState hk hf0 ipcFree_restart _ mb).trans
      (((nc σb _ mc).trans (nd σc _ md)).trans (ne σd _ me)).ofFalse
  have le : LKM (fun _ => False) (testPossibleSwitchTo (Z := Unit) t) := by
    unfold testPossibleSwitchTo; exact lkm_bind (lkm_gets _) fun _ => lkm_when _ (lkm_possibleSwitchTo _)
  have hL : LK (fun _ => False) σ σ' :=
    (((lkm_setThreadState t .restart σ _ mb).trans (lkm_ifCondRefillUnblockCheck _ _ _ σb _ mc)).trans
      (lkm_maybeM (fun p => lkm_schedContextResume p) _ σc _ md)).trans (le σd _ me)
  have fc : FKA (ifCondRefillUnblockCheck (Z := Unit) x.tcbSchedContext (some false) (some false)) := by
    fk_auto
  have fd : FKA (NonDet.maybeM (schedContextResume (Z := Unit)) x.tcbSchedContext) :=
    fk_maybeM (fun p => by fk_auto) _
  have fe : FKA (testPossibleSwitchTo (Z := Unit) t) := by
    unfold testPossibleSwitchTo; exact fk_bind (fk_gets _) fun _ => fk_when _ (by fk_auto)
  have hF : FK σ σ' :=
    ((((fk_setThreadState t .restart) σ _ mb).trans (fc σb _ mc)).trans (fd σc _ md)).trans (fe σd _ me)
  have pe : Pres (true, true) (testPossibleSwitchTo (Z := Unit) t) := by
    unfold testPossibleSwitchTo
    exact pres_bind (pres_gets (f := (true, true)) _) fun _ => pres_when (f := (true, true)) _
      (pres_possibleSwitchTo (f := (true, true)) _)
  have hsok : SOK (true, true) σ σ' :=
    ((((pres_setThreadState (f := (true, true)) t .restart) σ _ mb).trans
      ((pres_ifCondRefillUnblockCheck (f := (true, true)) _ _ _) σb _ mc)).trans
      ((pres_maybeM (f := (true, true)) (fun p => pres_schedContextResume (f := (true, true)) p) _) σc _ md)).trans
      (pe σd _ me)
  -- `BK`
  have hBb : BK σ σb := by
    rw [hσb]
    refine ⟨fun u y hu hq => ?_, fun p y n hp ha => ?_⟩
    · by_cases e : u = t
      · subst e
        simp only [updK, Function.update_self, Option.some.injEq, KernelObject.tcb.injEq] at hu
        subst hu; simp [ipcQueuedThreadState] at hq
      · exact ⟨y, by simpa [updK, e] using hu, hq⟩
    · have hpt : p ≠ t := by rintro rfl; simp [updK] at hp
      exact ⟨y, by simpa [updK, hpt] using hp, ha, fun _ e => Or.inl e⟩
  have bc : BKM (ifCondRefillUnblockCheck (Z := Unit) x.tcbSchedContext (some false) (some false)) :=
    bkm_of nc (MaxK.mk_ifCondRefillUnblockCheck' _ _ _)
  have bd : BKM (NonDet.maybeM (schedContextResume (Z := Unit)) x.tcbSchedContext) :=
    bkm_of nd (MaxK.mk_maybeM (fun p => by unf_ref; mk_auto) _)
  have be : BKM (testPossibleSwitchTo (Z := Unit) t) := by
    refine bkm_of ne ?_
    unfold testPossibleSwitchTo
    exact MaxK.mk_bind (MaxK.mk_gets _) fun _ => MaxK.mk_when _ (MaxK.mk_possibleSwitchTo' _)
  have hBK : BK σ σ' := hBb.trans (((bc σb _ mc).trans (bd σc _ md)).trans (be σd _ me))
  -- the current thread's facts: `MidK` up to the switch
  have mkb : MidK σ σb := by
    rw [hσb]
    exact MidK.upd hk (fun _ _ h => (h.elim htc hti).elim) (fun _ _ e => by cases e)
  have mkc : MidK σb σc := by
    cases hsc : x.tcbSchedContext with
    | none =>
      rw [hsc] at mc
      unfold ifCondRefillUnblockCheck NonDet.maybeM at mc
      have e := congrArg Prod.snd (Set.mem_singleton_iff.1 mc)
      simp only at e
      rw [e]; exact MidK.refl _
    | some p =>
      rw [hsc] at mc
      refine mka_ifCondRefillUnblockCheck p (some false) (some false) σb ?_ _ mc
      show p ≠ σb.curSc
      rw [hσb]
      show p ≠ σ.curSc
      intro e
      obtain ⟨y1, n1, hy1, hy1t⟩ := hI.back t x p hk hsc
      obtain ⟨xt, hkt, hxs, -⟩ := hC.tcb
      obtain ⟨y2, n2, hy2, hy2t⟩ := hI.back _ xt σ.curSc hkt hxs
      rw [← e, hy1] at hy2; cases hy2
      exact htc (Option.some.inj (hy1t.symm.trans hy2t))
  have mkd : MidK σc σd := by
    cases hsc : x.tcbSchedContext with
    | none =>
      rw [hsc] at md
      have e : σd = σc := congrArg Prod.snd (Set.mem_singleton_iff.1 md)
      rw [e]; exact MidK.refl _
    | some p =>
      rw [hsc] at md mc
      refine mka_schedContextResume p σc ?_ _ md
      intro y n u hy hyu
      obtain ⟨y0, hy0, -, e0⟩ := MaxK.mk_ifCondRefillUnblockCheck' _ _ _ σb _ mc p y n hy
      obtain ⟨y1, n1, hy1, hy1t⟩ := hI.back t x p hk hsc
      have hpt : p ≠ t := fun e => by rw [e, hk] at hy1; cases hy1
      have hkb : σb.kheap p = σ.kheap p := by rw [hσb]; exact Function.update_of_ne hpt _ _
      rw [hkb, hy1] at hy0; cases hy0
      rw [e0, hy1t] at hyu; cases hyu
      have m2 := mkb.trans mkc
      exact ⟨by rw [m2.idle]; exact hti, by rw [m2.ct]; exact htc⟩
  have mk : MidK σ σd := (mkb.trans mkc).trans mkd
  have hAd : ActIdle σd := by
    refine ⟨fun u hu => (hns u (mk.sw u hu)).elim, ?_⟩
    obtain ⟨xi, h1, h2, h3, h4⟩ := hA.2
    obtain ⟨y, hy, e1, e2⟩ := mk.idT xi h1
    refine ⟨y, by rw [mk.idle]; exact hy, by rw [e1]; exact h2, by rw [e2]; exact h3, fun hm => ?_⟩
    rw [mk.idle] at hm
    rcases mk.rq _ hm with h | ⟨h, -⟩
    · exact h4 h
    · exact h rfl
  -- the switch
  unfold testPossibleSwitchTo at he
  rw [nd_gets_bind] at he
  by_cases hs : schedulable t σd = true
  · rw [hs] at he
    have he' : possibleSwitchTo (Z := Unit) t σd = ({((), σ')}, False) := he
    have hmn := mkn_possibleSwitchTo ⟨by rw [mk.idle]; exact hti, by rw [mk.ct]; exact htc⟩ ((), σ')
      (by rw [he']; exact Set.mem_singleton _)
    exact ⟨hK, hL, hF, hsok, hBK, mk.toN.trans hmn, hAd.possibleSwitchTo hId hs he'⟩
  · rw [show schedulable t σd = false by simpa using hs] at he
    have e : σ' = σd :=
      the_result (show NonDet.when (false = true) (possibleSwitchTo (Z := Unit) t) σd = ({((), σd)}, False) from rfl) he
    subst e
    exact ⟨hK, hL, hF, hsok, hBK, mk.toN, hAd⟩

end Spec

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

set_option maxHeartbeats 4000000 in
/-- **A thread with a cap in a slot leaves the dead set** (`cover_cap` at the
same state). -/
theorem JAtZ.undead (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {x t : U64} (hxS : IsSlot Z.th x)
    (hc : capAt (L.mem s) x = ok (.Thread t)) (ht : t ∈ Z.T) :
    JAtZ (L := L) arI AR Z H Cs Ac Lst (D \ {t}) s a σ := by
  have hw : P1.WritesIn st s s (TFoot st Z.T Z.N Z.C Z.c s σ) := P1.WritesIn.refl _ _
  have hK : ScTKw (fun _ => False) σ σ := ScTKw.refl _ σ
  have hHt : H t = some .tcb := J.zH.1 t ht
  have hfit := J.kern.heap.fits t _ hHt
  simp only [P1.HKind.bits] at hfit
  have hcov := J.cover_cap hw hxS hc (fun h => by cases h) (ok_inj (phys_eq _).symm) rfl (range_thread t hfit)
    fun k hk' => by
      rw [hHt] at hk'; cases hk'
      exact ⟨by simp only [P1.HKind.bits]; omega, fun z h => by cases h⟩
  exact { J with
    jcov := J.sc_jcov hw (fun q hq => J.jcov.dead q hq.1) (fun q hq hn => by
      have e : q = t := Classical.byContradiction fun e => hn ⟨hq, e⟩
      subst e; exact hcov) rfl
    kern := J.sc_kern hw hK (FK.refl σ) J.xtop rfl Set.sdiff_subset }

set_option maxHeartbeats 16000000 in
/-- **`restart`'s tail at `J`** (module docstring). -/
theorem JAtZ.restartTailJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (hmb : sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    {t : U64} (ht : t ∈ Z.T) (htD : t ∉ D) {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x))
    (hin : x.tcbState = .inactive) (htc : t.bv ≠ σ.curThread) (hns : ∀ u, σ.schedulerAction ≠ .switchThread u)
    (hC : CurInv σ)
    (hRS : ∀ σb σc, Fl4Spec.setThreadState (Z := Unit) t.bv .restart σ = ({((), σb)}, False) →
      Fl4Spec.ifSporadicCurScTestRefillUnblockCheck (Z := Unit) x.tcbSchedContext σb = ({((), σc)}, False) →
      RelOK σc ∧ (∀ xc p, σc.kheap t.bv = some (.tcb xc) → xc.tcbSchedContext = some p →
        ∃ y n, σc.kheap p = some (.schedContext y n) ∧ y.scTcb = some t.bv) ∧
      ∀ σd, Fl4Spec.NonDet.maybeM (Fl4Spec.schedContextResume (Z := Unit)) x.tcbSchedContext σc =
        ({((), σd)}, False) → Inv σd) :
    restartTailF st arI s a t ⦃ r => r.2 = a ∧ ∀ Ac', P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H
      (P1.Heap.frame H) (P1.Heap.replies H) (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac' r.1 →
      L.mem r.1 (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) = L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) →
      ∃ σ', specRestartTail t.bv x.tcbSchedContext σ = ({((), σ')}, False) ∧
        ∃ Lst' : U64 → List U64, JAtZ (L := L) arI AR Z H Cs Ac' Lst' D r.1 a σ' ⦄ := by
  have hX := J.xtop
  have hS := hX.fin.1.1.1
  have hR := hX.fin.1.1.2.2.1
  have hti : t.bv ≠ σ.idleThread := fun e => by
    obtain ⟨xi, hki, -, hti, -⟩ := J.act.2
    rw [← e, hk] at hki; cases hki; rw [hin] at hti; cases hti
  have hq : ∀ n ∈ Z.N, ∀ z, σ.kheap n.bv = some (.notification z) → t.bv ∉ z.ntfnObj.ntfnQueue := by
    intro n _ z hz hm
    obtain ⟨xu, hku, hsu⟩ := (J.sv.ntfnQ n.bv z hz).2 t.bv hm
    rw [hk] at hku; cases hku; rw [hin] at hsu; cases hsu
  have hrq : ∀ d p, t.bv ∉ σ.readyQueues d p := by
    intro d p hm
    obtain ⟨x', -, -, -, h1, -, h3, -⟩ := J.inv.rq d p t.bv hm
    rw [hk] at h1; cases h1; rw [hin] at h3; cases h3
  refine WP.spec_mono (restart_tail_kfoot s a σ hR hS ht hk hin hq hrq hRS hmb) ?_
  rintro ⟨s', a'⟩ ⟨ha', σb, σc, σd, σ', hb, hc, hd, he, hR', hS', hI', hw⟩
  simp only at ha' hR' hS' hw ⊢
  subst a'
  refine ⟨rfl, fun Ac' hblk hDbg => ⟨σ', specRestartTail_eq hb hc hd he, ?_⟩⟩
  have hId : Inv σd := (hRS σb σc hb hc).2.2 σd hd
  obtain ⟨hK, hL, hF, hsok, hBK, hMK, hAI⟩ := restartTail_specJ hk hin hti htc hns J.inv J.act hC hb hc hd he hId
  have hwT := WritesIn.tfoot_of_kfoot hw
  have hX' : XTopAt (L := L) AR Z s' a σ' := xtop_sc_step hX J.ip J.nk hwT hK hS' hR' id
  have hN' : NSC Z.N Z.C σ' := nsc_of_lk J.nsc hK hL
  obtain ⟨-, hY', hM', ⟨Lst', hCR', hRF'⟩, hRP', -⟩ :=
    ScAll.of_k hS J.rp J.yld J.mcp J.call J.rfree ⟨⟨hS', hR', hN', hI'⟩, hw, hsok⟩
  obtain ⟨hC', hOw', hO'⟩ := hMK.mid3 hC J.off J.inv ⟨L.curW s, J.thT _ J.kern.curT, J.kern.cur.symm⟩
  have hdead : ∀ q ∈ D, DeadP (L := L) H s' q := fun q hq =>
    J.deadP_sc_stepQ hX' hwT hK (fun _ hp => absurd (show q = t from P1.eq_of_bv hp) (fun e => htD (e ▸ hq)))
      hL hF hAI.1 (fun h => h) (J.jcov.dead q hq)
  have hcr : CurRunM σ' := by
    by_cases hr : σ'.schedulerAction = .resumeCurThread
    · have h0 : σ.schedulerAction = .resumeCurThread := by
        cases e : σ.schedulerAction with
        | resumeCurThread => rfl
        | switchThread u => exact (hns u e).elim
        | chooseNewThread => rw [hMK.cn e] at hr; cases hr
      right
      rcases J.curRun.resolve_left (fun h => h h0) with hrun | hidl
      · left
        intro y hy
        obtain ⟨xt, hkt, -, -⟩ := hC.tcb
        obtain ⟨y', hy', -, e⟩ := hMK.ctT xt hkt
        rw [hMK.ct, hy'] at hy; cases hy
        rw [e]; exact hrun xt hkt
      · right; rw [hMK.ct, hMK.idle]; exact hidl
    · exact Or.inl hr
  exact ⟨Lst', J.sc_frame hwT hK hX' hCR' hRF' hY' hM' (J.sc_buf hwT hK) hRP' (J.sc_apart hwT hK)
    (J.sc_jpl hwT hK) (J.sc_jcov hwT hdead (fun q hq hn => absurd hq hn) (J.idleW_keep hX'.fin.1.1.1 hF.2))
    (J.sc_kern hwT hK hF hX' hDbg fun _ h => h) (J.sc_utc hwT hK hDbg) hN' hI' hC'
    (Or.inl (hC'.elim hOw' (curOwn_of_curInv hX'.fin.1.1.1 hI'))) hO' hAI (J.bsa.bk hBK hsok) hcr hblk⟩

set_option maxHeartbeats 16000000 in
/-- **`sched::restart` at `J`** (module docstring). -/
theorem JAtZ.restartTcbJ (hAT : P0.ArchTotal arI)
    (hSd : JCancelAt (L := L) arI AR Z.th fun ts => ∃ e d, ts = .blockedOnSend e d)
    (hNt : JCancelAt (L := L) arI AR Z.th fun ts => ∃ n, ts = .blockedOnNotification n)
    (hRv : JCancelAt (L := L) arI AR Z.th fun ts => ∃ e r d, ts = .blockedOnReceive e r d)
    (hRp : JCancelAt (L := L) arI AR Z.th fun ts => ∃ r, ts = .blockedOnReply r)
    (hmb : sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T) {x0 : U64}
    (hxS : IsSlot Z.th x0) (hcap : capAt (L.mem s) x0 = ok (.Thread t))
    (hC : CurInv σ) (hns : ∀ u, σ.schedulerAction ≠ .switchThread u) (hcr : CurRun σ) :
    sched.restart st arI s a t ⦃ r => r.2 = a ∧ ∃ σ', Fl4Spec.restart (Z := Unit) t.bv σ = ({((), σ')}, False) ∧
      ∃ (V : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
        JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac' Lst' D' r.1 r.2 σ' ⦄ := by
  have J0 := J.undead hxS hcap ht
  have htD : t ∉ D \ {t} := fun h => h.2 rfl
  have hP0 := J.ip
  have hI := J.xtop.irelK J.ks J.buf
  have htH : t ∈ P1.Heap.tcbs H := J.zH.1 t ht
  obtain ⟨x, hk, hTR⟩ := hI.1.tcb t ht
  -- P1's `BlkOK` and the debug word across the whole restart
  have hP1 : sched.restart st arI s a t ⦃ r => P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H
      (P1.Heap.frame H) (P1.Heap.replies H) (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac r.1 ∧
      L.mem r.1 (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) = L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) ⦄ := by
    obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := J.blk
    refine WP.spec_mono (P1.sched.restart.allK hAT s a t Q R h0 htH hB hX hS) fun r hr => ?_
    obtain ⟨s', a'⟩ := r
    try simp only [WP.uncurry'_pair] at hr
    obtain ⟨Q', R', h1, hB1, hX1, hS1, -, hF⟩ := hr
    exact ⟨⟨⟨Q', R', h1⟩, hB1, hX1, hS1, ⟨hSg.sub, fun b hb => by rw [hF.1]; exact hSg.ks b hb,
      fun o h1' h2' => by rw [hF.1]; exact hSg.ksΩ o h1' h2'⟩⟩, J.kw_dbg hF⟩
  -- the debug word and the kernel-state base through `cancel_ipc`
  obtain ⟨⟨Q0, R0, h0⟩, -, ⟨hO, hR, -⟩, -, hSg⟩ := J.blk
  have hreply : L.mem s (P1.stA t) = sched.TS_BLOCKED_ON_REPLY → P1.ReplyT st (P1.Heap.replies H)
      (P1.Heap.scs H) s t := fun hs => by
    obtain ⟨h1, h2⟩ := hR.reply t htH hs
    exact ⟨h1, h2, hR.next _ h1, hR.prev _ h1⟩
  have hkwc : ipc.cancel_ipc st arI s a t ⦃ r => L.ksb r.1 = L.ksb s ∧
      L.mem r.1 (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) = L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) ⦄ := by
    refine WP.spec_mono (P1.ipc.cancel_ipc.kw s a t h0 htH hO hSg.sub hreply
      (fun h1 h2 => (hR.recv t htH h1 h2).1)) fun r hr => ?_
    obtain ⟨s1, a1⟩ := r
    try simp only [WP.uncurry'_pair] at hr
    exact ⟨hr.1, J.kw_dbg hr⟩
  have hspec0 : Fl4Spec.restart (Z := Unit) t.bv σ =
      Fl4Spec.NonDet.when (¬ Fl4Spec.runnable x.tcbState = true ∧ ¬ Fl4Spec.idle x.tcbState) (do
        Fl4Spec.cancelIpc t.bv
        Fl4Spec.setThreadState t.bv .restart
        Fl4Spec.ifSporadicCurScTestRefillUnblockCheck x.tcbSchedContext
        Fl4Spec.NonDet.maybeM Fl4Spec.schedContextResume x.tcbSchedContext
        Fl4Spec.testPossibleSwitchTo t.bv) σ := by
    unfold Fl4Spec.restart
    rw [nd_bind_one (getThreadState_eq hk), nd_bind_one (getTcbObjRef_eq _ hk)]
  have hmain : sched.restart st arI s a t ⦃ r => ∀ Ac', P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H
      (P1.Heap.frame H) (P1.Heap.replies H) (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac' r.1 →
      L.mem r.1 (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) = L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) →
      r.2 = a ∧ ∃ σ', Fl4Spec.restart (Z := Unit) t.bv σ = ({((), σ')}, False) ∧
        ∃ (V : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
          JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac' Lst' D' r.1 r.2 σ' ⦄ := by
    unfold sched.restart
    rw [is_stopped_eq (ts := x.tcbState) hTR.st]
    simp only [bind_ok]
    by_cases hc : ¬ Fl4Spec.runnable x.tcbState = true ∧ ¬ Fl4Spec.idle x.tcbState
    swap
    · rw [decide_eq_false hc]
      simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
      intro _ _ _
      refine ⟨trivial, σ, ?_, Z.vs, Ac, Lst, D, J⟩
      rw [hspec0, Fl4Spec.NonDet.when, if_neg hc]; rfl
    rw [decide_eq_true hc]
    simp only [↓reduceIte]
    have hnr : Fl4Spec.runnable x.tcbState = false := by simpa using hc.1
    have htc0 : t.bv ≠ σ.curThread := fun e => by
      have := hcr x (e ▸ hk); rw [hnr] at this; cases this
    -- `cancel_ipc`, the dead set kept (without `t`)
    have hcan : ipc.cancel_ipc st arI s a t ⦃ r => r.2 = a ∧ ∃ σa,
        Fl4Spec.cancelIpc (Z := Unit) t.bv σ = ({((), σa)}, False) ∧ ∃ xa, σa.kheap t.bv = some (.tcb xa) ∧
        xa.tcbState = .inactive ∧ ∃ (V : XVs) (Ac1 : Set U64) (Lst1 : U64 → List U64),
          JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac1 Lst1 (D \ {t}) r.1 r.2 σa ⦄ := by
      by_cases hfree : IpcFree x.tcbState
      · have hin : x.tcbState = .inactive := by
          revert hfree hc
          cases x.tcbState <;> simp [IpcFree, Fl4Spec.epBlocked, Fl4Spec.ntfnBlocked, Fl4Spec.runnable, Fl4Spec.idle]
        refine WP.spec_mono (J0.cancelFreeJ ht hk hfree) ?_
        rintro r ⟨h1, h2, V, J1⟩
        exact ⟨h1, _, h2, { x with tcbFault := none }, by simp [updK], hin, V, Ac, Lst, J1⟩
      have hcases : (∃ e d, x.tcbState = .blockedOnSend e d) ∨ (∃ e r d, x.tcbState = .blockedOnReceive e r d) ∨
          (∃ n, x.tcbState = .blockedOnNotification n) ∨ (∃ r, x.tcbState = .blockedOnReply r) := by
        revert hfree
        cases x.tcbState <;> simp [IpcFree, Fl4Spec.epBlocked, Fl4Spec.ntfnBlocked]
      have hP : ipc.cancel_ipc st arI s a t ⦃ r => r.2 = a ∧ ∃ σ', Fl4Spec.cancelIpc (Z := Unit) t.bv σ =
          ({((), σ')}, False) ∧ ∃ (V : XVs) (Ac' : Set U64) (Lst' : U64 → List U64),
            JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac' Lst' (D \ {t}) r.1 r.2 σ' ⦄ := by
        rcases hcases with h | h | h | h
        · exact hSd Z H Cs Ac Lst (D \ {t}) s a σ rfl J0 t ht x hk h
        · exact hRv Z H Cs Ac Lst (D \ {t}) s a σ rfl J0 t ht x hk h
        · exact hNt Z H Cs Ac Lst (D \ {t}) s a σ rfl J0 t ht x hk h
        · exact hRp Z H Cs Ac Lst (D \ {t}) s a σ rfl J0 t ht x hk h
      refine WP.spec_mono (WP.spec_and hP (cancel_ipc_irelP (ar := arI) hP0 (removeTcbHypP_ok hP0) s a σ hI ht hk
        J.sv J.obj J.inv (removeTcbOK_fault hP0 hI ht hk J.removeTcbOK))) ?_
      rintro r ⟨⟨h1, σ1, h2, V, Ac1, Lst1, J1⟩, -, σ1', x1, h2', -, hk1, hs1⟩
      have e1 : σ1' = σ1 := by
        rw [h2] at h2'; exact ((Prod.mk.inj (Set.singleton_injective (congrArg Prod.fst h2'))).2).symm
      subst e1
      have hin : x1.tcbState = .inactive := by
        rw [hs1]; revert hfree; cases x.tcbState <;> simp [IpcFree, Fl4Spec.epBlocked, Fl4Spec.ntfnBlocked, cancelSt]
      exact ⟨h1, σ1', h2', x1, hk1, hin, V, Ac1, Lst1, J1⟩
    refine WP.spec_bind (WP.spec_and hcan hkwc) ?_
    rintro ⟨s1, a1⟩ ⟨⟨h1, σa, hca, xa, hka, hina, V1, Ac1, Lst1, J1⟩, hks1, hd1⟩
    simp only at h1 hks1 hd1
    subst a1
    -- the spec facts after `cancel_ipc`
    have hma : ((), σa) ∈ (Fl4Spec.cancelIpc (Z := Unit) t.bv σ).1 := by rw [hca]; exact Set.mem_singleton _
    have hKa := TscK.sk_cancelIpc t.bv σ ((), σa) hma
    have hxsa : xa.tcbSchedContext = x.tcbSchedContext := by
      obtain ⟨y0, hy0, e⟩ := hKa.1 _ _ hka; rw [hk] at hy0; cases hy0; exact e
    have hIK : IK t.bv σ σa := ikm_cancelIpc.of_eq hca
    have hFa : σa.curSc = σ.curSc :=
      ((PPS.tk_cancelIpc' (E := fun _ => False) (c := σ.curSc) t.bv) σ rfl ((), σa) hma).csc
    have hCa : CurInv σa := by
      obtain ⟨xt, hkt, hxs, hnb⟩ := hC.tcb
      obtain ⟨ya, hya, e1, e2⟩ := hIK.tcbF hkt
      refine ⟨⟨ya, by rw [hKa.2.2]; exact hya, by rw [e1, hFa]; exact hxs, by rw [e2 (Ne.symm htc0)]; exact hnb⟩,
        ?_, ?_, ?_⟩
      · obtain ⟨y0, n0, hy0⟩ := hC.sc
        obtain ⟨y', hy', -⟩ := hIK.scF hy0
        exact ⟨y', n0, by rw [hFa]; exact hy'⟩
      · intro hne y n hy
        rw [hFa] at hne hy
        obtain ⟨y0, hy0, hk0⟩ := hIK.scB hy
        have := hC.active hne y0 n hy0
        show Fl4Spec.activeSc y.scRefillMax = true
        rw [hk0.2.1]; exact this
      · rw [hKa.2.2, hIK.2.2.1]; exact hC.notRel
    have hnsa : ∀ u, σa.schedulerAction ≠ .switchThread u :=
      (Vs.ak_cancelIpc' t.bv).noSwitch (x := ((), σa)) hma hns
    have htca : t.bv ≠ σa.curThread := by rw [hKa.2.2]; exact htc0
    have hRS0 : RestartSpecOK t.bv σ := Sched.restartSpecOK_of J.inv J.sv.scSpor
    have hRS : ∀ σb σc, Fl4Spec.setThreadState (Z := Unit) t.bv .restart σa = ({((), σb)}, False) →
        Fl4Spec.ifSporadicCurScTestRefillUnblockCheck (Z := Unit) xa.tcbSchedContext σb = ({((), σc)}, False) →
        RelOK σc ∧ (∀ xc p, σc.kheap t.bv = some (.tcb xc) → xc.tcbSchedContext = some p →
          ∃ y n, σc.kheap p = some (.schedContext y n) ∧ y.scTcb = some t.bv) ∧
        ∀ σd, Fl4Spec.NonDet.maybeM (Fl4Spec.schedContextResume (Z := Unit)) xa.tcbSchedContext σc =
          ({((), σd)}, False) → Inv σd := by
      intro σb σc hb hc'
      rw [hxsa] at hc' ⊢
      exact hRS0 x σa σb σc hk hnr hca hb hc'
    show restartTailF st arI s1 a t ⦃ _ ⦄
    refine WP.spec_mono (J1.restartTailJ hmb ht htD hka hina htca hnsa hCa hRS) ?_
    rintro r ⟨hr2, hr⟩ Ac' hblk hd6
    have hn1 := P1.nodeAt_of_ksb hks1
    obtain ⟨σ', he', Lst', J'⟩ := hr Ac' hblk (by rw [hn1, hd6, hd1])
    refine ⟨hr2, σ', ?_, V1, Ac', Lst', D \ {t}, by rw [hr2]; exact J'⟩
    rw [hspec0, Fl4Spec.NonDet.when, if_pos hc, nd_bind_one hca]
    rw [hxsa] at he'
    exact he'
  refine WP.spec_mono (WP.spec_and hP1 hmain) ?_
  rintro ⟨s6, a6⟩ ⟨⟨hb6, hd6⟩, hM⟩
  exact hM Ac hb6 hd6

end

end

end Fl4Proofs.P3
