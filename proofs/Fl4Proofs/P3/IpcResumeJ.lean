/-
P3 (DESIGN.md §9), TCB invocations: **Resume from `JAtZ`** (the fold's
re-scoping of `resumeXLeaf_of`): `restart_tcb_irelS` (`RestartSpecOK`, the
spec facts after `restart`'s first three steps, in place of `Inv` and
`ActReady` at every `IRel`), `resumeXLeafJ`.
-/
import Fl4Proofs.P3.IpcResume
import Fl4Proofs.P3.IpcSuspendJ
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Ipc
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Sched

noncomputable section

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]
variable {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

/-- **The spec facts `restart` reads after its first three steps** [J-step,
spec only]: from a stopped thread, after `cancel_ipc`, `Restart` and the
sporadic unblock check, the release queue's facts (`RelOK`) and the thread's
SC bound back to it; after the SC's resume, `Inv` (l4v: `valid_release_q`,
`sym_refs`, `valid_sched`; from `Inv` and `ActSched` at the start, the thread
in no queue and not the action's target). -/
def RestartSpecOK (t : Fl4Spec.ObjRef) (σ : Fl4Spec.State Unit) : Prop :=
  ∀ (x : Fl4Spec.Tcb) (σa σb σc : Fl4Spec.State Unit), σ.kheap t = some (.tcb x) →
    Fl4Spec.runnable x.tcbState = false →
    Fl4Spec.cancelIpc (Z := Unit) t σ = ({((), σa)}, False) →
    Fl4Spec.setThreadState (Z := Unit) t .restart σa = ({((), σb)}, False) →
    Fl4Spec.ifSporadicCurScTestRefillUnblockCheck (Z := Unit) x.tcbSchedContext σb = ({((), σc)}, False) →
    RelOK σc ∧ (∀ xc p, σc.kheap t = some (.tcb xc) → xc.tcbSchedContext = some p →
      ∃ y n, σc.kheap p = some (.schedContext y n) ∧ y.scTcb = some t) ∧
    ∀ σd, Fl4Spec.NonDet.maybeM (Fl4Spec.schedContextResume (Z := Unit)) x.tcbSchedContext σc =
      ({((), σd)}, False) → Inv σd

set_option maxHeartbeats 16000000 in
/-- **`restart` on `IRel`, re-scoped** (`restart_tcb_irel` with its
"at every `IRel`" premises replaced): `SchedValid`, `ObjCover`, `Inv` at the
start; `RemoveTcbHyp` at the states `P`, `P` at the fault clear; the spec
facts after the first three steps and the SC's resume (`RestartSpecOK`); the
platform's `MIN_BUDGET`. `Inv` after (the switch a `QChange`). -/
theorem restart_tcb_irelS (hP0 : IPlaced N T E R B) {P : S → Fl4Spec.State Unit → Prop}
    (hRT : RemoveTcbHypP st th cr N T C E R B c P)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (hX : IRel st th cr N T C E R B c s σ) {t : U64} (ht : t ∈ T)
    (hSV : SchedValid σ) (hOC : ObjCover N T E R C σ) (hInv : Inv σ)
    (hPf : ∀ x, σ.kheap t.bv = some (.tcb x) → (∃ r, x.tcbState = .blockedOnReply r) →
      P (L.wr s (tFaultA t) 0#u64) (updK σ t.bv (.tcb { x with tcbFault := none })))
    (hRS : RestartSpecOK t.bv σ)
    (hmb : sporadic.min_budget ar a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄) :
    sched.restart st ar s a t ⦃ r => r.2 = a ∧ ∃ σ', Fl4Spec.restart (Z := Unit) t.bv σ = ({((), σ')}, False) ∧
      IRel st th cr N T C E R B c r.1 σ' ∧ σ'.curThread = σ.curThread ∧ Inv σ' ⦄ := by
  obtain ⟨x, hk, hTR⟩ := hX.1.tcb t ht
  have hspec0 : ∀ (m : Fl4Spec.SMonad Unit Unit), Fl4Spec.restart (Z := Unit) t.bv σ =
      Fl4Spec.NonDet.when (¬ Fl4Spec.runnable x.tcbState = true ∧ ¬ Fl4Spec.idle x.tcbState) (do
        Fl4Spec.cancelIpc t.bv
        Fl4Spec.setThreadState t.bv .restart
        Fl4Spec.ifSporadicCurScTestRefillUnblockCheck x.tcbSchedContext
        Fl4Spec.NonDet.maybeM Fl4Spec.schedContextResume x.tcbSchedContext
        Fl4Spec.testPossibleSwitchTo t.bv) σ := by
    intro _
    unfold Fl4Spec.restart
    rw [nd_bind_one (getThreadState_eq hk), nd_bind_one (getTcbObjRef_eq _ hk)]
  unfold sched.restart
  rw [is_stopped_eq (ts := x.tcbState) hTR.st]
  simp only [bind_ok]
  by_cases hc : ¬ Fl4Spec.runnable x.tcbState = true ∧ ¬ Fl4Spec.idle x.tcbState
  swap
  · rw [decide_eq_false hc]
    simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    refine ⟨trivial, σ, ?_, hX, rfl, hInv⟩
    rw [hspec0 (pure ()), Fl4Spec.NonDet.when, if_neg hc]; rfl
  rw [decide_eq_true hc]
  simp only [↓reduceIte]
  have hnr : Fl4Spec.runnable x.tcbState = false := by simpa using hc.1
  -- `cancel_ipc`
  refine WP.spec_bind (cancel_ipc_irelP hP0 hRT s a σ hX ht hk hSV hOC hInv (hPf x hk)) ?_
  rintro ⟨s1, a1⟩ ⟨rfl, σa, xa, hca, hXa, hka, hsa⟩
  have hsa' : xa.tcbState = .inactive := by
    rw [hsa]; generalize hx : x.tcbState = ts at hc hnr
    cases ts <;> simp_all [cancelSt, Fl4Spec.runnable, Fl4Spec.idle]
  have hKa := TscK.sk_cancelIpc t.bv σ ((), σa) (by rw [hca]; exact Set.mem_singleton _)
  have hxsa : xa.tcbSchedContext = x.tcbSchedContext := by
    obtain ⟨y0, hy0, e⟩ := hKa.1 _ _ hka; rw [hk] at hy0; cases hy0; exact e
  -- `Restart`
  obtain ⟨xa', hka', hTRa⟩ := hXa.1.tcb t ht
  rw [hka] at hka'; cases hka'
  have hwa : (L.mem s1 (tStA t)).val = 0 := by rw [hTRa.st, hsa']; rfl
  have hq := IpcRel.not_ep_queued hXa.1 (t := t) ⟨by rw [hwa]; decide, by rw [hwa]; decide⟩
  have hH := ipcCore_top (st := st) (th := th) (cr := cr) (N := N) (C := C) (c := c) hP0.e
  have hSRa := IpcRel.toSRN hXa.1 hXa.2
  have hcode : sched.TS_RESTART.val = tsCode .restart := by unfold sched.TS_RESTART; rfl
  refine WP.spec_bind (set_thread_state_c hH hP0 hP0.e _ _ hXa.1.toE hSRa ht hka hq (by rw [hsa']; decide)
    .restart (by decide) sched.TS_RESTART hcode) ?_
  rintro s2 ⟨hE2, hS2⟩
  have hXb := IpcRel.ofSRN hE2 hS2
  have hstb := Notif.setThreadState_eq (Z := Unit) .restart hka
  set σb := stsAct (updK σa t.bv (.tcb { xa with tcbState := .restart })) t.bv with hσb
  have hKb := TscK.sk_setThreadState' t.bv .restart σa ((), σb) (by rw [hstb]; exact Set.mem_singleton _)
  have hkb : σb.kheap t.bv = some (.tcb { xa with tcbState := .restart }) := by
    rw [hσb, stsAct_kheap]; simp [updK]
  -- the SC word
  obtain ⟨Qb, Rb, hcb, hsb⟩ := hXb.2.2.1.lists
  obtain ⟨xb, hkb', -, -, hscb, -⟩ := hsb.tcb t ht
  rw [hkb] at hkb'; cases hkb'
  have hxi : x.tcbSchedContext = optRef (L.mem s2 (scA t)) := by rw [← hxsa]; exact hscb
  -- the sporadic unblock
  refine restart_unblock_spec (unblock_irel hP0 s2 σb hXb t ht) ?_
  rintro s3 ⟨σc, hu, -, -, hXc⟩
  have hu' : Fl4Spec.ifSporadicCurScTestRefillUnblockCheck (Z := Unit) x.tcbSchedContext σb = ({((), σc)}, False) := by
    unfold specUnblock at hu
    rw [nd_bind_one (getTcbObjRef_eq _ hkb)] at hu
    rw [← hxsa]; exact hu
  have hKc := TscK.sk_unblock x.tcbSchedContext σb ((), σc) (by rw [hu']; exact Set.mem_singleton _)
  obtain ⟨hRelc, hBackc, hInvd⟩ := hRS x σa σb σc hk hnr hca hstb hu'
  have hK3 := (hKa.trans hKb).trans hKc
  obtain ⟨xc, hkc, hxc⟩ : ∃ xc, σc.kheap t.bv = some (.tcb xc) ∧ xc.tcbSchedContext = x.tcbSchedContext := by
    obtain ⟨xc, hkc, -⟩ := hXc.1.tcb t ht
    obtain ⟨y0, hy0, e⟩ := hK3.1 _ _ hkc
    rw [hk] at hy0; cases hy0; exact ⟨xc, hkc, e⟩
  obtain ⟨Qc, Rc, hcc, hsc⟩ := hXc.2.2.1.lists
  obtain ⟨xc', hkc', -, -, hscc, -⟩ := hsc.tcb t ht
  rw [hkc] at hkc'; cases hkc'
  have hi3 : L.mem s3 (scA t) = L.mem s2 (scA t) := optRef_inj.1 (by rw [← hscc, hxc, hxi])
  -- the resume, and the switch
  have tail : ∀ (s4 : S) (σd : Fl4Spec.State Unit), IRel st th cr N T C E R B c s4 σd → Inv σd →
      (do
        let b2 ← sched.is_schedulable st s4 t
        if b2 then do
          let s5 ← sched.possible_switch_to st s4 t
          ok (s5, a1)
        else ok (s4, a1)) ⦃ r => r.2 = a1 ∧ ∃ σe, Fl4Spec.testPossibleSwitchTo (Z := Unit) t.bv σd = ({((), σe)}, False) ∧
          IRel st th cr N T C E R B c r.1 σe ∧ σe.curThread = σd.curThread ∧ Inv σe ⦄ := by
    intro s4 σd hXd hId
    step with Sched.sched.is_schedulable.spec' as ⟨b2, hb2⟩
    rw [hb2, schedulable_eq hXd.1.toN hXd.2.2.1 ht]
    by_cases hsch : Fl4Spec.schedulable t.bv σd = true
    · rw [if_pos hsch]
      refine WP.spec_bind (switch_top hP0 s4 σd hXd.1 hXd.2 hId.actReady t ht) ?_
      rintro s5 ⟨σe, hps, -, hf, hv, hSe⟩
      rw [WP.spec_ok]
      have hmem : ((), σe) ∈ (Fl4Spec.possibleSwitchTo (Z := Unit) t.bv σd).1 := by rw [hps]; rfl
      obtain ⟨-, -, -, -, -, -, hct⟩ := nkm_possibleSwitchTo t.bv σd _ hmem
      refine ⟨rfl, σe, ?_, ⟨hXd.1.frame hP0 hf hv, hSe⟩, hct, hId.qchange (possibleSwitchTo_qchange hId hsch hps)⟩
      unfold Fl4Spec.testPossibleSwitchTo
      rw [nd_gets_bind, hsch]; exact hps
    · rw [if_neg hsch, WP.spec_ok]
      refine ⟨rfl, σd, ?_, hXd, rfl, hId⟩
      unfold Fl4Spec.testPossibleSwitchTo
      rw [nd_gets_bind, show Fl4Spec.schedulable t.bv σd = false by simpa using hsch]; rfl
  have hfin : ∀ σd σe, Fl4Spec.NonDet.maybeM (Fl4Spec.schedContextResume (Z := Unit)) x.tcbSchedContext σc =
      ({((), σd)}, False) → Fl4Spec.testPossibleSwitchTo (Z := Unit) t.bv σd = ({((), σe)}, False) →
      Fl4Spec.restart (Z := Unit) t.bv σ = ({((), σe)}, False) := by
    intro σd σe h1 h2
    rw [hspec0 (pure ()), Fl4Spec.NonDet.when, if_pos hc, nd_bind_one hca, nd_bind_one hstb, nd_bind_one hu',
      nd_bind_one h1, h2]
  by_cases hi0 : L.mem s2 (scA t) = 0#u64
  · unfold schedcontext.resume
    step with Sched.obj.Sc.is_null.spec' as ⟨bz, hbz⟩
    rw [hbz, decide_eq_true hi0]
    simp only [↓reduceIte, bind_ok]
    have hm0 : Fl4Spec.NonDet.maybeM (Fl4Spec.schedContextResume (Z := Unit)) x.tcbSchedContext σc =
        ({((), σc)}, False) := by rw [hxi, hi0, optRef_zero]; rfl
    refine WP.spec_mono (tail s3 σc hXc (hInvd σc hm0)) ?_
    rintro r ⟨h1, σe, h2, h3, h4, h5⟩
    exact ⟨h1, σe, hfin σc σe hm0 h2, h3, h4.trans hK3.2.2, h5⟩
  have hiC : L.mem s2 (scA t) ∈ C := by rw [← hi3]; exact hsc.scMem t ht (by rw [hi3]; exact hi0)
  have hxcs : xc.tcbSchedContext = some (L.mem s2 (scA t)).bv := by rw [hxc, hxi, Notif.optRef_ne hi0]
  obtain ⟨y, n, hky, hyt⟩ := hBackc xc _ hkc hxcs
  have htw := word24_of hXc.2.2.1 hiC hky hyt
  have hnq : ∀ x', σc.kheap t.bv = some (.tcb x') → t.bv ∉ σc.readyQueues x'.tcbDomain x'.tcbPriority := by
    intro x' _ hm
    rw [hK3.2.1] at hm
    obtain ⟨x0, -, -, -, hk0, -, hr0, -⟩ := hInv.rq _ _ _ hm
    rw [hk] at hk0; cases hk0
    rw [hnr] at hr0; cases hr0
  refine WP.spec_bind (resume_refines s3 a1 σc hXc.1.toN hXc.2.2.1 hRelc hmb hiC hi0 ht htw hi3 hnq) ?_
  rintro ⟨s4, a2⟩ ⟨rfl, σd, hres, hkd, -, -, -, -, hfd, hwd, hSd⟩
  have hK : ScTKw (fun q => q = σc.curThread) σc σd :=
    ScTKw.ofFalse (NKT.of_eq (nkt_schedContextResume _) hres)
  have hXd := tk_liftCW hP0 hXc (hwd.mono fun _ h => Or.inl (Or.inl (Or.inl h))) hK hSd
    (hXc.1.toN.frame hXc.2.2.1.placed hfd (KView.of_kheap hkd))
  have hm1 : Fl4Spec.NonDet.maybeM (Fl4Spec.schedContextResume (Z := Unit)) x.tcbSchedContext σc =
      ({((), σd)}, False) := by rw [hxi, Notif.optRef_ne hi0]; exact hres
  refine WP.spec_mono (tail s4 σd hXd (hInvd σd hm1)) ?_
  rintro r ⟨h1, σe, h2, h3, h4, h5⟩
  exact ⟨h1, σe, hfin σd σe hm1 h2, h3, h4.trans (hK.ct.trans hK3.2.2), h5⟩

end

end

end Fl4Proofs.P3.Ipc

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}

set_option maxHeartbeats 4000000 in
/-- **Resume from `JAtZ`** (`resumeXLeaf_of` re-scoped): the restart
(`xleaf_restartJ`), then `restart_tcb_irelS` with `JAtZ`'s `SchedValid`,
`ObjCover`, `Inv` after the restart and `RemoveTcbOK` carried to the fault
clear. Named: the target among the TCBs, `RestartSpecOK` after the restart
[J-step, spec only], the platform's `MIN_BUDGET` [P]. -/
theorem resumeXLeafJ {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {ar : A} {σ σ1 : Fl4Spec.State Unit} {p : U64}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ) (hJS : JStepHyps (L := L) arI AR Z.th)
    (hst : Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False)) (hpT : p ∈ Z.T)
    (hRS : RestartSpecOK p.bv σ1)
    (hmb : sporadic.min_budget arI ar ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄) :
    ResumeXLeaf (L := L) arI AR s ar σ σ1 p := by
  refine xleaf_restartJ J hni hJS hst fun s1 Ac' Lst' D' J' _ hI1 => ?_
  have hP0 := J.ip
  have hAR : AR ar σ.archState.x64CurrentCr3 := J.xtop.fin.1.1.2.2.2.2.2.2
  refine WP.spec_bind (restart_tcb_irelS (ar := arI) hP0 (removeTcbHypP_ok hP0) s1 ar σ1 hI1 hpT J'.sv J'.obj
    J'.inv (fun x hk hfr => removeTcbOK_fault hP0 hI1 hpT hk hfr J'.removeTcbOK) hRS hmb) ?_
  rintro ⟨s2, a2⟩ ⟨rfl, σ2, hm, hI2, -, -⟩
  exact (WP.spec_ok _).2 ⟨rfl, hAR, ((), σ2), by rw [hm]; exact Set.mem_singleton _, hI2⟩

end

end

end Fl4Proofs.P3
