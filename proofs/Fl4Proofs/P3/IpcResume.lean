/-
P3 (DESIGN.md §9), TCB invocations: **Resume on `IRel`** (`sched::restart`
against l4v `restart`), and its leaf at `XTop` (XTopTcbSched's
`ResumeXLeaf`).

A stopped thread (`is_stopped_eq`: inactive or blocked, l4v's
`¬ runnable ∧ ¬ idle`): `cancel_ipc` (`cancel_ipc_irel`), `Restart`
(`set_thread_state_c`), the sporadic unblock check (`unblock_irel`), the
SC's resume (`resume_refines`, lifted by `tk_liftCW`), and the switch to it
if schedulable (`switch_top`). The spec reads the thread's SC before
`cancel_ipc`, FL4 after: IpcTscK's `TSK` (`cancel_ipc` and
`set_thread_state` keep it, and the ready queues, so the thread, not
runnable at the start, is in none, `Inv.rq`).
-/
import Fl4Proofs.P3.IpcSuspend
import Fl4Proofs.P3.IpcTscK
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Ipc
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Sched

noncomputable section

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]
variable {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

/-- `is_stopped`: inactive or blocked (l4v `¬ runnable ∧ ¬ idle`). -/
theorem is_stopped_eq {s : S} {t : U64} {ts : Fl4Spec.ThreadState}
    (h : (L.mem s (P1.stA t)).val = tsCode ts) :
    sched.is_stopped st s t = ok (decide (¬ Fl4Spec.runnable ts = true ∧ ¬ Fl4Spec.idle ts)) := by
  have e : obj.Tcb.state st t s = ok (L.mem s (P1.stA t)) := by
    obtain ⟨v, hv, hv'⟩ := Sched.rrt_exists (P1.obj.Tcb.state.spec (st := st) s t); rw [hv, hv']
  unfold sched.is_stopped sched.is_blocked
  simp only [e, bind_ok]
  generalize L.mem s (P1.stA t) = w at h ⊢
  have ev : ∀ k : U64, (w = k ↔ w.val = k.val) := fun k => ⟨fun h => h ▸ rfl, fun h => UScalar.eq_of_val_eq h⟩
  unfold sched.TS_INACTIVE sched.TS_BLOCKED_ON_RECV sched.TS_BLOCKED_ON_SEND sched.TS_BLOCKED_ON_NTFN
    sched.TS_BLOCKED_ON_REPLY
  simp only [ev, h]
  cases ts <;> simp [tsCode, Fl4Spec.runnable, Fl4Spec.idle]

/-- The FL4 sporadic unblock of `restart`, as `unblock_sporadic`. -/
theorem restart_unblock_spec {s : S} {t : U64} {X : Type} {k : U64 → S → Result X} {P : S → Prop}
    {Q : X → Prop} (h : notification.unblock_sporadic st s t ⦃ P ⦄)
    (hk : ∀ s3, P s3 → k (L.mem s (scA t)) s3 ⦃ Q ⦄) :
    (do
      let i ← obj.Tcb.sc st t s
      let b1 ← sporadic.sc_sporadic st s i
      let s3 ← (if b1 then (do
          let s4 ← sched.cur_sc st s
          let b2 ← core.cmp.PartialEq.ne.trait_default obj.Sc.Insts.CoreCmpPartialEqSc i s4
          (if b2 then sporadic.unblock_check st s i else ok s))
        else ok s)
      k i s3) ⦃ Q ⦄ := by
  have e : obj.Tcb.sc st t s = ok (L.mem s (scA t)) := by
    obtain ⟨v, hv, hv'⟩ := Sched.rrt_exists (P1.obj.Tcb.sc.spec (st := st) s t); rw [hv, hv']
  unfold notification.unblock_sporadic at h
  rw [e] at h ⊢
  simp only [Std.bind_tc_ok, bind_ok] at h ⊢
  have := WP.spec_bind h hk
  simpa only [Std.bind_assoc_eq, Std.bind_assoc] using this

set_option maxHeartbeats 16000000 in
/-- **`restart` on `IRel`** (module docstring). Named: `SchedValid`,
`ObjCover`, `Inv` at the start (`cancel_ipc_irel`) [J], `RemoveTcbHyp`, `Inv`
and `ActReady` on `IRel` [J], the platform's `MIN_BUDGET`. -/
theorem restart_tcb_irel (hP0 : IPlaced N T E R B) (hRT : RemoveTcbHyp st th cr N T C E R B c)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (hX : IRel st th cr N T C E R B c s σ) {t : U64} (ht : t ∈ T)
    (hSV : SchedValid σ) (hOC : ObjCover N T E R C σ) (hInv : Inv σ)
    (hInvI : ∀ s' σ', IRel st th cr N T C E R B c s' σ' → Inv σ')
    (hAct : ∀ s' σ', IRel st th cr N T C E R B c s' σ' → ActReady σ')
    (hmb : sporadic.min_budget ar a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄) :
    sched.restart st ar s a t ⦃ r => r.2 = a ∧ ∃ σ', Fl4Spec.restart (Z := Unit) t.bv σ = ({((), σ')}, False) ∧
      IRel st th cr N T C E R B c r.1 σ' ⦄ := by
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
    refine ⟨trivial, σ, ?_, hX⟩
    rw [hspec0 (pure ()), Fl4Spec.NonDet.when, if_neg hc]; rfl
  rw [decide_eq_true hc]
  simp only [↓reduceIte]
  have hnr : Fl4Spec.runnable x.tcbState = false := by simpa using hc.1
  -- `cancel_ipc`
  refine WP.spec_bind (cancel_ipc_irel hP0 hRT s a σ hX ht hk hSV hOC hInv) ?_
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
  have tail : ∀ (s4 : S) (σd : Fl4Spec.State Unit), IRel st th cr N T C E R B c s4 σd →
      (do
        let b2 ← sched.is_schedulable st s4 t
        if b2 then do
          let s5 ← sched.possible_switch_to st s4 t
          ok (s5, a1)
        else ok (s4, a1)) ⦃ r => r.2 = a1 ∧ ∃ σe, Fl4Spec.testPossibleSwitchTo (Z := Unit) t.bv σd = ({((), σe)}, False) ∧
          IRel st th cr N T C E R B c r.1 σe ⦄ := by
    intro s4 σd hXd
    step with Sched.sched.is_schedulable.spec' as ⟨b2, hb2⟩
    rw [hb2, schedulable_eq hXd.1.toN hXd.2.2.1 ht]
    by_cases hsch : Fl4Spec.schedulable t.bv σd = true
    · rw [if_pos hsch]
      refine WP.spec_bind (switch_top hP0 s4 σd hXd.1 hXd.2 (hAct _ _ hXd) t ht) ?_
      rintro s5 ⟨σe, hps, -, hf, hv, hSe⟩
      rw [WP.spec_ok]
      refine ⟨rfl, σe, ?_, hXd.1.frame hP0 hf hv, hSe⟩
      unfold Fl4Spec.testPossibleSwitchTo
      rw [nd_gets_bind, hsch]; exact hps
    · rw [if_neg hsch, WP.spec_ok]
      refine ⟨rfl, σd, ?_, hXd⟩
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
    refine WP.spec_mono (tail s3 σc hXc) ?_
    rintro r ⟨h1, σe, h2, h3⟩
    refine ⟨h1, σe, hfin σc σe ?_ h2, h3⟩
    rw [hxi, hi0, optRef_zero]; rfl
  have hiC : L.mem s2 (scA t) ∈ C := by rw [← hi3]; exact hsc.scMem t ht (by rw [hi3]; exact hi0)
  have hxcs : xc.tcbSchedContext = some (L.mem s2 (scA t)).bv := by rw [hxc, hxi, Notif.optRef_ne hi0]
  obtain ⟨y, n, hky, hyt⟩ := (hInvI _ _ hXc).back t.bv xc _ hkc hxcs
  have htw := word24_of hXc.2.2.1 hiC hky hyt
  have hnq : ∀ x', σc.kheap t.bv = some (.tcb x') → t.bv ∉ σc.readyQueues x'.tcbDomain x'.tcbPriority := by
    intro x' _ hm
    rw [hK3.2] at hm
    obtain ⟨x0, -, -, -, hk0, -, hr0, -⟩ := hInv.rq _ _ _ hm
    rw [hk] at hk0; cases hk0
    rw [hnr] at hr0; cases hr0
  refine WP.spec_bind (resume_refines s3 a1 σc hXc.1.toN hXc.2.2.1 (hInvI _ _ hXc).relOK hmb hiC hi0 ht htw hi3 hnq) ?_
  rintro ⟨s4, a2⟩ ⟨rfl, σd, hres, hkd, -, -, -, -, hfd, hwd, hSd⟩
  have hK : ScTKw (fun q => q = σc.curThread) σc σd :=
    ScTKw.ofFalse (NKT.of_eq (nkt_schedContextResume _) hres)
  have hXd := tk_liftCW hP0 hXc (hwd.mono fun _ h => Or.inl (Or.inl (Or.inl h))) hK hSd
    (hXc.1.toN.frame hXc.2.2.1.placed hfd (KView.of_kheap hkd))
  refine WP.spec_mono (tail s4 σd hXd) ?_
  rintro r ⟨h1, σe, h2, h3⟩
  refine ⟨h1, σe, hfin σd σe ?_ h2, h3⟩
  rw [hxi, Notif.optRef_ne hi0]; exact hres

end

end

end Fl4Proofs.P3.Ipc

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **What Resume needs beyond `IRel`**, at a state: `reply_remove_tcb`'s
facts (`RemoveTcbOK`, with `Inv`, `SchedValid`, `ObjCover`) and `ActReady`
[J]. -/
def ResumeOK (st : machine.Store S) [L : P1.LawfulStore st] (Z : XSets) (s : S) (σ : Fl4Spec.State Unit) : Prop :=
  RemoveTcbOK st Z.N Z.T Z.C Z.E Z.R Z.c s σ ∧ Notif.ActReady σ

/-- **`ResumeXLeaf`**: the restart (`xleaf_restart`), then `restart_tcb_irel`.
Named, at every `Z` the entry's `XTopAt` holds at: `KsApart`, the IPC
placement, the target among the TCBs, `ResumeOK` on `IRel`; `BufWordRel` at
`XTopAt`; `CurRun` [J]; the platform's `MIN_BUDGET`. -/
theorem resumeXLeaf_of {AR : A → Fl4Spec.Cr3 → Prop} {s : S} {ar : A} {σ σ1 : Fl4Spec.State Unit} {p : U64}
    (hst : Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False)) (hC : CurRun σ)
    (hmb : sporadic.min_budget arI ar ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hZ : ∀ Z : XSets, XTopAt (L := L) AR Z s ar σ → KsApart Z.N Z.T Z.E Z.R Z.B (L.ksb s) ∧
      IPlaced Z.N Z.T Z.E Z.R Z.B ∧ p ∈ Z.T ∧
      (∀ s' σ', IRel st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c s' σ' → ResumeOK st Z s' σ'))
    (hBW : ∀ (Z : XSets) s' a' σ', XTopAt (L := L) AR Z s' a' σ' → BufWordRel Z.T (L.mem s') σ') :
    ResumeXLeaf (L := L) arI AR s ar σ σ1 p := by
  refine xleaf_restart hst hC (fun Z hX => (hZ Z hX).1) hBW fun Z s1 hX _ _ hI1 => ?_
  obtain ⟨-, hP0, hpT, hOK⟩ := hZ Z hX
  have hAR : AR ar σ.archState.x64CurrentCr3 := hX.fin.1.1.2.2.2.2.2.2
  obtain ⟨⟨Lst, -, -, -, -, hInv, -, hSV, hOC⟩, -⟩ := hOK _ _ hI1
  refine WP.spec_bind (restart_tcb_irel (ar := arI) hP0 (removeTcbHyp_of hP0 fun s' σ' h => (hOK s' σ' h).1)
    s1 ar σ1 hI1 hpT hSV hOC hInv (fun s' σ' h => let ⟨⟨_, _, _, _, _, hI, _⟩, _⟩ := hOK s' σ' h; hI)
    (fun s' σ' h => (hOK s' σ' h).2) hmb) ?_
  rintro ⟨s2, a2⟩ ⟨rfl, σ2, hm, hI2⟩
  exact (WP.spec_ok _).2 ⟨rfl, hAR, ((), σ2), by rw [hm]; exact Set.mem_singleton _, hI2⟩

end

end

end Fl4Proofs.P3
