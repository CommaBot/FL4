/-
P3 (DESIGN.md §9), TCB: **`restart`'s tail on `SchedRel`, with its write
set** (toward `sched.restart` at `J`): after `cancel_ipc`, a stopped thread
`t` (now `Inactive`) set to `Restart`, the sporadic unblock check, the SC's
`resume` and the switch (`restartTailF`), against the spec's
`specRestartTail`, on the scheduler and notification relations with
`KFoot` as the write set (`restart_tail_kfoot`, as IpcResumeJ's
`restart_tcb_irelS` on `IRel`, here on `SchedRel` so that the SC step
machinery `JAtZ.sc_frame` applies). The spec facts the steps read after the
unblock check are `RestartSpecOK`'s (premise `hRS`, discharged at the
caller by `restartSpecOK_of`).
-/
import Fl4Proofs.P3.XTopJointReadRegs
import Fl4Proofs.P3.IpcResumeJ
import Fl4Proofs.P3.SpecDet
import Fl4Proofs.P1.QueueRestartFoot
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Det Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {ar : machine.Arch A}
variable {N T C : Set U64} {c : U64}

/-- **`restart` after `cancel_ipc`** (FL4's code, as `sched.restart`'s
continuation). -/
def restartTailF (st : machine.Store S) (ar : machine.Arch A) (s : S) (a : A) (t : U64) : Result (S × A) := do
  let s2 ← sched.set_thread_state st s t sched.TS_RESTART
  let i ← obj.Tcb.sc st t s2
  let b1 ← sporadic.sc_sporadic st s2 i
  let s3 ← (if b1 then (do
      let s4 ← sched.cur_sc st s2
      let b2 ← core.cmp.PartialEq.ne.trait_default obj.Sc.Insts.CoreCmpPartialEqSc i s4
      (if b2 then sporadic.unblock_check st s2 i else ok s2))
    else ok s2)
  let (s4, a2) ← schedcontext.resume st ar s3 a i
  let b2 ← sched.is_schedulable st s4 t
  if b2 then (do
    let s5 ← sched.possible_switch_to st s4 t
    ok (s5, a2))
  else ok (s4, a2)

/-- **The spec's `restart` after `cancelIpc`** (the SC read before). -/
def specRestartTail (t : Fl4Spec.ObjRef) (sc : Option Fl4Spec.ObjRef) : Fl4Spec.SMonad Unit Unit := do
  Fl4Spec.setThreadState t .restart
  Fl4Spec.ifSporadicCurScTestRefillUnblockCheck sc
  Fl4Spec.NonDet.maybeM Fl4Spec.schedContextResume sc
  Fl4Spec.testPossibleSwitchTo t

/-- A deterministic step's member outcome is its only one. -/
theorem det_single {α : Type} {m : Fl4Spec.SMonad Unit α} (hd : Det m) {σ : Fl4Spec.State Unit} {x : α × Fl4Spec.State Unit}
    (hx : x ∈ (m σ).1) (hn : ¬ (m σ).2) : m σ = ({x}, False) := by
  refine Prod.ext (Set.eq_singleton_iff_unique_mem.2 ⟨hx, fun y hy => (hd.at σ) y x hy hx⟩) (eq_false hn)

set_option maxHeartbeats 16000000 in
/-- **`restart`'s tail on `SchedRel`** (module docstring). -/
theorem restart_tail_kfoot (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hR : NtfnStateRel N T (L.mem s) σ) (hS : SchedRel st N T C c s σ) {t : U64} (ht : t ∈ T)
    {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x)) (hin : x.tcbState = .inactive)
    (hq : ∀ n ∈ N, ∀ z, σ.kheap n.bv = some (.notification z) → t.bv ∉ z.ntfnObj.ntfnQueue)
    (hrq : ∀ d p, t.bv ∉ σ.readyQueues d p)
    (hRS : ∀ σb σc, Fl4Spec.setThreadState (Z := Unit) t.bv .restart σ = ({((), σb)}, False) →
      Fl4Spec.ifSporadicCurScTestRefillUnblockCheck (Z := Unit) x.tcbSchedContext σb = ({((), σc)}, False) →
      RelOK σc ∧ (∀ xc p, σc.kheap t.bv = some (.tcb xc) → xc.tcbSchedContext = some p →
        ∃ y n, σc.kheap p = some (.schedContext y n) ∧ y.scTcb = some t.bv) ∧
      ∀ σd, Fl4Spec.NonDet.maybeM (Fl4Spec.schedContextResume (Z := Unit)) x.tcbSchedContext σc =
        ({((), σd)}, False) → Inv σd)
    (hmb : sporadic.min_budget ar a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄) :
    restartTailF st ar s a t ⦃ r => r.2 = a ∧ ∃ σ', specRestartTail t.bv x.tcbSchedContext σ = ({((), σ')}, False) ∧
      NtfnStateRel N T (L.mem r.1) σ' ∧ SchedRel st N T C c r.1 σ' ∧ Inv σ' ∧
      P1.WritesIn st s r.1 (KFoot st T N C c s σ) ⦄ := by
  have hP := hS.placed
  unfold restartTailF
  have hcode : sched.TS_RESTART.val = tsCode .restart := by unfold sched.TS_RESTART; rfl
  refine WP.spec_bind (WP.spec_and (set_thread_state_refines s σ hR hS ht hk hq _ .restart hcode
    (fun _ e => by cases e)) (set_thread_state_sfoot hS ht _)) ?_
  rintro s2 ⟨⟨σb, hstb, hRb, hSb⟩, hw2⟩
  have hσb := the_result (Notif.setThreadState_eq (Z := Unit) .restart hk) hstb
  have hkb : σb.kheap t.bv = some (.tcb { x with tcbState := .restart }) := by
    rw [hσb, stsAct_kheap]; simp [updK]
  have hkpb : ∀ p, p ≠ t.bv → σb.kheap p = σ.kheap p := fun p hp => by
    rw [hσb, stsAct_kheap]; simp [updK, hp]
  have hzb : SzKeep σ σb := SzKeep.of_tcb hkpb hkb
  have hw2' : P1.WritesIn st s s2 (KFoot st T N C c s σ) := WritesIn.kfoot_of_sfoot hw2
  -- the SC word
  obtain ⟨Qb, Rb, hcb, hsb⟩ := hSb.lists
  obtain ⟨xb, hkb', -, -, hscb, -⟩ := hsb.tcb t ht
  rw [hkb] at hkb'; cases hkb'
  have hxi : x.tcbSchedContext = optRef (L.mem s2 (P1.scA t)) := hscb
  -- the sporadic unblock
  refine restart_unblock_spec (WP.spec_and (unblock_sporadic_refines s2 σb hSb t ht)
    (unblock_sporadic_kfoot hSb t ht)) ?_
  rintro s3 ⟨⟨hnf, σc, hmc, hfc, hkvc, hSc⟩, hw3⟩
  have hu' : Fl4Spec.ifSporadicCurScTestRefillUnblockCheck (Z := Unit) x.tcbSchedContext σb = ({((), σc)}, False) := by
    have hd : Det (specUnblock t.bv) := by
      unfold specUnblock Fl4Spec.getTcbObjRef
      exact det_bind (det_threadGet _ _) fun _ => det_ifCondRefillUnblockCheck _ _ _
    have e := det_single hd hmc hnf
    unfold specUnblock Fl4Spec.getTcbObjRef at e
    rw [nd_bind_one (threadGet_eq _ hkb)] at e
    exact e
  have hRc : NtfnStateRel N T (L.mem s3) σc := hRb.frame hP hfc hkvc
  obtain ⟨hRelc, hBackc, hInvd⟩ := hRS σb σc hstb hu'
  have hw3' : P1.WritesIn st s s3 (KFoot st T N C c s σ) := WritesIn.kfoot_trans hw2' (SzKeepC.of hzb) hw3
  have hKb := TscK.sk_setThreadState' t.bv .restart σ ((), σb) (by rw [hstb]; exact Set.mem_singleton _)
  have hKc := TscK.sk_unblock x.tcbSchedContext σb ((), σc) (by rw [hu']; exact Set.mem_singleton _)
  obtain ⟨Qc, Rc, hcc, hsc⟩ := hSc.lists
  obtain ⟨xc, hkc, hxc⟩ : ∃ xc, σc.kheap t.bv = some (.tcb xc) ∧ xc.tcbSchedContext = x.tcbSchedContext := by
    obtain ⟨xc, hkc, -⟩ := hsc.tcb t ht
    obtain ⟨y0, hy0, e⟩ := hKc.1 _ _ hkc
    rw [hkb] at hy0; cases hy0; exact ⟨xc, hkc, e⟩
  obtain ⟨xc', hkc', -, -, hscc, -⟩ := hsc.tcb t ht
  rw [hkc] at hkc'; cases hkc'
  have hi3 : L.mem s3 (P1.scA t) = L.mem s2 (P1.scA t) := optRef_inj.1 (by rw [← hscc, hxc, hxi])
  -- the switch
  have tail : ∀ (s4 : S) (σd : Fl4Spec.State Unit), NtfnStateRel N T (L.mem s4) σd → SchedRel st N T C c s4 σd →
      Inv σd → P1.WritesIn st s s4 (KFoot st T N C c s σ) →
      (do
        let b2 ← sched.is_schedulable st s4 t
        if b2 then (do
          let s5 ← sched.possible_switch_to st s4 t
          ok (s5, a))
        else ok (s4, a)) ⦃ r => r.2 = a ∧ ∃ σe, Fl4Spec.testPossibleSwitchTo (Z := Unit) t.bv σd = ({((), σe)}, False) ∧
          NtfnStateRel N T (L.mem r.1) σe ∧ SchedRel st N T C c r.1 σe ∧ Inv σe ∧
          P1.WritesIn st s r.1 (KFoot st T N C c s σ) ⦄ := by
    intro s4 σd hRd hSd hId hwd
    step with Sched.sched.is_schedulable.spec' as ⟨b2, hb2⟩
    rw [hb2, schedulable_eq hRd hSd ht]
    by_cases hsch : Fl4Spec.schedulable t.bv σd = true
    · rw [if_pos hsch]
      refine WP.spec_bind (WP.spec_and (possible_switch_to_refines s4 σd hRd hSd hId.actReady t ht)
        (possible_switch_to_sfoot hRd hSd hId.actReady ht)) ?_
      rintro s5 ⟨⟨σe, hps, hke, hfe, hSe⟩, hw5⟩
      rw [WP.spec_ok]
      refine ⟨rfl, σe, ?_, hRd.frame hSd.placed hfe (KView.of_kheap hke), hSe,
        hId.qchange (possibleSwitchTo_qchange hId hsch hps),
        WritesIn.kfoot_trans hwd (SzKeepC.of (SzKeep.refl σ)) (WritesIn.kfoot_of_sfoot hw5)⟩
      unfold Fl4Spec.testPossibleSwitchTo
      rw [nd_gets_bind, hsch]; exact hps
    · rw [if_neg hsch, WP.spec_ok]
      refine ⟨rfl, σd, ?_, hRd, hSd, hId, hwd⟩
      unfold Fl4Spec.testPossibleSwitchTo
      rw [nd_gets_bind, show Fl4Spec.schedulable t.bv σd = false by simpa using hsch]; rfl
  have hfin : ∀ σd σe, Fl4Spec.NonDet.maybeM (Fl4Spec.schedContextResume (Z := Unit)) x.tcbSchedContext σc =
      ({((), σd)}, False) → Fl4Spec.testPossibleSwitchTo (Z := Unit) t.bv σd = ({((), σe)}, False) →
      specRestartTail t.bv x.tcbSchedContext σ = ({((), σe)}, False) := by
    intro σd σe h1 h2
    unfold specRestartTail
    rw [nd_bind_one hstb, nd_bind_one hu', nd_bind_one h1, h2]
  -- the resume
  by_cases hi0 : L.mem s2 (P1.scA t) = 0#u64
  · unfold schedcontext.resume
    step with Sched.obj.Sc.is_null.spec' as ⟨bz, hbz⟩
    rw [hbz, decide_eq_true hi0]
    simp only [↓reduceIte, bind_ok]
    have hm0 : Fl4Spec.NonDet.maybeM (Fl4Spec.schedContextResume (Z := Unit)) x.tcbSchedContext σc =
        ({((), σc)}, False) := by rw [hxi, hi0, optRef_zero]; rfl
    refine WP.spec_mono (tail s3 σc hRc hSc (hInvd σc hm0) hw3') ?_
    rintro r ⟨h1, σe, h2, h3, h4, h5, h6⟩
    exact ⟨h1, σe, hfin σc σe hm0 h2, h3, h4, h5, h6⟩
  have hiC : L.mem s2 (P1.scA t) ∈ C := by rw [← hi3]; exact hsc.scMem t ht (by rw [hi3]; exact hi0)
  have hxcs : xc.tcbSchedContext = some (L.mem s2 (P1.scA t)).bv := by rw [hxc, hxi, Notif.optRef_ne hi0]
  obtain ⟨y, n, hky, hyt⟩ := hBackc xc _ hkc hxcs
  have htw := word24_of hSc hiC hky hyt
  have hnq : ∀ x', σc.kheap t.bv = some (.tcb x') → t.bv ∉ σc.readyQueues x'.tcbDomain x'.tcbPriority := by
    intro x' _ hm
    rw [hKc.2.1, hKb.2.1] at hm
    exact hrq _ _ hm
  refine WP.spec_bind (resume_refines s3 a σc hRc hSc hRelc hmb hiC hi0 ht htw hi3 hnq) ?_
  rintro ⟨s4, a2⟩ ⟨rfl, σd, hres, hkd, -, -, -, -, hfd, hwd, hSd⟩
  have hm1 : Fl4Spec.NonDet.maybeM (Fl4Spec.schedContextResume (Z := Unit)) x.tcbSchedContext σc =
      ({((), σd)}, False) := by rw [hxi, Notif.optRef_ne hi0]; exact hres
  refine WP.spec_mono (tail s4 σd (hRc.frame hSd.placed hfd (KView.of_kheap hkd)) hSd (hInvd σd hm1)
    (WritesIn.kfoot_trans hw3' (SzKeepC.of (SzKeep.refl σ)) (WritesIn.kfoot_of_sfoot hwd))) ?_
  rintro r ⟨h1, σe, h2, h3, h4, h5, h6⟩
  exact ⟨h1, σe, hfin σd σe hm1 h2, h3, h4, h5, h6⟩

end

end

end Fl4Proofs.P3
