/-
P3 (DESIGN.md §9), scheduler: **`schedule` with the domain switch, up to
the FPU** (KENTRY-PLAN.md sch5 (B)): ScNextDomC's `cn_refines0`,
`cn_enq0`/`cn_app0`, `switch_branch_refines0`, `schedule_refinesWP0` with
the corrected arch premises of sch4 (A): `ArchSwF`/`ArchNdF` [P] (ScArchF,
ScNextDomF) in place of `ArchSw`/`ArchNd` (false whenever the spec has an
FPU owner), `FpuOwnOK` [J] (l4v X64 `valid_cur_fpu`) at the switch state
(carried from the fire predicate across `awaken` and the queue operations
as in ScScheduleF: `ow_awaken`, `ow_tcbSchedAction`), and
`HeapEqUpToFpu σ σ'` for `σ'.kheap = σ.kheap` in the posts. Same proofs
(scripted copy, ScScheduleF's changes applied to ScNextDomC).
`schedule_refinesWP0F` supersedes `schedule_refinesWP0`.
-/
import Fl4Proofs.P3.ScNextDomC
import Fl4Proofs.P3.ScNextDomF
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3

noncomputable section

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]

theorem cn_refines0F {N T C : Set U64} {c : U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) (hN : NSC N C σ) (hI : Inv σ)
    (hA : ArchSwF st ar N T C c) (hAN : ArchNdF st N T C c) (hfo : FpuOwnOK σ) (hvr : VsRootOK T σ)
    (hNk : ∀ n ∈ N, n.val + 40 ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ n.val)
    (hdt : σ.domainTime ≠ 0 ∨ NdOK (L := L) s σ) {t : U64} (ht : t ∈ T)
    (hsch : Fl4Spec.schedulable t.bv σ = true) (enq : Bool) :
    (do
      let s5 ← if enq then sched.enqueue st s t else sched.append st s t
      let s6 ← sched.set_action st s5 sched.ACTION_CHOOSE_NEW
      sched.schedule_choose_new_thread st ar s6 a) ⦃ r => ∃ σ', (do
        Fl4Spec.tcbSchedAction (Z := Unit) (if enq then Fl4Spec.tcbSchedEnqueue else Fl4Spec.tcbSchedAppend) t.bv
        Fl4Spec.setSchedulerAction .chooseNewThread
        Fl4Spec.scheduleChooseNewThread) σ =
      ({((), { σ' with schedulerAction := .resumeCurThread })}, False) ∧
      SchedRel st N T C c r.1 σ' ∧ NtfnStateRel N T (L.mem r.1) σ' ∧ NSC N C σ' ∧ Inv σ' ∧
      (σ'.curThread = σ.idleThread ∨ Fl4Spec.schedulable σ'.curThread σ = true) ∧
      σ'.curSc = σ.curSc ∧ σ'.releaseQueue = σ.releaseQueue ∧ HeapEqUpToFpu σ σ' ∧ TK0 σ σ' ∧ P1.WritesIn st s r.1 (SFootN st T c s) ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨x, scp, -, -, hk, hsc, -, -, -, hnr⟩ := schedulable_inv hsch
  have hrel0 : (L.mem s (inqA t) &&& sched.Q_RELEASE) = 0#u64 := by
    by_contra hne
    exact hnr (by rw [hs.rel]; exact List.mem_map_of_mem ((hc.released t ht).1 hne))
  -- the queue operation
  have hq : (if enq then sched.enqueue st s t else sched.append st s t) ⦃ s5 => ∃ σ5,
      Fl4Spec.tcbSchedAction (Z := Unit) (if enq then Fl4Spec.tcbSchedEnqueue else Fl4Spec.tcbSchedAppend) t.bv σ =
        ({((), σ5)}, False) ∧ QChange σ σ5 ∧ (σ5.schedulerAction = σ.schedulerAction ∧ TK σ σ5 ∧
          σ5.curSc = σ.curSc ∧ σ5.idleThread = σ.idleThread) ∧
        FootEq N T (L.mem s) (L.mem s5) ∧ SchedRel st N T C c s5 σ5 ∧ WritesIn st s s5 (SFoot st T c s) ∧
        σ5.domainList = σ.domainList ∧ σ5.domainIndex = σ.domainIndex ∧ σ5.domainStartIndex = σ.domainStartIndex ⦄ := by
    cases enq
    · refine WP.spec_mono (WP.spec_and (append_refines s σ hS t ht (fun _ => hrel0)) (append_sfoot hS ht)) ?_
      rintro s5 ⟨⟨σ5, he, -, -, hf, hS5⟩, hw5⟩
      have e := pair_eq (he.symm.trans (tcbSchedAction_gen hk _))
      refine ⟨σ5, he, ?_, ?_, hf, hS5, hw5, ?_⟩ <;> rw [← e]
      · exact qchange_append hk hsch
      · exact ⟨rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl⟩
      · exact ⟨rfl, rfl, rfl⟩
    · refine WP.spec_mono (WP.spec_and (enqueue_refines s σ hS t ht (fun _ => hrel0)) (enqueue_sfoot hS ht)) ?_
      rintro s5 ⟨⟨σ5, he, -, -, hf, hS5⟩, hw5⟩
      have e := pair_eq (he.symm.trans (tcbSchedAction_gen hk _))
      refine ⟨σ5, he, ?_, ?_, hf, hS5, hw5, ?_⟩ <;> rw [← e]
      · exact qchange_enqueue hk hsch
      · exact ⟨rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl⟩
      · exact ⟨rfl, rfl, rfl⟩
  refine WP.spec_bind hq ?_
  rintro s5 ⟨σ5, he, hq5, ⟨-, htk5, hcs5, hid5⟩, hf5, hS5, hw5, hdl5, hdi5, hds5⟩
  have hR5 := hR.frame hS.placed hf5 (KView.of_kheap hq5.1)
  have hI5 := hI.qchange hq5
  step with sched.set_action.spec' as ⟨s6, hs6⟩
  subst hs6
  have hc5 := hS5.lists.choose_spec.choose_spec.1.cur
  rw [hc5, choose_val']
  have hS6 := hS5.set_action (Or.inr (Or.inl rfl)) (a := .chooseNewThread) rfl
  have hf6 : FootEq N T (L.mem s5) (L.mem (L.wr s5 (L.nodeAt s5 c layout.node.SCHED_ACTION) 1#u64)) :=
    node_wr_foot hS5 (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION])
  set σ6 : Fl4Spec.State Unit := { σ5 with schedulerAction := .chooseNewThread }
  have hR6 : NtfnStateRel N T (L.mem (L.wr s5 (L.nodeAt s5 c layout.node.SCHED_ACTION) 1#u64)) σ6 :=
    hR5.frame hS5.placed hf6 (KView.of_kheap rfl)
  have hN6 : NSC N C σ6 := fun n hn x0 p hx hp => hN n hn x0 p (by rw [← hq5.1]; exact hx) hp
  have hI6 : Inv σ6 := hI5.congr rfl rfl rfl rfl
  have hw6 : WritesIn st s5 (L.wr s5 (L.nodeAt s5 c layout.node.SCHED_ACTION) 1#u64) (SFoot st T c s5) :=
    sfoot_wr_node hS5.lists.choose_spec.choose_spec.1.node (by simp [layout.node.SCHED_ACTION])
      (by simp [layout.node.SCHED_ACTION]) _
  have hdt6 : σ6.domainTime ≠ 0 ∨ NdOK (L := L) (L.wr s5 (L.nodeAt s5 c layout.node.SCHED_ACTION) 1#u64) σ6 :=
    hdt.imp (fun h => by show σ5.domainTime ≠ 0; rw [htk5.2.2.2.2.1]; exact h)
      (fun h => (h.sfoot hS hw5 hdl5 hdi5 hds5).sfoot hS5 hw6 rfl rfl rfl)
  have hNk6 : ∀ n ∈ N, n.val + 40 ≤ (L.ksb (L.wr s5 (L.nodeAt s5 c layout.node.SCHED_ACTION) 1#u64)).val ∨
      (L.ksb (L.wr s5 (L.nodeAt s5 c layout.node.SCHED_ACTION) 1#u64)).val + 13568 ≤ n.val := by
    rw [hw6.1, hw5.1]; exact hNk
  have hfo6 : FpuOwnOK σ6 := hfo.of (show σ5.archState.x64CurrentFpuOwner = σ.archState.x64CurrentFpuOwner from OW.of_eq (ow_tcbSchedAction _ _) he) hq5.1
  have hvr6 : VsRootOK T σ6 := hvr.of_eq hq5.1 (show σ5.archState.x64AsidTable = σ.archState.x64AsidTable from asid_of_crk (Vs.crk_tcbSchedAction' _ _) he)
  refine WP.spec_mono (scnt_refines0F _ a σ6 hS6 hR6 hN6 hI6 hA hAN hfo6 hvr6 hNk6 hdt6) ?_
  rintro r ⟨σ', h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  refine ⟨σ', ?_, h2, h3, h4, h5, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [nd_bind_one he, nd_bind_one (setAction_eq σ5 _)]; exact h1
  · rcases h6 with h6 | h6
    · exact Or.inl (h6.trans hid5)
    · exact Or.inr (by rw [← schedulable_heap (σ' := σ6) hq5.1 hq5.2.1]; exact h6)
  · rw [h7]; exact hcs5
  · rw [h8]; exact hq5.2.1
  · exact HeapEqUpToFpu.eq_trans (σ2 := σ6) hq5.1 h9
  · exact (TK.tk0 htk5).trans h10
  · exact WritesIn.sfootN_trans (WritesIn.sfootN_of (WritesIn.sfoot_trans hw5 hw6)) h11


theorem cn_enq0F {N T C : Set U64} {c : U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) (hN : NSC N C σ) (hI : Inv σ)
    (hA : ArchSwF st ar N T C c) (hAN : ArchNdF st N T C c) (hfo : FpuOwnOK σ) (hvr : VsRootOK T σ)
    (hNk : ∀ n ∈ N, n.val + 40 ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ n.val)
    (hdt : σ.domainTime ≠ 0 ∨ NdOK (L := L) s σ) {t : U64} (ht : t ∈ T)
    (hsch : Fl4Spec.schedulable t.bv σ = true) :
    (do
      let s5 ← sched.enqueue st s t
      let s6 ← sched.set_action st s5 sched.ACTION_CHOOSE_NEW
      sched.schedule_choose_new_thread st ar s6 a) ⦃ r => ∃ σ', (do
        Fl4Spec.tcbSchedAction (Z := Unit) Fl4Spec.tcbSchedEnqueue t.bv
        Fl4Spec.setSchedulerAction .chooseNewThread
        Fl4Spec.scheduleChooseNewThread) σ =
      ({((), { σ' with schedulerAction := .resumeCurThread })}, False) ∧
      SchedRel st N T C c r.1 σ' ∧ NtfnStateRel N T (L.mem r.1) σ' ∧ NSC N C σ' ∧ Inv σ' ∧
      (σ'.curThread = σ.idleThread ∨ Fl4Spec.schedulable σ'.curThread σ = true) ∧
      σ'.curSc = σ.curSc ∧ σ'.releaseQueue = σ.releaseQueue ∧ HeapEqUpToFpu σ σ' ∧ TK0 σ σ' ∧ P1.WritesIn st s r.1 (SFootN st T c s) ⦄ :=
  cn_refines0F s a σ hS hR hN hI hA hAN hfo hvr hNk hdt ht hsch true

theorem cn_app0F {N T C : Set U64} {c : U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) (hN : NSC N C σ) (hI : Inv σ)
    (hA : ArchSwF st ar N T C c) (hAN : ArchNdF st N T C c) (hfo : FpuOwnOK σ) (hvr : VsRootOK T σ)
    (hNk : ∀ n ∈ N, n.val + 40 ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ n.val)
    (hdt : σ.domainTime ≠ 0 ∨ NdOK (L := L) s σ) {t : U64} (ht : t ∈ T)
    (hsch : Fl4Spec.schedulable t.bv σ = true) :
    (do
      let s5 ← sched.append st s t
      let s6 ← sched.set_action st s5 sched.ACTION_CHOOSE_NEW
      sched.schedule_choose_new_thread st ar s6 a) ⦃ r => ∃ σ', (do
        Fl4Spec.tcbSchedAction (Z := Unit) Fl4Spec.tcbSchedAppend t.bv
        Fl4Spec.setSchedulerAction .chooseNewThread
        Fl4Spec.scheduleChooseNewThread) σ =
      ({((), { σ' with schedulerAction := .resumeCurThread })}, False) ∧
      SchedRel st N T C c r.1 σ' ∧ NtfnStateRel N T (L.mem r.1) σ' ∧ NSC N C σ' ∧ Inv σ' ∧
      (σ'.curThread = σ.idleThread ∨ Fl4Spec.schedulable σ'.curThread σ = true) ∧
      σ'.curSc = σ.curSc ∧ σ'.releaseQueue = σ.releaseQueue ∧ HeapEqUpToFpu σ σ' ∧ TK0 σ σ' ∧ P1.WritesIn st s r.1 (SFootN st T c s) ⦄ :=
  cn_refines0F s a σ hS hR hN hI hA hAN hfo hvr hNk hdt ht hsch false





theorem switch_branch_refines0F {N T C : Set U64} {c : U64} (s : S) (a : A) (σ0 σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) (hN : NSC N C σ) (hI : Inv σ)
    (hA : ArchSwF st ar N T C c) (hAN : ArchNdF st N T C c) (hfo : FpuOwnOK σ) (hvr : VsRootOK T σ)
    (hNk : ∀ n ∈ N, n.val + 40 ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ n.val)
    (hdt : σ.domainTime ≠ 0 ∨ NdOK (L := L) s σ) {t : U64} (ht : t ∈ T)
    (hsch : Fl4Spec.schedulable t.bv σ = true) (wr : Bool)
    (hidle : σ.curThread = σ.idleThread → wr = false)
    (hwhen : Fl4Spec.NonDet.when (wr = true) (Fl4Spec.tcbSchedAction (Z := Unit) Fl4Spec.tcbSchedEnqueue σ.curThread) σ0 =
      ({((), σ)}, False)) :
    (do
      let ct1 ← sched.cur_thread st s
      let t1 ← sched.idle_thread st s
      let b ← obj.Tcb.Insts.CoreCmpPartialEqTcb.eq ct1 t1
      let fastfail ←
        if b
        then ok true
        else
          do
          let i ← obj.Tcb.prio st t s
          let i1 ← obj.Tcb.prio st ct1 s
          if i < i1
          then ok true
          else ok false
      if fastfail
      then
        let i ← sched.cur_domain st s
        let i1 ← obj.Tcb.prio st t s
        let b1 ← sched.is_highest_prio st s i i1
        if b1
        then
          if wr
          then
            let i2 ← obj.Tcb.prio st ct1 s
            if i1 = i2
            then
              let s5 ← sched.append st s t
              let s6 ← sched.set_action st s5 sched.ACTION_CHOOSE_NEW
              sched.schedule_choose_new_thread st ar s6 a
            else sched.switch_to_thread st ar s a t
          else sched.switch_to_thread st ar s a t
        else
          let s5 ← sched.enqueue st s t
          let s6 ← sched.set_action st s5 sched.ACTION_CHOOSE_NEW
          sched.schedule_choose_new_thread st ar s6 a
      else
        if wr
        then
          let i ← obj.Tcb.prio st t s
          let i1 ← obj.Tcb.prio st ct1 s
          if i = i1
          then
            let s5 ← sched.append st s t
            let s6 ← sched.set_action st s5 sched.ACTION_CHOOSE_NEW
            sched.schedule_choose_new_thread st ar s6 a
          else sched.switch_to_thread st ar s a t
        else sched.switch_to_thread st ar s a t) ⦃ r => ∃ σ',
      Fl4Spec.scheduleSwitchThreadBranch (Z := Unit) t.bv σ.curThread wr σ0 =
        ({((), { σ' with schedulerAction := .resumeCurThread })}, False) ∧
      SchedRel st N T C c r.1 σ' ∧ NtfnStateRel N T (L.mem r.1) σ' ∧ NSC N C σ' ∧ Inv σ' ∧
      (σ'.curThread = σ.idleThread ∨ Fl4Spec.schedulable σ'.curThread σ = true) ∧
      σ'.curSc = σ.curSc ∧ σ'.releaseQueue = σ.releaseQueue ∧ HeapEqUpToFpu σ σ' ∧ TK0 σ σ' ∧ P1.WritesIn st s r.1 (SFootN st T c s) ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨xa, hka, -, -, -, hpa⟩ := hs.tcb t ht
  have hct := hc.curT
  obtain ⟨xc, hkc, -, -, -, hpc⟩ := hs.tcb _ hct
  rw [← hs.curThread] at hkc
  -- the spec up to the `if`
  have hsp : ∀ (cp : Fl4Spec.Priority) (X : Fl4Spec.SMonad Unit Unit),
      (σ.curThread ≠ σ.idleThread → cp = xc.tcbPriority) → (σ.curThread = σ.idleThread → cp = 0) →
      ((if decide (σ.curThread ≠ σ.idleThread → xa.tcbPriority < cp) = true ∧
          ¬ (@decide (Fl4Spec.isHighestPrio σ.curDomain xa.tcbPriority σ) (Classical.propDecidable _)) = true then do
          Fl4Spec.tcbSchedAction Fl4Spec.tcbSchedEnqueue t.bv
          Fl4Spec.setSchedulerAction .chooseNewThread
          Fl4Spec.scheduleChooseNewThread
        else if wr = true ∧ cp = xa.tcbPriority then do
          Fl4Spec.tcbSchedAction Fl4Spec.tcbSchedAppend t.bv
          Fl4Spec.setSchedulerAction .chooseNewThread
          Fl4Spec.scheduleChooseNewThread
        else do
          Fl4Spec.guardedSwitchTo t.bv
          Fl4Spec.setSchedulerAction .resumeCurThread) : Fl4Spec.SMonad Unit Unit) σ = X σ →
      Fl4Spec.scheduleSwitchThreadBranch (Z := Unit) t.bv σ.curThread wr σ0 = X σ := by
    intro cp X hcp1 hcp2 hX
    unfold Fl4Spec.scheduleSwitchThreadBranch
    rw [nd_bind_one hwhen, nd_gets_bind, nd_bind_one (threadGet_eq _ hka)]
    by_cases hne : σ.curThread ≠ σ.idleThread
    · rw [if_pos hne, nd_bind_one (threadGet_eq _ hkc), ← hcp1 hne]
      unfold Fl4Spec.scheduleSwitchThreadFastfail
      beta_reduce
      rw [nd_bind_one (show (pure (decide (σ.curThread ≠ σ.idleThread → xa.tcbPriority < cp)) :
        Fl4Spec.SMonad Unit Bool) σ = ({(_, σ)}, False) from rfl), nd_gets_bind, nd_gets_bind]
      exact hX
    · rw [if_neg hne, nd_bind_one (show (pure 0 : Fl4Spec.SMonad Unit Fl4Spec.Priority) σ = ({(0, σ)}, False) from rfl),
        ← hcp2 (not_not.1 hne)]
      unfold Fl4Spec.scheduleSwitchThreadFastfail
      beta_reduce
      rw [nd_bind_one (show (pure (decide (σ.curThread ≠ σ.idleThread → xa.tcbPriority < cp)) :
        Fl4Spec.SMonad Unit Bool) σ = ({(_, σ)}, False) from rfl), nd_gets_bind, nd_gets_bind]
      exact hX
  have hp : (L.mem s (prioA t)).val < 256 := hc.prio t ht
  have hpa' : specPrio (L.mem s (prioA t)) = xa.tcbPriority := specPrio_eq hpa
  have post : ∀ (cp : Fl4Spec.Priority) (X : Fl4Spec.SMonad Unit Unit),
      (σ.curThread ≠ σ.idleThread → cp = xc.tcbPriority) → (σ.curThread = σ.idleThread → cp = 0) →
      ((if decide (σ.curThread ≠ σ.idleThread → xa.tcbPriority < cp) = true ∧
          ¬ (@decide (Fl4Spec.isHighestPrio σ.curDomain xa.tcbPriority σ) (Classical.propDecidable _)) = true then do
          Fl4Spec.tcbSchedAction Fl4Spec.tcbSchedEnqueue t.bv
          Fl4Spec.setSchedulerAction .chooseNewThread
          Fl4Spec.scheduleChooseNewThread
        else if wr = true ∧ cp = xa.tcbPriority then do
          Fl4Spec.tcbSchedAction Fl4Spec.tcbSchedAppend t.bv
          Fl4Spec.setSchedulerAction .chooseNewThread
          Fl4Spec.scheduleChooseNewThread
        else do
          Fl4Spec.guardedSwitchTo t.bv
          Fl4Spec.setSchedulerAction .resumeCurThread) : Fl4Spec.SMonad Unit Unit) σ = X σ →
      ∀ r : S × A, (∃ σ', X σ = ({((), { σ' with schedulerAction := .resumeCurThread })}, False) ∧
        SchedRel st N T C c r.1 σ' ∧ NtfnStateRel N T (L.mem r.1) σ' ∧ NSC N C σ' ∧ Inv σ' ∧
        (σ'.curThread = σ.idleThread ∨ Fl4Spec.schedulable σ'.curThread σ = true) ∧
        σ'.curSc = σ.curSc ∧ σ'.releaseQueue = σ.releaseQueue ∧ HeapEqUpToFpu σ σ' ∧ TK0 σ σ' ∧ P1.WritesIn st s r.1 (SFootN st T c s)) →
      ∃ σ', Fl4Spec.scheduleSwitchThreadBranch (Z := Unit) t.bv σ.curThread wr σ0 =
        ({((), { σ' with schedulerAction := .resumeCurThread })}, False) ∧
        SchedRel st N T C c r.1 σ' ∧ NtfnStateRel N T (L.mem r.1) σ' ∧ NSC N C σ' ∧ Inv σ' ∧
        (σ'.curThread = σ.idleThread ∨ Fl4Spec.schedulable σ'.curThread σ = true) ∧
        σ'.curSc = σ.curSc ∧ σ'.releaseQueue = σ.releaseQueue ∧ HeapEqUpToFpu σ σ' ∧ TK0 σ σ' ∧ P1.WritesIn st s r.1 (SFootN st T c s) := by
    intro cp X h1 h2 hX r ⟨σ', e, rest⟩
    exact ⟨σ', (hsp cp X h1 h2 hX).trans e, rest⟩
  have SW := fun cp h1 h2 hX => WP.spec_mono (WP.spec_mono (sw_refinesF s a σ hS hR hN hI hA hfo hvr ht hsch)
    fun r ⟨σ', g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11⟩ =>
      ⟨σ', g1, g2, g3, g4, g5, g6, g7, g8, g9, TK.tk0 g10, WritesIn.sfootN_of g11⟩) (post cp _ h1 h2 hX)
  have CE := fun cp h1 h2 hX => WP.spec_mono (cn_enq0F s a σ hS hR hN hI hA hAN hfo hvr hNk hdt ht hsch)
    (post cp _ h1 h2 hX)
  have CA := fun cp h1 h2 hX => WP.spec_mono (cn_app0F s a σ hS hR hN hI hA hAN hfo hvr hNk hdt ht hsch)
    (post cp _ h1 h2 hX)
  step with sched.cur_thread.spec' as ⟨ct1, hct1⟩
  rw [hc.cur] at hct1
  subst hct1
  step with sched.idle_thread.spec2 as ⟨t1, ht1⟩
  rw [hc.cur] at ht1
  subst ht1
  unfold obj.Tcb.Insts.CoreCmpPartialEqTcb.eq
  simp only [bind_ok]
  by_cases hci : nodeW st s c layout.node.CUR_THREAD = nodeW st s c layout.node.IDLE_THREAD
  · have hcid : σ.curThread = σ.idleThread := by rw [hs.curThread, hs.idleTh, hci]
    have hwr := hidle hcid
    subst hwr
    simp only [hci, decide_true, ↓reduceIte, bind_ok]
    step with sched.cur_domain.spec' as ⟨i, hi⟩
    step with obj.Tcb.prio.spec as ⟨i1, hi1⟩
    subst hi hi1
    refine WP.spec_bind (is_highest_prio_refines s σ hS _ hp) ?_
    intro b1 hb1
    rw [hpa'] at hb1
    by_cases hb : b1 = true
    · simp only [hb, ↓reduceIte, Bool.false_eq_true]
      refine SW 0 (fun h => absurd hcid h) (fun _ => rfl) ?_
      rw [if_neg (by rw [← hb1, hb]; simp), if_neg (by simp)]
    · have hb' : b1 = false := by simpa using hb
      simp only [hb', Bool.false_eq_true, ↓reduceIte]
      refine CE 0 (fun h => absurd hcid h) (fun _ => rfl) ?_
      rw [if_pos ⟨by simp [hcid], by rw [← hb1, hb']; simp⟩]
  · have hcid : σ.curThread ≠ σ.idleThread := by
      rw [hs.curThread, hs.idleTh]; exact bv_ne hci
    simp only [hci, decide_false, Bool.false_eq_true, ↓reduceIte]
    have hpc' : (L.mem s (prioA (nodeW st s c layout.node.CUR_THREAD))).val = xc.tcbPriority.toNat := hpc
    step with obj.Tcb.prio.spec as ⟨i, hi⟩
    step with obj.Tcb.prio.spec as ⟨i1, hi1⟩
    subst hi hi1
    have hcp1 : σ.curThread ≠ σ.idleThread → xc.tcbPriority = xc.tcbPriority := fun _ => rfl
    have hcp2 : σ.curThread = σ.idleThread → xc.tcbPriority = 0 := fun h => absurd h hcid
    have heq : (L.mem s (prioA t) = L.mem s (prioA (nodeW st s c layout.node.CUR_THREAD))) ↔
        xc.tcbPriority = xa.tcbPriority := (prio_eq_iff hpa hpc').trans eq_comm
    by_cases hlt : L.mem s (prioA t) < L.mem s (prioA (nodeW st s c layout.node.CUR_THREAD))
    · have hlt' : xa.tcbPriority < xc.tcbPriority := (prio_lt_iff hpa hpc').1 hlt
      simp only [hlt, ↓reduceIte, bind_ok]
      step with sched.cur_domain.spec' as ⟨i, hi⟩
      step with obj.Tcb.prio.spec as ⟨i1, hi1⟩
      subst hi hi1
      refine WP.spec_bind (is_highest_prio_refines s σ hS _ hp) ?_
      intro b1 hb1
      rw [hpa'] at hb1
      by_cases hb : b1 = true
      · simp only [hb, ↓reduceIte]
        have hc1 : ¬ (decide (σ.curThread ≠ σ.idleThread → xa.tcbPriority < xc.tcbPriority) = true ∧
            ¬ (@decide (Fl4Spec.isHighestPrio σ.curDomain xa.tcbPriority σ) (Classical.propDecidable _)) = true) := by
          rw [← hb1, hb]; simp
        cases wr
        · simp only [Bool.false_eq_true, ↓reduceIte]
          exact SW _ hcp1 hcp2 (by rw [if_neg hc1, if_neg (by simp)])
        · simp only [↓reduceIte]
          step with obj.Tcb.prio.spec as ⟨i2, hi2⟩
          subst hi2
          by_cases he : L.mem s (prioA t) = L.mem s (prioA (nodeW st s c layout.node.CUR_THREAD))
          · simp only [he, ↓reduceIte]
            exact CA _ hcp1 hcp2 (by rw [if_neg hc1, if_pos ⟨rfl, heq.1 he⟩])
          · simp only [he, ↓reduceIte]
            exact SW _ hcp1 hcp2 (by rw [if_neg hc1, if_neg (fun h => he (heq.2 h.2))])
      · have hb' : b1 = false := by simpa using hb
        simp only [hb', Bool.false_eq_true, ↓reduceIte]
        exact CE _ hcp1 hcp2 (by rw [if_pos ⟨by simp [hcid, hlt'], by rw [← hb1, hb']; simp⟩])
    · have hc1 : ¬ (decide (σ.curThread ≠ σ.idleThread → xa.tcbPriority < xc.tcbPriority) = true ∧
          ¬ (@decide (Fl4Spec.isHighestPrio σ.curDomain xa.tcbPriority σ) (Classical.propDecidable _)) = true) :=
        fun h => hlt ((prio_lt_iff hpa hpc').2 (by simpa [hcid] using h.1))
      simp only [hlt, Bool.false_eq_true, ↓reduceIte, bind_ok]
      cases wr
      · simp only [Bool.false_eq_true, ↓reduceIte]
        exact SW _ hcp1 hcp2 (by rw [if_neg hc1, if_neg (by simp)])
      · simp only [↓reduceIte]
        step with obj.Tcb.prio.spec as ⟨i, hi⟩
        step with obj.Tcb.prio.spec as ⟨i1, hi1⟩
        subst hi hi1
        by_cases he : L.mem s (prioA t) = L.mem s (prioA (nodeW st s c layout.node.CUR_THREAD))
        · simp only [he, ↓reduceIte]
          exact CA _ hcp1 hcp2 (by rw [if_neg hc1, if_pos ⟨rfl, heq.1 he⟩])
        · simp only [he, ↓reduceIte]
          exact SW _ hcp1 hcp2 (by rw [if_neg hc1, if_neg (fun h => he (heq.2 h.2))])



end

end

end Fl4Proofs.P3.Sched
