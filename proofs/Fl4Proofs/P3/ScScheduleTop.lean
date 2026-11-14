/-
P3 (DESIGN.md §9), scheduler: **`schedule` refines l4v `schedule`**
(`schedule_refines`), ending in `Inv` and `CurInv`.

* `is_highest_prio_refines`: the bitmap test against l4v `is_highest_prio`.
* `schedule_choose_new_thread_refines`: in the domain scope (domain time
  nonzero, so no `next_domain`), `choose_thread`.
* `sw_refines`, `cn_refines`: the switch-thread branch's outcomes, a direct
  `guarded_switch_to` of the (schedulable) candidate, or queueing it
  (enqueue or append) and choosing a new thread.
* `switch_branch_refines`: the switch-thread branch (l4v
  `schedule_switch_thread_branch`): the fast-fail test (idle current thread,
  or a lower candidate priority), `is_highest_prio`, the equal-priority
  append; the idle thread is not schedulable (`IdleOK`).
* `tail_refines`: `resume_cur_thread`, then `sc_and_timer`
  (`switch_sched_context_cur`; timer programming is the hypothesis
  `SniHyp`), then FL4's SMP IPIs (`SendHyp`).
* `schedule_refines`: FL4's `schedule` runs its TCB timers first
  (`timer::fire`, l4h 0003, the hypothesis `FireHyp`: a sequence of
  notification signals, `Fires`); l4v's `schedule` runs from the state after
  them.
-/
import Fl4Proofs.P3.ScAwaken
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section Spec
open Fl4Spec

theorem OffOK.of_eq {σ σ' : State Unit} (h : OffOK σ) (hk : σ'.kheap = σ.kheap) (hcs : σ'.curSc = σ.curSc)
    (hcn : σ'.consumedTime = σ.consumedTime) (htm : σ'.curTime = σ.curTime) : OffOK σ' := by
  intro h0 y n hy
  rw [hcn] at h0 ⊢; rw [htm]; rw [hk, hcs] at hy
  exact h h0 y n hy

/-- The new current thread after `schedule`'s branch: the idle thread, a
schedulable thread, or the current one. -/
theorem newcur_of {σ σ' : State Unit} (h : σ'.curThread = σ.idleThread ∨ schedulable σ'.curThread σ = true ∨
      σ'.curThread = σ.curThread)
    (hk : σ'.kheap = σ.kheap) (hr : σ'.releaseQueue = σ.releaseQueue) (hId : IdleOK σ) (hC : CurInv σ) :
    ∃ xt scp, σ'.kheap σ'.curThread = some (.tcb xt) ∧ xt.tcbSchedContext = some scp ∧
      (∀ q, xt.tcbState ≠ .blockedOnNotification q) ∧ σ'.curThread ∉ σ'.releaseQueue ∧
      (scp ≠ idleScPtr → ∀ x n, σ'.kheap scp = some (.schedContext x n) → scActive x = true) := by
  rw [hk, hr]
  rcases h with h | h | h
  · rw [h]
    obtain ⟨x, h1, h2, h3, h4⟩ := hId
    refine ⟨x, idleScPtr, h1, h2, ?_, h4, fun hne => absurd rfl hne⟩
    intro q e; rw [h3] at e; cases e
  · obtain ⟨x, scp, y, n, h1, h2, h3, h4, h5, h6⟩ := schedulable_inv h
    refine ⟨x, scp, h1, h2, ?_, h6, fun _ x' n' hx => ?_⟩
    · intro q e; rw [e] at h3; cases h3
    · rw [h4] at hx; cases hx; exact h5
  · rw [h]
    obtain ⟨xt, hkt, hxs, hnb⟩ := hC.tcb
    exact ⟨xt, σ.curSc, hkt, hxs, hnb, hC.notRel, fun hne x n hx => hC.active hne x n hx⟩

end Spec

section Spec
open Fl4Spec

/-- l4v `schedule` after `awaken` and `check_domain_time` (one domain). -/
theorem schedule_unfold {σ1 σ2 : State Unit} (haw : awaken (Z := Unit) σ1 = ({((), σ2)}, False))
    (hnd : numDomains = 1) :
    schedule (Z := Unit) σ1 = (match σ2.schedulerAction with
      | .resumeCurThread => scAndTimer
      | .chooseNewThread => do
          NonDet.when (schedulable σ2.curThread σ2 = true) (tcbSchedAction tcbSchedEnqueue σ2.curThread)
          scheduleChooseNewThread
          scAndTimer
      | .switchThread candidate => do
          scheduleSwitchThreadBranch candidate σ2.curThread (schedulable σ2.curThread σ2)
          scAndTimer) σ2 := by
  unfold schedule
  rw [nd_bind_one haw, nd_bind_one (checkDomainTime_eq hnd σ2), nd_gets_bind, nd_gets_bind, nd_gets_bind]
  cases σ2.schedulerAction <;> rfl

theorem resume_self {σ : State Unit} (h : σ.schedulerAction = .resumeCurThread) :
    ({ σ with schedulerAction := .resumeCurThread } : State Unit) = σ := by
  rw [← h]

end Spec

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]

/-- **`is_highest_prio` refines l4v `is_highest_prio`** (one domain: the
bitmap's L1 word is 0 iff no thread is ready; otherwise `highest_prio` is
the greatest non-empty priority). -/
theorem is_highest_prio_refines {N T C : Set U64} {c : U64} (s : S) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) (p : U64) (hp : p.val < 256) :
    sched.is_highest_prio st s (L.mem s (curDomA st s)) p ⦃ b =>
      b = @decide (Fl4Spec.isHighestPrio σ.curDomain (specPrio p) σ) (Classical.propDecidable _) ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  rw [hs.curDom.2]
  unfold sched.is_highest_prio sched.bitmap_dom
  rw [num_domains_eq, if_neg (by decide)]
  simp only [bind_ok]
  step with LawfulStore.cur_cpu_spec as ⟨cpu, hcpu⟩
  rw [hc.cur] at hcpu
  subst cpu
  unfold sched.l1_off
  simp only [bind_ok, lift]
  step with obj.node_get.spec as ⟨l1, hl1⟩
  have hl1' : l1 = L.l1W s c := by
    rw [hl1]; unfold LawfulStore.l1W; congr 2
    unfold layout.node.L1_BITMAP l1Off w64; rfl
  subst hl1'
  split
  · rename_i he
    rw [WP.spec_ok]
    exact (@decide_eq_true _ (Classical.propDecidable _) (Or.inl ((choose_empty hS).1 he))).symm
  · rename_i hne
    have hN' : NodePlaced st T s (L.cpu s) := by rw [hc.cur]; exact hc.node
    have hB : BitmapOK st s (L.cpu s) (fun p => Q p ≠ []) := by rw [hc.cur]; exact hc.ready.2
    refine WP.spec_bind (sched.highest_prio.spec s 0#u64 _ hN' hB (by rw [hc.cur]; exact hne)) ?_
    rintro p' ⟨hp', hpne, hmax⟩
    rw [WP.spec_ok]
    have hnall : ¬ ∀ prio, σ.readyQueues σ.curDomain prio = [] := fun h => hne ((choose_empty hS).2 h)
    have hmx : Fl4Spec.setMax {prio | σ.readyQueues σ.curDomain prio ≠ []} = specPrio p' := by
      rw [hs.curDom.1]
      refine setMax_eq (by show σ.readyQueues 0 (specPrio p') ≠ []; rw [hs.rq p' hp']; simpa using hpne) ?_
      intro x hx
      obtain ⟨q, hq, rfl⟩ := prio_of_spec x
      have hne' : Q q ≠ [] := by
        intro e; apply hx; show σ.readyQueues 0 (specPrio q) = []; rw [hs.rq q hq, e]; rfl
      exact (specPrio_le hq hp').2 (hmax q hq hne')
    refine decide_eq_decide.2 ⟨fun h => Or.inr ?_, fun h => ?_⟩
    · show Fl4Spec.setMax _ ≤ specPrio p
      rw [hmx]; exact (specPrio_le hp' hp).2 (by scalar_tac)
    · rcases h with h | h
      · exact absurd h hnall
      · have h2 : Fl4Spec.setMax _ ≤ specPrio p := h
        rw [hmx] at h2
        have := (specPrio_le hp' hp).1 h2
        scalar_tac

theorem sched.domain_time.spec2 (s : S) : sched.domain_time st s ⦃ v => v = L.mem s (dtA st s) ⦄ := by
  unfold sched.domain_time
  refine WP.spec_mono (obj.ks_get.spec s _) fun v hv => ?_
  rw [hv]; unfold dtA layout.ks.DOMAIN_TIME; rfl

/-- **`schedule_choose_new_thread` refines l4v's**, in the domain scope
(domain time nonzero: the domain does not end), up to the final
`set_scheduler_action resume_cur_thread`, which FL4 does in `schedule`. -/
theorem schedule_choose_new_thread_refines {N T C : Set U64} {c : U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) (hN : NSC N C σ) (hI : Inv σ)
    (hvm : ∀ t ∈ T, vspace.set_vm_root st ar s a t ⦃ r => ∃ σ1, Fl4Spec.archSwitchToThread (Z := Unit) t.bv σ =
      ({((), σ1)}, False) ∧ SchedRel st N T C c r.1 σ1 ∧ NtfnStateRel N T (L.mem r.1) σ1 ∧ ArchKeeps σ σ1 ⦄)
    (hvmi : vspace.set_kernel_vm_root st ar s a ⦃ r => ∃ σ1, Fl4Spec.archSwitchToIdleThread (Z := Unit) σ =
      ({((), σ1)}, False) ∧ SchedRel st N T C c r.1 σ1 ∧ NtfnStateRel N T (L.mem r.1) σ1 ∧ ArchKeeps σ σ1 ⦄)
    (hdt : σ.domainTime ≠ 0) :
    sched.schedule_choose_new_thread st ar s a ⦃ r => ∃ σ', Fl4Spec.scheduleChooseNewThread (Z := Unit) σ =
      ({((), { σ' with schedulerAction := .resumeCurThread })}, False) ∧
      SchedRel st N T C c r.1 σ' ∧ NtfnStateRel N T (L.mem r.1) σ' ∧ NSC N C σ' ∧ Inv σ' ∧
      (σ'.curThread = σ.idleThread ∨ Fl4Spec.schedulable σ'.curThread σ = true) ∧
      σ'.curSc = σ.curSc ∧ σ'.releaseQueue = σ.releaseQueue ∧ σ'.kheap = σ.kheap ∧ TK σ σ' ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  unfold sched.schedule_choose_new_thread
  step with sched.domain_time.spec2 as ⟨i, hi⟩
  have hi0 : i ≠ 0#u64 := by
    intro e; apply hdt; rw [hs.domTime, ← hi, e]; rfl
  simp only [hi0, ↓reduceIte, bind_ok]
  refine WP.spec_mono (choose_thread_refines s a σ hS hR hN hI hvm hvmi (by rw [← hs.idleTh])) ?_
  rintro r ⟨σ', h1, h2, h3, h4, h5, h6, h7, h8, h9, -, h11⟩
  refine ⟨σ', ?_, h2, h3, h4, h5, h6, h7, h8, h9, h11⟩
  unfold Fl4Spec.scheduleChooseNewThread
  rw [nd_gets_bind]
  unfold Fl4Spec.NonDet.when
  rw [if_neg hdt, nd_bind_one (show Fl4Spec.NonDet.pure (σ := Fl4Spec.State Unit) () σ = ({((), σ)}, False) from rfl),
    nd_bind_one h1]
  rfl

/-- The arch hypotheses of a thread switch, at every related state:
`set_vm_root` refines `arch_switch_to_thread`, `set_kernel_vm_root` refines
`arch_switch_to_idle_thread`, both keeping `ArchKeeps`. -/
def ArchSw (st : machine.Store S) [L : LawfulStore st] (ar : machine.Arch A) (N T C : Set U64) (c : U64) : Prop :=
  (∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), SchedRel st N T C c s σ → NtfnStateRel N T (L.mem s) σ →
    ∀ t ∈ T, vspace.set_vm_root st ar s a t ⦃ r => ∃ σ1, Fl4Spec.archSwitchToThread (Z := Unit) t.bv σ =
      ({((), σ1)}, False) ∧ SchedRel st N T C c r.1 σ1 ∧ NtfnStateRel N T (L.mem r.1) σ1 ∧ ArchKeeps σ σ1 ⦄) ∧
  (∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), SchedRel st N T C c s σ → NtfnStateRel N T (L.mem s) σ →
    vspace.set_kernel_vm_root st ar s a ⦃ r => ∃ σ1, Fl4Spec.archSwitchToIdleThread (Z := Unit) σ =
      ({((), σ1)}, False) ∧ SchedRel st N T C c r.1 σ1 ∧ NtfnStateRel N T (L.mem r.1) σ1 ∧ ArchKeeps σ σ1 ⦄)

/-- The switch-thread branch's direct switch: `guarded_switch_to` of a
schedulable thread, then `resume_cur_thread`. -/
theorem sw_refines {N T C : Set U64} {c : U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) (hN : NSC N C σ) (hI : Inv σ)
    (hA : ArchSw st ar N T C c) {t : U64} (ht : t ∈ T) (hsch : Fl4Spec.schedulable t.bv σ = true) :
    sched.switch_to_thread st ar s a t ⦃ r => ∃ σ', (do
        Fl4Spec.guardedSwitchTo (Z := Unit) t.bv
        Fl4Spec.setSchedulerAction .resumeCurThread) σ =
      ({((), { σ' with schedulerAction := .resumeCurThread })}, False) ∧
      SchedRel st N T C c r.1 σ' ∧ NtfnStateRel N T (L.mem r.1) σ' ∧ NSC N C σ' ∧ Inv σ' ∧
      (σ'.curThread = σ.idleThread ∨ Fl4Spec.schedulable σ'.curThread σ = true) ∧
      σ'.curSc = σ.curSc ∧ σ'.releaseQueue = σ.releaseQueue ∧ σ'.kheap = σ.kheap ∧ TK σ σ' ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨x, hk, hd, -, -, -⟩ := hs.tcb t ht
  obtain ⟨x', scp, -, -, hk', hsc, -⟩ := schedulable_inv hsch
  rw [hk] at hk'; cases hk'
  refine WP.spec_mono (switch_to_thread_refines s a σ hS hR hN ht (hA.1 s a σ hS hR t ht)) ?_
  rintro r ⟨σ', h1, h2, h3, h4, h5, h6, h7, h8, h9, -, h11⟩
  refine ⟨σ', ?_, h2, h3, h4, h5 hI, Or.inr (by rw [h6]; exact hsch), h7, h8, h9, h11⟩
  rw [nd_bind_one (by rw [guardedSwitchTo_eq hk hsc hsch (by rw [hd, hs.curDom.1])]; exact h1)]
  rfl

/-- The switch-thread branch's queue-then-choose path: the candidate is
enqueued (`enq`) or appended, the action becomes `choose_new_thread`, and a
new thread is chosen. -/
theorem cn_refines {N T C : Set U64} {c : U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) (hN : NSC N C σ) (hI : Inv σ)
    (hA : ArchSw st ar N T C c) (hdt : σ.domainTime ≠ 0) {t : U64} (ht : t ∈ T)
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
      σ'.curSc = σ.curSc ∧ σ'.releaseQueue = σ.releaseQueue ∧ σ'.kheap = σ.kheap ∧ TK σ σ' ⦄ := by
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
        FootEq N T (L.mem s) (L.mem s5) ∧ SchedRel st N T C c s5 σ5 ⦄ := by
    cases enq
    · refine WP.spec_mono (append_refines s σ hS t ht (fun _ => hrel0)) ?_
      rintro s5 ⟨σ5, he, -, -, hf, hS5⟩
      have e := pair_eq (he.symm.trans (tcbSchedAction_gen hk _))
      refine ⟨σ5, he, ?_, ?_, hf, hS5⟩ <;> rw [← e]
      · exact qchange_append hk hsch
      · exact ⟨rfl, ⟨rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl⟩
    · refine WP.spec_mono (enqueue_refines s σ hS t ht (fun _ => hrel0)) ?_
      rintro s5 ⟨σ5, he, -, -, hf, hS5⟩
      have e := pair_eq (he.symm.trans (tcbSchedAction_gen hk _))
      refine ⟨σ5, he, ?_, ?_, hf, hS5⟩ <;> rw [← e]
      · exact qchange_enqueue hk hsch
      · exact ⟨rfl, ⟨rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl⟩
  refine WP.spec_bind hq ?_
  rintro s5 ⟨σ5, he, hq5, ⟨-, htk5, hcs5, hid5⟩, hf5, hS5⟩
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
  have hdt6 : σ6.domainTime ≠ 0 := by show σ5.domainTime ≠ 0; rw [htk5.2.2.2.2]; exact hdt
  refine WP.spec_mono (schedule_choose_new_thread_refines _ a σ6 hS6 hR6 hN6 hI6 (hA.1 _ a σ6 hS6 hR6)
    (hA.2 _ a σ6 hS6 hR6) hdt6) ?_
  rintro r ⟨σ', h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  refine ⟨σ', ?_, h2, h3, h4, h5, ?_, ?_, ?_, ?_, ?_⟩
  · rw [nd_bind_one he, nd_bind_one (setAction_eq σ5 _)]; exact h1
  · rcases h6 with h6 | h6
    · exact Or.inl (h6.trans hid5)
    · exact Or.inr (by rw [← schedulable_heap (σ' := σ6) hq5.1 hq5.2.1]; exact h6)
  · rw [h7]; exact hcs5
  · rw [h8]; exact hq5.2.1
  · rw [h9]; exact hq5.1
  · exact ⟨h10.1.trans htk5.1, h10.2.1.trans htk5.2.1, h10.2.2.1.trans htk5.2.2.1, h10.2.2.2.1.trans htk5.2.2.2.1,
      h10.2.2.2.2.trans htk5.2.2.2.2⟩

theorem cn_enq {N T C : Set U64} {c : U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) (hN : NSC N C σ) (hI : Inv σ)
    (hA : ArchSw st ar N T C c) (hdt : σ.domainTime ≠ 0) {t : U64} (ht : t ∈ T)
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
      σ'.curSc = σ.curSc ∧ σ'.releaseQueue = σ.releaseQueue ∧ σ'.kheap = σ.kheap ∧ TK σ σ' ⦄ :=
  cn_refines s a σ hS hR hN hI hA hdt ht hsch true

theorem cn_app {N T C : Set U64} {c : U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) (hN : NSC N C σ) (hI : Inv σ)
    (hA : ArchSw st ar N T C c) (hdt : σ.domainTime ≠ 0) {t : U64} (ht : t ∈ T)
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
      σ'.curSc = σ.curSc ∧ σ'.releaseQueue = σ.releaseQueue ∧ σ'.kheap = σ.kheap ∧ TK σ σ' ⦄ :=
  cn_refines s a σ hS hR hN hI hA hdt ht hsch false

theorem prio_lt_iff {p q : U64} {x y : Fl4Spec.Tcb} (hp : p.val = x.tcbPriority.toNat) (hq : q.val = y.tcbPriority.toNat) :
    p < q ↔ x.tcbPriority < y.tcbPriority := by
  rw [BitVec.lt_def, ← hp, ← hq]; exact Iff.rfl

theorem prio_eq_iff {p q : U64} {x y : Fl4Spec.Tcb} (hp : p.val = x.tcbPriority.toNat) (hq : q.val = y.tcbPriority.toNat) :
    p = q ↔ x.tcbPriority = y.tcbPriority := by
  constructor
  · intro e; apply BitVec.eq_of_toNat_eq; rw [← hp, ← hq, e]
  · intro e; apply UScalar.eq_of_val_eq; rw [hp, hq, e]

/-- **The switch-thread branch** (l4v `schedule_switch_thread_branch` after
its first line, the enqueue of the current thread when schedulable): the
candidate `t` (schedulable) is switched to, or queued and a new thread
chosen. The fast-fail test and the bitmap's `is_highest_prio` agree with
the spec's; the idle thread is not schedulable (`IdleOK`). -/
theorem switch_branch_refines {N T C : Set U64} {c : U64} (s : S) (a : A) (σ0 σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) (hN : NSC N C σ) (hI : Inv σ)
    (hA : ArchSw st ar N T C c) (hdt : σ.domainTime ≠ 0) {t : U64} (ht : t ∈ T)
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
      σ'.curSc = σ.curSc ∧ σ'.releaseQueue = σ.releaseQueue ∧ σ'.kheap = σ.kheap ∧ TK σ σ' ⦄ := by
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
        σ'.curSc = σ.curSc ∧ σ'.releaseQueue = σ.releaseQueue ∧ σ'.kheap = σ.kheap ∧ TK σ σ') →
      ∃ σ', Fl4Spec.scheduleSwitchThreadBranch (Z := Unit) t.bv σ.curThread wr σ0 =
        ({((), { σ' with schedulerAction := .resumeCurThread })}, False) ∧
        SchedRel st N T C c r.1 σ' ∧ NtfnStateRel N T (L.mem r.1) σ' ∧ NSC N C σ' ∧ Inv σ' ∧
        (σ'.curThread = σ.idleThread ∨ Fl4Spec.schedulable σ'.curThread σ = true) ∧
        σ'.curSc = σ.curSc ∧ σ'.releaseQueue = σ.releaseQueue ∧ σ'.kheap = σ.kheap ∧ TK σ σ' := by
    intro cp X h1 h2 hX r ⟨σ', e, rest⟩
    exact ⟨σ', (hsp cp X h1 h2 hX).trans e, rest⟩
  have SW := fun cp h1 h2 hX => WP.spec_mono (sw_refines s a σ hS hR hN hI hA ht hsch)
    (post cp _ h1 h2 hX)
  have CE := fun cp h1 h2 hX => WP.spec_mono (cn_enq s a σ hS hR hN hI hA hdt ht hsch)
    (post cp _ h1 h2 hX)
  have CA := fun cp h1 h2 hX => WP.spec_mono (cn_app s a σ hS hR hN hI hA hdt ht hsch)
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

/-- The arch hypothesis on `set_next_interrupt` (programming the timer) at
every related state. -/
def SniHyp (st : machine.Store S) [L : LawfulStore st] (ar : machine.Arch A) (N T C : Set U64) (c : U64) : Prop :=
  ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), SchedRel st N T C c s σ → NtfnStateRel N T (L.mem s) σ →
    sched.set_next_interrupt st ar s a ⦃ r => ∃ σ1, Fl4Spec.setNextInterrupt (Z := Unit) σ = ({((), σ1)}, False) ∧
      SchedRel st N T C c r.1 σ1 ∧ NtfnStateRel N T (L.mem r.1) σ1 ∧ ArchKeeps σ σ1 ⦄

/-- The SMP hypothesis on `send_pending` (the remote reschedule IPIs, not in
the single-core spec) at every related state. -/
def SendHyp (st : machine.Store S) [L : LawfulStore st] (ar : machine.Arch A) (N T C : Set U64) (c : U64) : Prop :=
  ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), SchedRel st N T C c s σ → NtfnStateRel N T (L.mem s) σ →
    smp.send_pending st ar s a ⦃ r => SchedRel st N T C c r.1 σ ∧ NtfnStateRel N T (L.mem r.1) σ ⦄

/-- **`schedule`'s tail**: the action becomes `resume_cur_thread`, then
`sc_and_timer` (`switch_sched_context`, and the timer when it is to be
reprogrammed). The new current thread is bound to an SC (active unless the
idle SC), not released and not blocked on a notification; the outgoing SC
is one of `C`, bound to `u0` and back. It ends in `Inv` and `CurInv`. -/
theorem tail_refines {N T C : Set U64} {c : U64} (s3 : S) (a2 : A) (σ3 : Fl4Spec.State Unit)
    (hS3 : SchedRel st N T C c s3 σ3) (hR3 : NtfnStateRel N T (L.mem s3) σ3) (hN3 : NSC N C σ3) (hI3 : Inv σ3)
    (hnew : ∃ xt scp, σ3.kheap σ3.curThread = some (.tcb xt) ∧ xt.tcbSchedContext = some scp ∧
      (∀ q, xt.tcbState ≠ .blockedOnNotification q) ∧ σ3.curThread ∉ σ3.releaseQueue ∧
      (scp ≠ Fl4Spec.idleScPtr → ∀ x n, σ3.kheap scp = some (.schedContext x n) → Fl4Spec.scActive x = true))
    (hcsc : ∃ sc ∈ C, sc.bv = σ3.curSc)
    {u0 : Fl4Spec.ObjRef} (hown0 : ∀ x n, σ3.kheap σ3.curSc = some (.schedContext x n) → x.scTcb = some u0)
    (hback : ∀ xt, σ3.kheap u0 = some (.tcb xt) → xt.tcbSchedContext = some σ3.curSc)
    (hnr : u0 ∉ σ3.releaseQueue) (hoff : OffOK σ3)
    (hmrt : ∀ a, sporadic.max_release_time ar a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : ∀ a, sporadic.min_budget ar a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hsni : SniHyp st ar N T C c) (hsend : SendHyp st ar N T C c) :
    (do
      let s4 ← sched.set_action st s3 sched.ACTION_RESUME_CURRENT
      let (s5, a3) ← sched.switch_sched_context st ar s4 a2
      let c ← st.cur_cpu s5
      let i ← obj.node_get st s5 c layout.node.REPROGRAM
      let (s6, a4) ←
        if i != 0#u64
        then
          do
          let (s7, a5) ← sched.set_next_interrupt st ar s5 a3
          let s8 ← obj.node_set st s7 c layout.node.REPROGRAM 0#u64
          ok (s8, a5)
        else ok (s5, a3)
      smp.send_pending st ar s6 a4) ⦃ r => ∃ σ',
      Fl4Spec.scAndTimer (Z := Unit) { σ3 with schedulerAction := .resumeCurThread } = ({((), σ')}, False) ∧
      SchedRel st N T C c r.1 σ' ∧ NtfnStateRel N T (L.mem r.1) σ' ∧ NSC N C σ' ∧ Inv σ' ∧ CurInv σ' ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS3.lists
  step with sched.set_action.spec' as ⟨s4, hs4⟩
  subst hs4
  rw [hc.cur, resume_val']
  set σ4 : Fl4Spec.State Unit := { σ3 with schedulerAction := .resumeCurThread } with hσ4
  have hS4 : SchedRel st N T C c (L.wr s3 (L.nodeAt s3 c layout.node.SCHED_ACTION) 0#u64) σ4 :=
    hS3.set_action (Or.inl rfl) rfl
  have hf4 : FootEq N T (L.mem s3) (L.mem (L.wr s3 (L.nodeAt s3 c layout.node.SCHED_ACTION) 0#u64)) :=
    node_wr_foot hS3 (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION])
  have hR4 : NtfnStateRel N T (L.mem (L.wr s3 (L.nodeAt s3 c layout.node.SCHED_ACTION) 0#u64)) σ4 :=
    hR3.frame hS3.placed hf4 (KView.of_kheap rfl)
  have hN4 : NSC N C σ4 := hN3
  have hI4 : Inv σ4 := hI3.congr rfl rfl rfl rfl
  set s4 := L.wr s3 (L.nodeAt s3 c layout.node.SCHED_ACTION) 0#u64
  obtain ⟨Q4, R4, hc4, hs4⟩ := hS4.lists
  obtain ⟨xt, scp, hkt, hsct, hnbt, hntr, hactt⟩ := hnew
  have hct4 := hc4.curT
  obtain ⟨xt', hkt', -, -, hsct', -⟩ := hs4.tcb _ hct4
  have e1 : σ3.curThread = (nodeW st s4 c layout.node.CUR_THREAD).bv := hs4.curThread
  rw [← e1, hkt] at hkt'; cases hkt'
  rw [hsct] at hsct'
  obtain ⟨hb0, hscp⟩ := optRef_some hsct'.symm
  have e2 : σ3.curSc = (nodeW st s4 c layout.node.CUR_SC).bv := hs4.curSc
  obtain ⟨sc, hscC0, hscv⟩ := hcsc
  have hscw : nodeW st s4 c layout.node.CUR_SC = sc := eq_of_bv (by rw [← e2, hscv])
  refine WP.spec_bind (switch_sched_context_cur s4 a2 σ4 hS4 hR4 hN4 hI4 (by rw [hscw]; exact hscC0) hb0
    (by rw [← e1]; exact hntr)
    (fun xt0 hk0 q => by rw [← e1, hkt] at hk0; cases hk0; exact hnbt q)
    (fun hid x n hx => hactt (by rw [← hscp]; exact hid) x n (by rw [← hscp]; exact hx))
    (u0 := u0) (fun x n hx => hown0 x n (by rw [e2]; exact hx)) hback hnr hoff (hmrt a2) (hmb a2)) ?_
  rintro ⟨s5, a3⟩ ⟨σ5, h5, hS5, hR5, hN5, hI5, hC5, rfl⟩
  obtain ⟨Q5, R5, hc5, hs5⟩ := hS5.lists
  have hsc5 : Fl4Spec.scAndTimer (Z := Unit) σ4 = (do
      let reprogram ← Fl4Spec.NonDet.gets fun s : Fl4Spec.State Unit => s.reprogramTimer
      Fl4Spec.NonDet.when (reprogram = true) (do
        Fl4Spec.setNextInterrupt
        Fl4Spec.NonDet.modify fun s : Fl4Spec.State Unit => { s with reprogramTimer := false })) σ5 := by
    unfold Fl4Spec.scAndTimer; rw [nd_bind_one h5]
  rw [hsc5, nd_gets_bind]
  step with LawfulStore.cur_cpu_spec as ⟨c5, hc5'⟩
  rw [hc5.cur] at hc5'
  subst hc5'
  step with obj.node_get.spec as ⟨i, hi⟩
  have hrep := hS5.repr
  by_cases hi0 : i = 0#u64
  · have hb : (i != 0#u64) = false := by rw [hi0]; rfl
    simp only [hb, Bool.false_eq_true, ↓reduceIte, bind_ok]
    have hrf : σ5.reprogramTimer = false := by rw [hrep]; simp [nodeW, ← hi, hi0]
    refine WP.spec_mono (hsend s5 a3 σ5 hS5 hR5) ?_
    rintro r ⟨hSr, hRr⟩
    refine ⟨σ5, ?_, hSr, hRr, hN5, hI5, hC5⟩
    unfold Fl4Spec.NonDet.when; rw [hrf]; rfl
  · have hb : (i != 0#u64) = true := by simpa using hi0
    simp only [hb, ↓reduceIte]
    have hrt : σ5.reprogramTimer = true := by rw [hrep]; simp [nodeW, ← hi, hi0]
    refine WP.spec_bind (Pₘ := fun r : S × A => ∃ σ7, (do
        Fl4Spec.setNextInterrupt (Z := Unit)
        Fl4Spec.NonDet.modify fun s : Fl4Spec.State Unit => { s with reprogramTimer := false }) σ5 =
          ({((), σ7)}, False) ∧ SchedRel st N T C c5 r.1 σ7 ∧ NtfnStateRel N T (L.mem r.1) σ7 ∧ NSC N C σ7 ∧
          Inv σ7 ∧ CurInv σ7) ?_ ?_
    · refine WP.spec_bind (hsni s5 a3 σ5 hS5 hR5) ?_
      rintro ⟨s7, a5⟩ ⟨σ6, h6, hS6, hR6, ek, eq, er, ect, esc, etm, ecn, eact, eid, ecd, edt⟩
      step with obj.node_set.spec as ⟨s8, hs8⟩
      subst hs8
      obtain ⟨hS8, hf8, -⟩ := hS6.set_repr 0#u64
      rw [show decide ((0#u64 : U64) ≠ 0#u64) = false from by decide] at hS8
      refine ⟨{ σ6 with reprogramTimer := false }, by rw [nd_bind_one h6]; rfl, hS8,
        hR6.frame hS6.placed hf8 (KView.of_kheap rfl), fun n hn x p hx hp => hN5 n hn x p (by rw [← ek]; exact hx) hp,
        hI5.congr ek eq er etm, hC5.congr ek ect esc er⟩
    · rintro ⟨s6, a4⟩ ⟨σ7, h7, hS7, hR7, hN7, hI7, hC7⟩
      refine WP.spec_mono (hsend s6 a4 σ7 hS7 hR7) ?_
      rintro r ⟨hSr, hRr⟩
      refine ⟨σ7, ?_, hSr, hRr, hN7, hI7, hC7⟩
      unfold Fl4Spec.NonDet.when; rw [if_pos hrt]; exact h7

/-- `schedule`'s enqueue of the current thread when it is schedulable. -/
theorem enq_ct_refines {N T C : Set U64} {c : U64} (s : S) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) {t : U64} (ht : t ∈ T) (hct : σ.curThread = t.bv) :
    (if Fl4Spec.schedulable t.bv σ = true then sched.enqueue st s t else ok s) ⦃ s4 => ∃ σ4,
      Fl4Spec.NonDet.when (Fl4Spec.schedulable σ.curThread σ = true)
        (Fl4Spec.tcbSchedAction (Z := Unit) Fl4Spec.tcbSchedEnqueue σ.curThread) σ = ({((), σ4)}, False) ∧
      QChange σ σ4 ∧ σ4.schedulerAction = σ.schedulerAction ∧ TK σ σ4 ∧ σ4.curSc = σ.curSc ∧
      σ4.curThread = σ.curThread ∧ FootEq N T (L.mem s) (L.mem s4) ∧ SchedRel st N T C c s4 σ4 ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  rw [hct]
  by_cases hsch : Fl4Spec.schedulable t.bv σ = true
  · simp only [hsch, ↓reduceIte]
    obtain ⟨x, -, -, -, hk, -, -, -, -, hnr⟩ := schedulable_inv hsch
    have hrel0 : (L.mem s (inqA t) &&& sched.Q_RELEASE) = 0#u64 := by
      by_contra hne
      exact hnr (by rw [hs.rel]; exact List.mem_map_of_mem ((hc.released t ht).1 hne))
    refine WP.spec_mono (enqueue_refines s σ hS t ht (fun _ => hrel0)) ?_
    rintro s4 ⟨σ4, he, -, -, hf, hS4⟩
    have e := pair_eq (he.symm.trans (tcbSchedAction_gen hk _))
    refine ⟨σ4, by unfold Fl4Spec.NonDet.when; rw [if_pos trivial]; exact he, ?_, ?_, ?_, ?_, ?_, hf, hS4⟩ <;> rw [← e]
    · exact qchange_enqueue hk hsch
    · rfl
    · exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    · rfl
    · exact hct
  · simp only [hsch, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    exact ⟨σ, by unfold Fl4Spec.NonDet.when; rw [if_neg not_false]; rfl, QChange.refl σ, rfl, ⟨rfl, rfl, rfl, rfl, rfl⟩,
      rfl, hct, FootEq.rfl', hS⟩

/-- The hypothesis on FL4's TCB timers (`timer::fire`, l4h 0003) at every
related state: a sequence of notification signals, keeping the relations
and `SchedPre`. -/
def FireHyp (st : machine.Store S) [L : LawfulStore st] (ar : machine.Arch A) (N T C : Set U64) (c : U64) : Prop :=
  ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), SchedRel st N T C c s σ → NtfnStateRel N T (L.mem s) σ →
    NSC N C σ → SchedPre σ → timer.fire st ar s a ⦃ r => ∃ σ1, Fires σ σ1 ∧ SchedRel st N T C c r.1 σ1 ∧
      NtfnStateRel N T (L.mem r.1) σ1 ∧ NSC N C σ1 ∧ SchedPre σ1 ⦄

/-- **`schedule` refines l4v `schedule`**, ending in `Inv` and `CurInv`.

FL4's `schedule` starts with its TCB timers (`timer::fire`, l4h 0003), a
sequence of notification signals (`Fires`); l4v's `schedule` runs from the
state after them. Hypotheses: `SchedPre` (`Inv`, `CurInv`, `OffOK`,
`IdleOK`, `ActSched`, and the domain scope, domain time nonzero), one domain,
the TCB timers (`FireHyp`), the arch thread switch (`ArchSw`), timer
programming (`SniHyp`), the SMP IPIs (`SendHyp`), and the platform
constants. -/
theorem schedule_refines {N T C : Set U64} {c : U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) (hN : NSC N C σ) (hP : SchedPre σ)
    (hnd : Fl4Spec.numDomains = 1)
    (hfire : FireHyp st ar N T C c) (hA : ArchSw st ar N T C c) (hsni : SniHyp st ar N T C c) (hsend : SendHyp st ar N T C c)
    (hmrt : ∀ a, sporadic.max_release_time ar a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : ∀ a, sporadic.min_budget ar a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄) :
    sched.schedule st ar s a ⦃ r => ∃ σ1 σ', Fires σ σ1 ∧ Fl4Spec.schedule (Z := Unit) σ1 = ({((), σ')}, False) ∧
      SchedRel st N T C c r.1 σ' ∧ NtfnStateRel N T (L.mem r.1) σ' ∧ NSC N C σ' ∧ Inv σ' ∧ CurInv σ' ⦄ := by
  unfold sched.schedule
  refine WP.spec_bind (awaken_refines s a σ (hfire s a σ hS hR hN hP)) ?_
  rintro ⟨s1, a1⟩ ⟨σ1, σ2, hF, haw, hS2, hR2, hN2, ⟨hI2, hC2, hO2, hId2, hA2, hd2⟩, -, -⟩
  have hsp := schedule_unfold haw hnd
  simp only [check_domain_time_refines, bind_ok]
  obtain ⟨Q, R, hc, hs⟩ := hS2.lists
  obtain ⟨hscC, -, -, -, -, -, -⟩ := CurInv.facts hS2 hI2 hC2
  obtain ⟨xt0, hkt0, hxs0, -⟩ := hC2.tcb
  have hown0 : ∀ x n, σ2.kheap σ2.curSc = some (.schedContext x n) → x.scTcb = some σ2.curThread := by
    intro x n hx; obtain ⟨y, m, hy, hyt⟩ := hI2.back _ xt0 _ hkt0 hxs0; rw [hx] at hy; cases hy; exact hyt
  have hback : ∀ xt, σ2.kheap σ2.curThread = some (.tcb xt) → xt.tcbSchedContext = some σ2.curSc := by
    intro xt hk; rw [hkt0] at hk; cases hk; exact hxs0
  have hcsc : ∃ sc ∈ C, sc.bv = σ2.curSc := ⟨_, hscC, hs.curSc.symm⟩
  -- the tail after a branch ending in `σ3`
  have tail : ∀ (s3 : S) (a2 : A) (σ3 : Fl4Spec.State Unit),
      SchedRel st N T C c s3 σ3 → NtfnStateRel N T (L.mem s3) σ3 → NSC N C σ3 → Inv σ3 →
      (σ3.curThread = σ2.idleThread ∨ Fl4Spec.schedulable σ3.curThread σ2 = true ∨ σ3.curThread = σ2.curThread) →
      σ3.kheap = σ2.kheap → σ3.releaseQueue = σ2.releaseQueue → σ3.curSc = σ2.curSc →
      σ3.consumedTime = σ2.consumedTime → σ3.curTime = σ2.curTime →
      (∀ σ', Fl4Spec.scAndTimer (Z := Unit) { σ3 with schedulerAction := .resumeCurThread } = ({((), σ')}, False) →
        Fl4Spec.schedule (Z := Unit) σ1 = ({((), σ')}, False)) →
      (do
        let s4 ← sched.set_action st s3 sched.ACTION_RESUME_CURRENT
        let (s5, a3) ← sched.switch_sched_context st ar s4 a2
        let c ← st.cur_cpu s5
        let i ← obj.node_get st s5 c layout.node.REPROGRAM
        let (s6, a4) ←
          if i != 0#u64
          then
            do
            let (s7, a5) ← sched.set_next_interrupt st ar s5 a3
            let s8 ← obj.node_set st s7 c layout.node.REPROGRAM 0#u64
            ok (s8, a5)
          else ok (s5, a3)
        smp.send_pending st ar s6 a4) ⦃ r => ∃ σ1' σ', Fires σ σ1' ∧
          Fl4Spec.schedule (Z := Unit) σ1' = ({((), σ')}, False) ∧
          SchedRel st N T C c r.1 σ' ∧ NtfnStateRel N T (L.mem r.1) σ' ∧ NSC N C σ' ∧ Inv σ' ∧ CurInv σ' ⦄ := by
    intro s3 a2 σ3 hS3 hR3 hN3 hI3 hnc hk3 hr3 hcs3 hcn3 htm3 hspec
    refine WP.spec_mono (tail_refines s3 a2 σ3 hS3 hR3 hN3 hI3 (newcur_of hnc hk3 hr3 hId2 hC2)
      (by rw [hcs3]; exact hcsc) (u0 := σ2.curThread) (fun x n hx => hown0 x n (by rw [← hk3, ← hcs3]; exact hx))
      (fun xt hx => by rw [hcs3]; exact hback xt (by rw [← hk3]; exact hx)) (by rw [hr3]; exact hC2.notRel)
      (hO2.of_eq hk3 hcs3 hcn3 htm3) hmrt hmb hsni hsend) ?_
    rintro r ⟨σ', h', rest⟩
    exact ⟨σ1, σ', hF, hspec σ' h', rest⟩
  step with sched.action.spec' as ⟨act, hact⟩
  rw [hc.cur] at hact
  subst hact
  have ha := hS2.act
  by_cases h0 : nodeW st s1 c layout.node.SCHED_ACTION = 0#u64
  · -- resume
    have hres : σ2.schedulerAction = .resumeCurThread := by
      cases e : σ2.schedulerAction <;> rw [e] at ha <;> simp only [ActRel] at ha <;>
        first | rfl | (rw [h0] at ha; exact absurd ha (by decide)) | exact absurd h0 ha.1
    have hb : (nodeW st s1 c layout.node.SCHED_ACTION != sched.ACTION_RESUME_CURRENT) = false := by
      rw [resume_val', h0]; rfl
    simp only [hb, Bool.false_eq_true, ↓reduceIte, bind_ok]
    refine tail s1 a1 σ2 hS2 hR2 hN2 hI2 (Or.inr (Or.inr rfl)) rfl rfl rfl rfl rfl (fun σ' h' => ?_)
    rw [hsp, hres]; rw [resume_self hres] at h'; exact h'
  · have hb : (nodeW st s1 c layout.node.SCHED_ACTION != sched.ACTION_RESUME_CURRENT) = true := by
      rw [resume_val']; simpa using h0
    simp only [hb, ↓reduceIte]
    have hct := hc.curT
    have ect : σ2.curThread = (nodeW st s1 c layout.node.CUR_THREAD).bv := hs.curThread
    step with sched.cur_thread.spec' as ⟨ct, hct'⟩
    rw [hc.cur] at hct'
    subst hct'
    step with sched.is_schedulable.spec' as ⟨wr, hwr⟩
    rw [schedulable_eq hR2 hS2 hct] at hwr
    subst hwr
    refine WP.spec_bind (enq_ct_refines s1 σ2 hS2 hct ect) ?_
    rintro s4 ⟨σ4, hw4, hq4, ha4, htk4, hcs4, hct4, hf4, hS4⟩
    have hR4 := hR2.frame hS2.placed hf4 (KView.of_kheap hq4.1)
    have hN4 : NSC N C σ4 := fun n hn x p hx hp => hN2 n hn x p (by rw [← hq4.1]; exact hx) hp
    have hI4 := hI2.qchange hq4
    have hd4 : σ4.domainTime ≠ 0 := by rw [htk4.2.2.2.2]; exact hd2
    -- what a branch ending in `σ3` from `σ4` gives
    have conv : ∀ σ3 : Fl4Spec.State Unit,
        (σ3.curThread = σ4.idleThread ∨ Fl4Spec.schedulable σ3.curThread σ4 = true) →
        σ3.kheap = σ4.kheap → σ3.releaseQueue = σ4.releaseQueue → σ3.curSc = σ4.curSc → TK σ4 σ3 →
        (σ3.curThread = σ2.idleThread ∨ Fl4Spec.schedulable σ3.curThread σ2 = true ∨ σ3.curThread = σ2.curThread) ∧
        σ3.kheap = σ2.kheap ∧ σ3.releaseQueue = σ2.releaseQueue ∧ σ3.curSc = σ2.curSc ∧
        σ3.consumedTime = σ2.consumedTime ∧ σ3.curTime = σ2.curTime := by
      intro σ3 hnc hk hr hcs htk
      refine ⟨?_, hk.trans hq4.1, hr.trans hq4.2.1, hcs.trans hcs4, htk.2.1.trans htk4.2.1, htk.1.trans htk4.1⟩
      rcases hnc with h | h
      · exact Or.inl (h.trans htk4.2.2.1)
      · exact Or.inr (Or.inl (by rw [← schedulable_heap (σ' := σ4) hq4.1 hq4.2.1]; exact h))
    by_cases h1 : nodeW st s1 c layout.node.SCHED_ACTION = 1#u64
    · -- choose a new thread
      have hcn : σ2.schedulerAction = .chooseNewThread := by
        cases e : σ2.schedulerAction <;> rw [e] at ha <;> simp only [ActRel] at ha <;>
          first | rfl | exact absurd ha h0 | exact absurd h1 ha.2.1
      rw [choose_val']
      simp only [h1, ↓reduceIte]
      refine WP.spec_bind (schedule_choose_new_thread_refines s4 a1 σ4 hS4 hR4 hN4 hI4 (hA.1 s4 a1 σ4 hS4 hR4)
        (hA.2 s4 a1 σ4 hS4 hR4) hd4) ?_
      rintro ⟨s3, a2⟩ ⟨σ3, h3, hS3, hR3, hN3, hI3, hnc3, hcs3, hr3, hk3, htk3⟩
      obtain ⟨g1, g2, g3, g4, g5, g6⟩ := conv σ3 hnc3 hk3 hr3 hcs3 htk3
      refine tail s3 a2 σ3 hS3 hR3 hN3 hI3 g1 g2 g3 g4 g5 g6 (fun σ' h' => ?_)
      rw [hsp, hcn]
      exact (nd_bind_one hw4 _).trans ((nd_bind_one h3 _).trans h')
    · -- switch to the candidate
      have hwT : nodeW st s1 c layout.node.SCHED_ACTION ∈ T := by
        rcases hS2.actW with e | e | e
        · exact absurd e h0
        · exact absurd e h1
        · exact e
      have hsw : σ2.schedulerAction = .switchThread (nodeW st s1 c layout.node.SCHED_ACTION).bv := by
        cases e : σ2.schedulerAction <;> rw [e] at ha <;> simp only [ActRel] at ha <;>
          first | exact absurd ha h0 | exact absurd ha h1 | rw [ha.2.2]
      have hb1 : ¬ nodeW st s1 c layout.node.SCHED_ACTION = sched.ACTION_CHOOSE_NEW := by rw [choose_val']; exact h1
      simp only [hb1, ↓reduceIte]
      have hsch4 : Fl4Spec.schedulable (nodeW st s1 c layout.node.SCHED_ACTION).bv σ4 = true := by
        rw [schedulable_heap hq4.1 hq4.2.1]; exact hA2 _ hsw
      have hidle4 : σ4.curThread = σ4.idleThread →
          Fl4Spec.schedulable (nodeW st s1 c layout.node.CUR_THREAD).bv σ2 = false := by
        intro hi
        rw [hct4, htk4.2.2.1, ect] at hi
        rw [hi]
        obtain ⟨x, hx1, -, hx3, -⟩ := hId2
        by_contra hne
        obtain ⟨x', -, -, -, hk', -, hr', -⟩ := schedulable_inv (by simpa using hne)
        rw [hx1] at hk'; cases hk'
        rw [hx3] at hr'; cases hr'
      have hwhen : Fl4Spec.NonDet.when (Fl4Spec.schedulable (nodeW st s1 c layout.node.CUR_THREAD).bv σ2 = true)
          (Fl4Spec.tcbSchedAction (Z := Unit) Fl4Spec.tcbSchedEnqueue σ4.curThread) σ2 = ({((), σ4)}, False) := by
        rw [hct4, ← ect]; exact hw4
      refine WP.spec_bind (switch_branch_refines s4 a1 σ2 σ4 hS4 hR4 hN4 hI4 hA hd4 hwT hsch4 _ hidle4 hwhen) ?_
      rintro ⟨s3, a2⟩ ⟨σ3, h3, hS3, hR3, hN3, hI3, hnc3, hcs3, hr3, hk3, htk3⟩
      obtain ⟨g1, g2, g3, g4, g5, g6⟩ := conv σ3 hnc3 hk3 hr3 hcs3 htk3
      refine tail s3 a2 σ3 hS3 hR3 hN3 hI3 g1 g2 g3 g4 g5 g6 (fun σ' h' => ?_)
      rw [hsp, hsw]
      rw [hct4, ← ect] at h3
      exact (nd_bind_one h3 _).trans h'

end
end
end Fl4Proofs.P3.Sched
