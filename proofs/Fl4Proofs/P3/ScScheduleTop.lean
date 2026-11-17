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
  fired timers, each a notification signal and a reprogram request, `Fires`); l4v's `schedule` runs from the state after
  them.
* `schedule_refinesW`: the same from a mid-entry state, `SchedPreW`
  (`CurInv` only unless a reschedule is pending, the current SC's owner
  `CurOwn`, ScAwaken); `schedule_refines` its corollary (`SchedPre.toW`).
  The outgoing SC's commit needs its owner out of the release queue only
  while time is to be charged (`0 < consumed_time`, l4v
  `cur_sc_in_release_q_imp_zero_consumed`).
-/
import Fl4Proofs.P3.ScAwaken
import Fl4Proofs.P3.ScPlatform
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

/-- The current thread runnable, or the idle thread current (P3's `CurRunW`,
unfolded). -/
def RunW (σ : State Unit) : Prop :=
  (∀ x, σ.kheap σ.curThread = some (.tcb x) → runnable x.tcbState = true) ∨ σ.curThread = σ.idleThread

/-- `RunW` unless a reschedule is pending (P3's `CurRunM`, unfolded). -/
def RunM (σ : State Unit) : Prop := σ.schedulerAction = .chooseNewThread ∨ RunW σ

theorem RunW.calm {σ σ' : State Unit} (h : RunW σ) (hc : Calm σ σ') : RunW σ' := by
  obtain ⟨hk, hct, -, -, -, hid, -⟩ := hc
  rcases h with h | h
  · exact Or.inl fun x hx => h x (by rw [← hk, ← hct]; exact hx)
  · exact Or.inr (by rw [hct, hid]; exact h)

theorem RunM.calm {σ σ' : State Unit} (h : RunM σ) (hc : Calm σ σ')
    (hcn : σ.schedulerAction = .chooseNewThread → σ'.schedulerAction = .chooseNewThread) : RunM σ' := by
  rcases h with h | h
  · exact Or.inl (hcn h)
  · exact Or.inr (h.calm hc)

/-- `RunW` of the new current thread after `schedule`'s branch (as
`newcur_of`): the idle thread, a schedulable one (runnable), or the current
one (`hW`). -/
theorem RunW.of_new2 {σ σ3 : State Unit}
    (h : σ3.curThread = σ.idleThread ∨ schedulable σ3.curThread σ = true)
    (hk : σ3.kheap = σ.kheap) (hid : σ3.idleThread = σ.idleThread) : RunW σ3 := by
  rcases h with h | h
  · exact Or.inr (h.trans hid.symm)
  · obtain ⟨x, scp, y, n, h1, h2, h3, -⟩ := schedulable_inv h
    exact Or.inl fun x' hx' => by rw [hk, h1] at hx'; cases hx'; exact h3

theorem RunW.of_new {σ σ3 : State Unit}
    (h : σ3.curThread = σ.idleThread ∨ schedulable σ3.curThread σ = true ∨ σ3.curThread = σ.curThread)
    (hk : σ3.kheap = σ.kheap) (hid : σ3.idleThread = σ.idleThread) (hW : σ3.curThread = σ.curThread → RunW σ) :
    RunW σ3 := by
  rcases h with h | h | h
  · exact Or.inr (h.trans hid.symm)
  · obtain ⟨x, scp, y, n, h1, h2, h3, -⟩ := schedulable_inv h
    exact Or.inl fun x' hx' => by rw [hk, h1] at hx'; cases hx'; exact h3
  · rcases hW h with hr | hi
    · exact Or.inl fun x hx => hr x (by rw [← h, ← hk]; exact hx)
    · exact Or.inr (by rw [h, hi, hid])

/-- The new current thread after `schedule`'s branch: the idle thread, a
schedulable thread, or the current one. -/
theorem newcur_of {σ σ' : State Unit} (h : σ'.curThread = σ.idleThread ∨ schedulable σ'.curThread σ = true ∨
      σ'.curThread = σ.curThread)
    (hk : σ'.kheap = σ.kheap) (hr : σ'.releaseQueue = σ.releaseQueue) (hId : IdleOK σ) (hC : CurInv σ) :
    ∃ xt scp, σ'.kheap σ'.curThread = some (.tcb xt) ∧ xt.tcbSchedContext = some scp ∧
      NotIpcBlk xt.tcbState ∧ σ'.curThread ∉ σ'.releaseQueue ∧
      (scp ≠ idleScPtr → ∀ x n, σ'.kheap scp = some (.schedContext x n) → scActive x = true) := by
  rw [hk, hr]
  rcases h with h | h | h
  · rw [h]
    obtain ⟨x, h1, h2, h3, h4⟩ := hId
    refine ⟨x, idleScPtr, h1, h2, ?_, h4, fun hne => absurd rfl hne⟩
    rw [h3]; exact NotIpcBlk.idle
  · obtain ⟨x, scp, y, n, h1, h2, h3, h4, h5, h6⟩ := schedulable_inv h
    refine ⟨x, scp, h1, h2, ?_, h6, fun _ x' n' hx => ?_⟩
    · exact NotIpcBlk.of_runnable h3
    · rw [h4] at hx; cases hx; exact h5
  · rw [h]
    obtain ⟨xt, hkt, hxs, hnb⟩ := hC.tcb
    exact ⟨xt, σ.curSc, hkt, hxs, hnb, hC.notRel, fun hne x n hx => hC.active hne x n hx⟩

/-- `newcur_of` for a new thread that is idle or schedulable (no `CurInv`). -/
theorem newcur_of2 {σ σ' : State Unit} (h : σ'.curThread = σ.idleThread ∨ schedulable σ'.curThread σ = true)
    (hk : σ'.kheap = σ.kheap) (hr : σ'.releaseQueue = σ.releaseQueue) (hId : IdleOK σ) :
    ∃ xt scp, σ'.kheap σ'.curThread = some (.tcb xt) ∧ xt.tcbSchedContext = some scp ∧
      NotIpcBlk xt.tcbState ∧ σ'.curThread ∉ σ'.releaseQueue ∧
      (scp ≠ idleScPtr → ∀ x n, σ'.kheap scp = some (.schedContext x n) → scActive x = true) := by
  rw [hk, hr]
  rcases h with h | h
  · rw [h]
    obtain ⟨x, h1, h2, h3, h4⟩ := hId
    refine ⟨x, idleScPtr, h1, h2, ?_, h4, fun hne => absurd rfl hne⟩
    rw [h3]; exact NotIpcBlk.idle
  · obtain ⟨x, scp, y, n, h1, h2, h3, h4, h5, h6⟩ := schedulable_inv h
    refine ⟨x, scp, h1, h2, ?_, h6, fun _ x' n' hx => ?_⟩
    · exact NotIpcBlk.of_runnable h3
    · rw [h4] at hx; cases hx; exact h5

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

/-! ### FL4's footprints on the schedule path -/

theorem bind_ok_inv {α β : Type} {m : Result α} {f : α → Result β} {r : β} (h : (m >>= f) = ok r) :
    ∃ v, m = ok v ∧ f v = ok r := by
  cases m <;> simp at h
  exact ⟨_, rfl, h⟩

theorem spec_ok_post' {α : Type} {m : Result α} {P : α → Prop} (h : m ⦃ P ⦄) {v : α} (hv : m = ok v) : P v := by
  rw [hv, WP.spec_ok] at h; exact h

theorem node_set_tail {s : S} {r : S × A} {cpu o v : U64} {x : Result A}
    (h : (do let s1 ← obj.node_set st s cpu o v; let a1 ← x; ok (s1, a1)) = ok r) :
    r.1 = L.wr s (L.nodeAt s cpu o) v := by
  obtain ⟨s1, h1, h⟩ := bind_ok_inv h
  obtain ⟨a1, -, h⟩ := bind_ok_inv h
  have e := spec_ok_post' (obj.node_set.spec s cpu o v) h1
  have h' : (s1, a1) = r := by simpa using h
  subst h'; exact e

/-- **`set_next_interrupt`'s footprint**: the node's `ARMED` word. -/
theorem sni_foot {T : Set U64} {c : U64} {s : S} {a : A} {r : S × A} (hN : NodePlaced st T s c)
    (hcpu : L.cpu s = c) (h : sched.set_next_interrupt st ar s a = ok r) : WritesIn st s r.1 (SFoot st T c s) := by
  unfold sched.set_next_interrupt at h
  obtain ⟨now, -, h⟩ := bind_ok_inv h
  obtain ⟨t, -, h⟩ := bind_ok_inv h
  obtain ⟨i, -, h⟩ := bind_ok_inv h
  obtain ⟨rr, -, h⟩ := bind_ok_inv h
  obtain ⟨nx, -, h⟩ := bind_ok_inv h
  obtain ⟨nx1, -, h⟩ := bind_ok_inv h
  obtain ⟨i1, hi1, h⟩ := bind_ok_inv h
  have e1 : i1 = L.cpu s := spec_ok_post' (L.cur_cpu_spec s) hi1
  obtain ⟨i2, -, h⟩ := bind_ok_inv h
  obtain ⟨b, -, h⟩ := bind_ok_inv h
  obtain ⟨nx2, -, h⟩ := bind_ok_inv h
  obtain ⟨pr, -, h⟩ := bind_ok_inv h
  obtain ⟨dl, -, h⟩ := bind_ok_inv h
  obtain ⟨td, -, h⟩ := bind_ok_inv h
  obtain ⟨dl1, -, h⟩ := bind_ok_inv h
  obtain ⟨arm, -, h⟩ := bind_ok_inv h
  have hw : WritesIn st s (L.wr s (L.nodeAt s i1 layout.node.ARMED) dl1) (SFoot st T c s) := by
    rw [e1, hcpu]; exact sfoot_wr_node hN (by simp [layout.node.ARMED]) (by simp [layout.node.ARMED]) _
  split at h
  · split at h
    · have h' : (s, a) = r := by simpa using h
      subst h'; exact WritesIn.refl _ _
    · rw [node_set_tail h]; exact hw
  · rw [node_set_tail h]; exact hw

/-- **`send_pending`'s footprint**: the node's `IPI_PENDING` word. -/
theorem send_pending_foot {T : Set U64} {c : U64} {s : S} {a : A} {r : S × A} (hN : NodePlaced st T s c)
    (hcpu : L.cpu s = c) (h : smp.send_pending st ar s a = ok r) : WritesIn st s r.1 (SFoot st T c s) := by
  unfold smp.send_pending at h
  obtain ⟨i1, hi1, h⟩ := bind_ok_inv h
  have e1 : i1 = L.cpu s := spec_ok_post' (L.cur_cpu_spec s) hi1
  obtain ⟨m, -, h⟩ := bind_ok_inv h
  split at h
  · rw [node_set_tail h, e1, hcpu]
    exact sfoot_wr_node hN (by simp [layout.node.IPI_PENDING]) (by simp [layout.node.IPI_PENDING]) _
  · have h' : (s, a) = r := by simpa using h
    subst h'; exact WritesIn.refl _ _

/-- **`append`'s footprint.** -/
theorem append_sfoot {N T C : Set U64} {c : U64} {s : S} {σ : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) {t : U64} (ht : t ∈ T) :
    sched.append st s t ⦃ s' => WritesIn st s s' (SFoot st T c s) ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  have hp := hc.prio t ht
  have haf := hc.aff t ht
  have hN : NodePlaced st T s (L.mem s (affA t)) := by rw [haf]; exact hc.node
  have hN' : NodePlaced st T s (L.cpu s) := by rw [hc.cur]; exact hc.node
  have hR1 : ReadyQueues st T s (L.mem s (affA t)) Q := by rw [haf]; exact hc.ready
  have hnq : (L.mem s (inqA t) &&& sched.Q_QUEUED) = 0#u64 → t ∉ Q (L.mem s (prioA t)) :=
    fun h0 hm => ((hc.queued t ht).2 hm) h0
  refine WP.spec_mono (sched.append.foot s t _ hc.tcbs ht hp hN hN' (hR1.1.rel _ hp) hnq) ?_
  rintro s' ⟨hw, -⟩
  rw [haf] at hw
  refine hw.mono fun b hb => qfoot_sfoot hc.tcbs (fun w hw' => ?_) ht hc.node hc.cur hb
  rcases List.mem_cons.1 hw' with rfl | hw'
  · exact ht
  · exact (hc.ready.1.rel _ hp).mem w hw'

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
      σ'.curSc = σ.curSc ∧ σ'.releaseQueue = σ.releaseQueue ∧ σ'.kheap = σ.kheap ∧ TK σ σ' ∧ WritesIn st s r.1 (SFoot st T c s) ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  unfold sched.schedule_choose_new_thread
  step with sched.domain_time.spec2 as ⟨i, hi⟩
  have hi0 : i ≠ 0#u64 := by
    intro e; apply hdt; rw [hs.domTime, ← hi, e]; rfl
  simp only [hi0, ↓reduceIte, bind_ok]
  refine WP.spec_mono (choose_thread_refines s a σ hS hR hN hI hvm hvmi (by rw [← hs.idleTh])) ?_
  rintro r ⟨σ', h1, h2, h3, h4, h5, h6, h7, h8, h9, -, h11, h12⟩
  refine ⟨σ', ?_, h2, h3, h4, h5, h6, h7, h8, h9, h11, h12⟩
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
      σ'.curSc = σ.curSc ∧ σ'.releaseQueue = σ.releaseQueue ∧ σ'.kheap = σ.kheap ∧ TK σ σ' ∧ WritesIn st s r.1 (SFoot st T c s) ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨x, hk, hd, -, -, -⟩ := hs.tcb t ht
  obtain ⟨x', scp, -, -, hk', hsc, -⟩ := schedulable_inv hsch
  rw [hk] at hk'; cases hk'
  refine WP.spec_mono (switch_to_thread_refines s a σ hS hR hN ht (hA.1 s a σ hS hR t ht)) ?_
  rintro r ⟨σ', h1, h2, h3, h4, h5, h6, h7, h8, h9, -, h11, h12⟩
  refine ⟨σ', ?_, h2, h3, h4, h5 hI, Or.inr (by rw [h6]; exact hsch), h7, h8, h9, h11, h12⟩
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
      σ'.curSc = σ.curSc ∧ σ'.releaseQueue = σ.releaseQueue ∧ σ'.kheap = σ.kheap ∧ TK σ σ' ∧ WritesIn st s r.1 (SFoot st T c s) ⦄ := by
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
        FootEq N T (L.mem s) (L.mem s5) ∧ SchedRel st N T C c s5 σ5 ∧ WritesIn st s s5 (SFoot st T c s) ⦄ := by
    cases enq
    · refine WP.spec_mono (WP.spec_and (append_refines s σ hS t ht (fun _ => hrel0)) (append_sfoot hS ht)) ?_
      rintro s5 ⟨⟨σ5, he, -, -, hf, hS5⟩, hw5⟩
      have e := pair_eq (he.symm.trans (tcbSchedAction_gen hk _))
      refine ⟨σ5, he, ?_, ?_, hf, hS5, hw5⟩ <;> rw [← e]
      · exact qchange_append hk hsch
      · exact ⟨rfl, ⟨rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl⟩
    · refine WP.spec_mono (WP.spec_and (enqueue_refines s σ hS t ht (fun _ => hrel0)) (enqueue_sfoot hS ht)) ?_
      rintro s5 ⟨⟨σ5, he, -, -, hf, hS5⟩, hw5⟩
      have e := pair_eq (he.symm.trans (tcbSchedAction_gen hk _))
      refine ⟨σ5, he, ?_, ?_, hf, hS5, hw5⟩ <;> rw [← e]
      · exact qchange_enqueue hk hsch
      · exact ⟨rfl, ⟨rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl⟩
  refine WP.spec_bind hq ?_
  rintro s5 ⟨σ5, he, hq5, ⟨-, htk5, hcs5, hid5⟩, hf5, hS5, hw5⟩
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
  rintro r ⟨σ', h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  refine ⟨σ', ?_, h2, h3, h4, h5, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [nd_bind_one he, nd_bind_one (setAction_eq σ5 _)]; exact h1
  · rcases h6 with h6 | h6
    · exact Or.inl (h6.trans hid5)
    · exact Or.inr (by rw [← schedulable_heap (σ' := σ6) hq5.1 hq5.2.1]; exact h6)
  · rw [h7]; exact hcs5
  · rw [h8]; exact hq5.2.1
  · rw [h9]; exact hq5.1
  · exact ⟨h10.1.trans htk5.1, h10.2.1.trans htk5.2.1, h10.2.2.1.trans htk5.2.2.1, h10.2.2.2.1.trans htk5.2.2.2.1,
      h10.2.2.2.2.trans htk5.2.2.2.2⟩
  · exact WritesIn.sfoot_trans (WritesIn.sfoot_trans hw5 (sfoot_wr_node hS5.lists.choose_spec.choose_spec.1.node
      (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION]) _)) h11

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
      σ'.curSc = σ.curSc ∧ σ'.releaseQueue = σ.releaseQueue ∧ σ'.kheap = σ.kheap ∧ TK σ σ' ∧ WritesIn st s r.1 (SFoot st T c s) ⦄ :=
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
      σ'.curSc = σ.curSc ∧ σ'.releaseQueue = σ.releaseQueue ∧ σ'.kheap = σ.kheap ∧ TK σ σ' ∧ WritesIn st s r.1 (SFoot st T c s) ⦄ :=
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
      σ'.curSc = σ.curSc ∧ σ'.releaseQueue = σ.releaseQueue ∧ σ'.kheap = σ.kheap ∧ TK σ σ' ∧ WritesIn st s r.1 (SFoot st T c s) ⦄ := by
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
        σ'.curSc = σ.curSc ∧ σ'.releaseQueue = σ.releaseQueue ∧ σ'.kheap = σ.kheap ∧ TK σ σ' ∧ WritesIn st s r.1 (SFoot st T c s)) →
      ∃ σ', Fl4Spec.scheduleSwitchThreadBranch (Z := Unit) t.bv σ.curThread wr σ0 =
        ({((), { σ' with schedulerAction := .resumeCurThread })}, False) ∧
        SchedRel st N T C c r.1 σ' ∧ NtfnStateRel N T (L.mem r.1) σ' ∧ NSC N C σ' ∧ Inv σ' ∧
        (σ'.curThread = σ.idleThread ∨ Fl4Spec.schedulable σ'.curThread σ = true) ∧
        σ'.curSc = σ.curSc ∧ σ'.releaseQueue = σ.releaseQueue ∧ σ'.kheap = σ.kheap ∧ TK σ σ' ∧ WritesIn st s r.1 (SFoot st T c s) := by
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
      NotIpcBlk xt.tcbState ∧ σ3.curThread ∉ σ3.releaseQueue ∧
      (scp ≠ Fl4Spec.idleScPtr → ∀ x n, σ3.kheap scp = some (.schedContext x n) → Fl4Spec.scActive x = true))
    (hcsc : ∃ sc ∈ C, sc.bv = σ3.curSc)
    {u0 : Fl4Spec.ObjRef} (hown0 : ∀ x n, σ3.kheap σ3.curSc = some (.schedContext x n) → x.scTcb = some u0 ∨ x.scTcb = none)
    (hback : ∀ xt, σ3.kheap u0 = some (.tcb xt) → xt.tcbSchedContext = some σ3.curSc)
    (hnr : 0 < σ3.consumedTime → u0 ∉ σ3.releaseQueue) (hoff : OffOK σ3)
    (hT : TimeAgree ar)
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
      SchedRel st N T C c r.1 σ' ∧ NtfnStateRel N T (L.mem r.1) σ' ∧ NSC N C σ' ∧ Inv σ' ∧ CurInv σ' ∧
      (IdleOK σ3 → ActIdle σ') ∧ WritesIn st s3 r.1 (KFoot st T N C c s3 σ3) ⦄ := by
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
  have hA4 : IdleOK σ3 → ActIdle σ4 := fun h =>
    ActIdle.of_noswitch (IdleOK.of h rfl rfl id) (fun t e => by cases e)
  have hw4 : WritesIn st s3 (L.wr s3 (L.nodeAt s3 c layout.node.SCHED_ACTION) 0#u64) (KFoot st T N C c s3 σ3) :=
    WritesIn.kfoot_of_sfoot (sfoot_wr_node hc.node (by simp [layout.node.SCHED_ACTION])
      (by simp [layout.node.SCHED_ACTION]) _)
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
    (fun xt0 hk0 => by rw [← e1, hkt] at hk0; cases hk0; exact hnbt)
    (fun hid x n hx => hactt (by rw [← hscp]; exact hid) x n (by rw [← hscp]; exact hx))
    (u0 := u0) (fun x n hx => hown0 x n (by rw [e2]; exact hx)) hback hnr hoff (hT.mrt a2) (hT.mb a2)) ?_
  rintro ⟨s5, a3⟩ ⟨σ5, h5, hS5, hR5, hN5, hI5, hC5, hA5, rfl, hw5⟩
  have hw5' : WritesIn st s3 s5 (KFoot st T N C c s3 σ3) :=
    WritesIn.kfoot_trans hw4 (SzKeepC.of (SzKeep.of_kheap rfl)) hw5
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
    refine WP.spec_mono (spec_and_eq (hsend s5 a3 σ5 hS5 hR5) fun r hr => send_pending_foot hc5.node hc5.cur hr) ?_
    rintro r ⟨⟨hSr, hRr⟩, hwr⟩
    refine ⟨σ5, ?_, hSr, hRr, hN5, hI5, hC5, fun h => hA5 (hA4 h), WritesIn.kfoot_sfoot hw5' hwr⟩
    unfold Fl4Spec.NonDet.when; rw [hrf]; rfl
  · have hb : (i != 0#u64) = true := by simpa using hi0
    simp only [hb, ↓reduceIte]
    have hrt : σ5.reprogramTimer = true := by rw [hrep]; simp [nodeW, ← hi, hi0]
    refine WP.spec_bind (Pₘ := fun r : S × A => ∃ σ7, (do
        Fl4Spec.setNextInterrupt (Z := Unit)
        Fl4Spec.NonDet.modify fun s : Fl4Spec.State Unit => { s with reprogramTimer := false }) σ5 =
          ({((), σ7)}, False) ∧ SchedRel st N T C c5 r.1 σ7 ∧ NtfnStateRel N T (L.mem r.1) σ7 ∧ NSC N C σ7 ∧
          Inv σ7 ∧ CurInv σ7 ∧ (IdleOK σ3 → ActIdle σ7) ∧ WritesIn st s3 r.1 (KFoot st T N C c5 s3 σ3)) ?_ ?_
    · refine WP.spec_bind (spec_and_eq (hsni s5 a3 σ5 hS5 hR5) fun r hr => sni_foot hc5.node hc5.cur hr) ?_
      rintro ⟨s7, a5⟩ ⟨⟨σ6, h6, hS6, hR6, ek, eq, er, ect, esc, etm, ecn, eact, eid, ecd, edt⟩, hw7⟩
      step with obj.node_set.spec as ⟨s8, hs8⟩
      subst hs8
      obtain ⟨hS8, hf8, -⟩ := hS6.set_repr 0#u64
      rw [show decide ((0#u64 : U64) ≠ 0#u64) = false from by decide] at hS8
      refine ⟨{ σ6 with reprogramTimer := false }, by rw [nd_bind_one h6]; rfl, hS8,
        hR6.frame hS6.placed hf8 (KView.of_kheap rfl), fun n hn x p hx hp => hN5 n hn x p (by rw [← ek]; exact hx) hp,
        hI5.congr ek eq er etm, hC5.congr ek ect esc er,
        fun h => (hA5 (hA4 h)).keep (TKeepE.of_kheap _ ek) (fun u hu => by rw [er] at hu; exact hu) (Or.inl eact) eid,
        WritesIn.kfoot_sfoot (WritesIn.kfoot_sfoot hw5' hw7)
          (sfoot_wr_node hS6.lists.choose_spec.choose_spec.1.node (by simp [layout.node.REPROGRAM])
            (by simp [layout.node.REPROGRAM]) _)⟩
    · rintro ⟨s6, a4⟩ ⟨σ7, h7, hS7, hR7, hN7, hI7, hC7, hA7, hw6⟩
      refine WP.spec_mono (spec_and_eq (hsend s6 a4 σ7 hS7 hR7) fun r hr =>
        send_pending_foot hS7.lists.choose_spec.choose_spec.1.node hS7.lists.choose_spec.choose_spec.1.cur hr) ?_
      rintro r ⟨⟨hSr, hRr⟩, hwr⟩
      refine ⟨σ7, ?_, hSr, hRr, hN7, hI7, hC7, hA7, WritesIn.kfoot_sfoot hw6 hwr⟩
      unfold Fl4Spec.NonDet.when; rw [if_pos hrt]; exact h7

/-- `schedule`'s enqueue of the current thread when it is schedulable. -/
theorem enq_ct_refines {N T C : Set U64} {c : U64} (s : S) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) {t : U64} (ht : t ∈ T) (hct : σ.curThread = t.bv) :
    (if Fl4Spec.schedulable t.bv σ = true then sched.enqueue st s t else ok s) ⦃ s4 => ∃ σ4,
      Fl4Spec.NonDet.when (Fl4Spec.schedulable σ.curThread σ = true)
        (Fl4Spec.tcbSchedAction (Z := Unit) Fl4Spec.tcbSchedEnqueue σ.curThread) σ = ({((), σ4)}, False) ∧
      QChange σ σ4 ∧ σ4.schedulerAction = σ.schedulerAction ∧ TK σ σ4 ∧ σ4.curSc = σ.curSc ∧
      σ4.curThread = σ.curThread ∧ FootEq N T (L.mem s) (L.mem s4) ∧ SchedRel st N T C c s4 σ4 ∧
      WritesIn st s s4 (SFoot st T c s) ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  rw [hct]
  by_cases hsch : Fl4Spec.schedulable t.bv σ = true
  · simp only [hsch, ↓reduceIte]
    obtain ⟨x, -, -, -, hk, -, -, -, -, hnr⟩ := schedulable_inv hsch
    have hrel0 : (L.mem s (inqA t) &&& sched.Q_RELEASE) = 0#u64 := by
      by_contra hne
      exact hnr (by rw [hs.rel]; exact List.mem_map_of_mem ((hc.released t ht).1 hne))
    refine WP.spec_mono (WP.spec_and (enqueue_refines s σ hS t ht (fun _ => hrel0)) (enqueue_sfoot hS ht)) ?_
    rintro s4 ⟨⟨σ4, he, -, -, hf, hS4⟩, hw4⟩
    have e := pair_eq (he.symm.trans (tcbSchedAction_gen hk _))
    refine ⟨σ4, by unfold Fl4Spec.NonDet.when; rw [if_pos trivial]; exact he, ?_, ?_, ?_, ?_, ?_, hf, hS4, hw4⟩ <;>
      rw [← e]
    · exact qchange_enqueue hk hsch
    · rfl
    · exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    · rfl
    · exact hct
  · simp only [hsch, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    exact ⟨σ, by unfold Fl4Spec.NonDet.when; rw [if_neg not_false]; rfl, QChange.refl σ, rfl, ⟨rfl, rfl, rfl, rfl, rfl⟩,
      rfl, hct, FootEq.rfl', hS, WritesIn.refl _ _⟩

/-- The hypothesis on FL4's TCB timers (`timer::fire`, l4h 0003) at every
related state: a sequence of fired timers (`Fires`), keeping the relations
and `SchedPre`. -/
def FireHyp (st : machine.Store S) [L : LawfulStore st] (ar : machine.Arch A) (N T C : Set U64) (c : U64) : Prop :=
  ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), SchedRel st N T C c s σ → NtfnStateRel N T (L.mem s) σ →
    NSC N C σ → SchedPre σ → timer.fire st ar s a ⦃ r => ∃ σ1, Fires σ σ1 ∧ SchedRel st N T C c r.1 σ1 ∧
      NtfnStateRel N T (L.mem r.1) σ1 ∧ NSC N C σ1 ∧ SchedPre σ1 ⦄

/-- **`schedule` refines l4v `schedule` from a mid-entry state**
(`SchedPreW`: `CurInv` only unless a reschedule is pending, the current SC's
owner `CurOwn`), ending in `Inv`, `CurInv` and `ActIdle`. The TCB timers'
hypothesis is stated at `σ` (`hfire`, keeping `SchedPreW`). -/
theorem schedule_refinesWP {N T C : Set U64} {c : U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) (hN : NSC N C σ)
    (hnd : Fl4Spec.numDomains = 1) {Pf : S × A → Fl4Spec.State Unit → Prop}
    (hfire : timer.fire st ar s a ⦃ r => ∃ σ1, Fires σ σ1 ∧ SchedRel st N T C c r.1 σ1 ∧
      NtfnStateRel N T (L.mem r.1) σ1 ∧ NSC N C σ1 ∧ SchedPreW T C σ1 ∧ Pf r σ1 ⦄) (hA : ArchSw st ar N T C c)
    (hsni : SniHyp st ar N T C c) (hsend : SendHyp st ar N T C c)
    (hT : TimeAgree ar) :
    sched.schedule st ar s a ⦃ r => ∃ σ1 σ', Fires σ σ1 ∧ Fl4Spec.schedule (Z := Unit) σ1 = ({((), σ')}, False) ∧
      SchedRel st N T C c r.1 σ' ∧ NtfnStateRel N T (L.mem r.1) σ' ∧ NSC N C σ' ∧ Inv σ' ∧ CurInv σ' ∧
      ActIdle σ' ∧ ∃ rf : S × A, Pf rf σ1 ∧ WritesIn st rf.1 r.1 (KFoot st T N C c rf.1 σ1) ∧
      ∃ σ3 : Fl4Spec.State Unit, OffOK σ3 ∧ (RunM σ1 → RunW σ3) ∧
        Fl4Spec.scAndTimer (Z := Unit) { σ3 with schedulerAction := .resumeCurThread } = ({((), σ')}, False) ⦄ := by
  unfold sched.schedule
  refine WP.spec_bind (awaken_refinesW s a σ hfire) ?_
  rintro ⟨s1, a1⟩ ⟨σ1, σ2, hF, haw, hS2, hR2, hN2, ⟨hI2, hC2w, hO2, ⟨hA2, hId2⟩, hd2, hW2⟩, hcalm, hcn12, -,
    rf, hPf, -, hwA⟩
  have hM2 : RunM σ1 → RunM σ2 := fun h => h.calm hcalm hcn12
  have hsp := schedule_unfold haw hnd
  simp only [check_domain_time_refines, bind_ok]
  obtain ⟨Q, R, hc, hs⟩ := hS2.lists
  -- the outgoing SC's owner `u0`, or (unbound) the SC itself, which no thread names
  obtain ⟨u0, hown0, hback, hnr0, hcsc⟩ : ∃ u0 : Fl4Spec.ObjRef,
      (∀ x n, σ2.kheap σ2.curSc = some (.schedContext x n) → x.scTcb = some u0 ∨ x.scTcb = none) ∧
      (∀ xt, σ2.kheap u0 = some (.tcb xt) → xt.tcbSchedContext = some σ2.curSc) ∧
      (0 < σ2.consumedTime → u0 ∉ σ2.releaseQueue) ∧ ∃ sc ∈ C, sc.bv = σ2.curSc := by
    rcases hW2 with ⟨u0w, hu0T, xt0, hkt0, hxs0, hown0, hnr0⟩ | ⟨⟨sc, hscC, hscv⟩, hun⟩
    · refine ⟨u0w.bv, fun x n hx => Or.inl (hown0 x n hx), fun xt hk => ?_, hnr0, ?_⟩
      · rw [hkt0] at hk; cases hk; exact hxs0
      · obtain ⟨x', hk', -, -, hsct, -⟩ := hs.tcb u0w hu0T
        rw [hkt0] at hk'; cases hk'
        rw [hxs0] at hsct
        obtain ⟨h0, hbv⟩ := optRef_some hsct.symm
        exact ⟨_, hs.scMem _ hu0T h0, hbv⟩
    · obtain ⟨y, n, hky, -⟩ := hs.scs sc hscC
      rw [hscv] at hky
      refine ⟨σ2.curSc, fun x n hx => Or.inr (hun x n hx), fun xt hk => ?_, fun _ hm => ?_, sc, hscC, hscv⟩
      · rw [hky] at hk; cases hk
      · obtain ⟨xu, -, -, -, h1, -⟩ := hI2.rel _ hm
        rw [hky] at h1; cases h1
  -- the tail after a branch ending in `σ3`
  have tail : ∀ (s3 : S) (a2 : A) (σ3 : Fl4Spec.State Unit),
      SchedRel st N T C c s3 σ3 → NtfnStateRel N T (L.mem s3) σ3 → NSC N C σ3 → Inv σ3 →
      (∃ xt scp, σ3.kheap σ3.curThread = some (.tcb xt) ∧ xt.tcbSchedContext = some scp ∧
        NotIpcBlk xt.tcbState ∧ σ3.curThread ∉ σ3.releaseQueue ∧
        (scp ≠ Fl4Spec.idleScPtr → ∀ x n, σ3.kheap scp = some (.schedContext x n) → Fl4Spec.scActive x = true)) →
      σ3.kheap = σ2.kheap → σ3.releaseQueue = σ2.releaseQueue → σ3.curSc = σ2.curSc →
      σ3.consumedTime = σ2.consumedTime → σ3.curTime = σ2.curTime → σ3.idleThread = σ2.idleThread →
      (∀ σ', Fl4Spec.scAndTimer (Z := Unit) { σ3 with schedulerAction := .resumeCurThread } = ({((), σ')}, False) →
        Fl4Spec.schedule (Z := Unit) σ1 = ({((), σ')}, False)) →
      WritesIn st s1 s3 (SFoot st T c s1) → (RunM σ1 → RunW σ3) →
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
          SchedRel st N T C c r.1 σ' ∧ NtfnStateRel N T (L.mem r.1) σ' ∧ NSC N C σ' ∧ Inv σ' ∧ CurInv σ' ∧
          ActIdle σ' ∧ ∃ rf : S × A, Pf rf σ1' ∧ WritesIn st rf.1 r.1 (KFoot st T N C c rf.1 σ1') ∧
          ∃ σ3 : Fl4Spec.State Unit, OffOK σ3 ∧ (RunM σ1' → RunW σ3) ∧
            Fl4Spec.scAndTimer (Z := Unit) { σ3 with schedulerAction := .resumeCurThread } = ({((), σ')}, False) ⦄ := by
    intro s3 a2 σ3 hS3 hR3 hN3 hI3 hnc hk3 hr3 hcs3 hcn3 htm3 hid3 hspec hw3 hrw3
    refine WP.spec_mono (tail_refines s3 a2 σ3 hS3 hR3 hN3 hI3 hnc
      (by rw [hcs3]; exact hcsc) (u0 := u0) (fun x n hx => hown0 x n (by rw [← hk3, ← hcs3]; exact hx))
      (fun xt hx => by rw [hcs3]; exact hback xt (by rw [← hk3]; exact hx)) (fun h0 hm => hnr0 (by rw [← hcn3]; exact h0) (by rw [← hr3]; exact hm))
      (hO2.of_eq hk3 hcs3 hcn3 htm3) hT hsni hsend) ?_
    rintro r ⟨σ', h', a1, a2, a3, a4, a5, a6, a7⟩
    exact ⟨σ1, σ', hF, hspec σ' h', a1, a2, a3, a4, a5,
      a6 (IdleOK.of hId2 hid3 (by rw [hk3]) (fun hm => by rw [hr3] at hm; exact hm)), rf, hPf,
      WritesIn.kfoot_trans (WritesIn.kfoot_of_sfoot (WritesIn.sfoot_trans hwA hw3))
        (SzKeepC.of (SzKeep.of_kheap (hk3.trans hcalm.1))) a7, σ3, hO2.of_eq hk3 hcs3 hcn3 htm3, hrw3, h'⟩
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
    refine tail s1 a1 σ2 hS2 hR2 hN2 hI2
      (newcur_of (Or.inr (Or.inr rfl)) rfl rfl hId2 (hC2w.resolve_left (by rw [hres]; intro e; cases e))) rfl rfl rfl rfl rfl rfl (fun σ' h' => ?_)
      (WritesIn.refl _ _) (fun h => (hM2 h).resolve_left (by rw [hres]; intro e; cases e))
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
    rintro s4 ⟨σ4, hw4, hq4, ha4, htk4, hcs4, hct4, hf4, hS4, hwq4⟩
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
        σ3.consumedTime = σ2.consumedTime ∧ σ3.curTime = σ2.curTime ∧ σ3.idleThread = σ2.idleThread := by
      intro σ3 hnc hk hr hcs htk
      refine ⟨?_, hk.trans hq4.1, hr.trans hq4.2.1, hcs.trans hcs4, htk.2.1.trans htk4.2.1, htk.1.trans htk4.1,
        htk.2.2.1.trans htk4.2.2.1⟩
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
      rintro ⟨s3, a2⟩ ⟨σ3, h3, hS3, hR3, hN3, hI3, hnc3, hcs3, hr3, hk3, htk3, hwb3⟩
      obtain ⟨g1, g2, g3, g4, g5, g6, g7⟩ := conv σ3 hnc3 hk3 hr3 hcs3 htk3
      refine tail s3 a2 σ3 hS3 hR3 hN3 hI3
        (newcur_of2 (by
          rcases hnc3 with h | h
          · exact Or.inl (h.trans htk4.2.2.1)
          · exact Or.inr (by rw [← schedulable_heap (σ' := σ4) hq4.1 hq4.2.1]; exact h)) g2 g3 hId2)
        g2 g3 g4 g5 g6 g7 (fun σ' h' => ?_) (WritesIn.sfoot_trans hwq4 hwb3)
        (fun _ => RunW.of_new2 (σ := σ2) (by
          rcases hnc3 with h | h
          · exact Or.inl (h.trans htk4.2.2.1)
          · exact Or.inr (by rw [← schedulable_heap (σ' := σ4) hq4.1 hq4.2.1]; exact h)) g2 g7)
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
      rintro ⟨s3, a2⟩ ⟨σ3, h3, hS3, hR3, hN3, hI3, hnc3, hcs3, hr3, hk3, htk3, hwb3⟩
      obtain ⟨g1, g2, g3, g4, g5, g6, g7⟩ := conv σ3 hnc3 hk3 hr3 hcs3 htk3
      refine tail s3 a2 σ3 hS3 hR3 hN3 hI3
        (newcur_of g1 g2 g3 hId2 (hC2w.resolve_left (by rw [hsw]; intro e; cases e)))
        g2 g3 g4 g5 g6 g7 (fun σ' h' => ?_) (WritesIn.sfoot_trans hwq4 hwb3)
        (fun h => RunW.of_new g1 g2 g7 fun _ => (hM2 h).resolve_left (by rw [hsw]; intro e; cases e))
      rw [hsp, hsw]
      rw [hct4, ← ect] at h3
      exact (nd_bind_one h3 _).trans h'


/-- `schedule_refinesWP` without the fire predicate and footprint. -/
theorem schedule_refinesW {N T C : Set U64} {c : U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) (hN : NSC N C σ)
    (hnd : Fl4Spec.numDomains = 1)
    (hfire : timer.fire st ar s a ⦃ r => ∃ σ1, Fires σ σ1 ∧ SchedRel st N T C c r.1 σ1 ∧
      NtfnStateRel N T (L.mem r.1) σ1 ∧ NSC N C σ1 ∧ SchedPreW T C σ1 ⦄) (hA : ArchSw st ar N T C c)
    (hsni : SniHyp st ar N T C c) (hsend : SendHyp st ar N T C c)
    (hT : TimeAgree ar) :
    sched.schedule st ar s a ⦃ r => ∃ σ1 σ', Fires σ σ1 ∧ Fl4Spec.schedule (Z := Unit) σ1 = ({((), σ')}, False) ∧
      SchedRel st N T C c r.1 σ' ∧ NtfnStateRel N T (L.mem r.1) σ' ∧ NSC N C σ' ∧ Inv σ' ∧ CurInv σ' ∧
      ActIdle σ' ⦄ :=
  WP.spec_mono (schedule_refinesWP (Pf := fun _ _ => True) s a σ hS hR hN hnd
    (WP.spec_mono hfire fun _ ⟨σ1, h1, h2, h3, h4, h5⟩ => ⟨σ1, h1, h2, h3, h4, h5, trivial⟩) hA hsni hsend hT)
    fun _ ⟨σ1, σ', h1, h2, h3, h4, h5, h6, h7, h8, _⟩ => ⟨σ1, σ', h1, h2, h3, h4, h5, h6, h7, h8⟩

/-- **`schedule` refines l4v `schedule`**, ending in `Inv` and `CurInv`.

FL4's `schedule` starts with its TCB timers (`timer::fire`, l4h 0003), a
sequence of fired timers (`Fires`: notification signals and reprogram requests); l4v's `schedule` runs from the
state after them. Hypotheses: `SchedPre` (`Inv`, `CurInv`, `OffOK`,
`ActIdle`, and the domain scope, domain time nonzero), one domain,
the TCB timers (`FireHyp`), the arch thread switch (`ArchSw`), timer
programming (`SniHyp`), the SMP IPIs (`SendHyp`), and the platform
constants. It ends in `Inv`, `CurInv` and `ActIdle`. A corollary of
`schedule_refinesW`. -/
theorem schedule_refines {N T C : Set U64} {c : U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) (hN : NSC N C σ) (hP : SchedPre σ)
    (hnd : Fl4Spec.numDomains = 1)
    (hfire : FireHyp st ar N T C c) (hA : ArchSw st ar N T C c) (hsni : SniHyp st ar N T C c) (hsend : SendHyp st ar N T C c)
    (hT : TimeAgree ar) :
    sched.schedule st ar s a ⦃ r => ∃ σ1 σ', Fires σ σ1 ∧ Fl4Spec.schedule (Z := Unit) σ1 = ({((), σ')}, False) ∧
      SchedRel st N T C c r.1 σ' ∧ NtfnStateRel N T (L.mem r.1) σ' ∧ NSC N C σ' ∧ Inv σ' ∧ CurInv σ' ∧
      ActIdle σ' ⦄ :=
  schedule_refinesW s a σ hS hR hN hnd
    (WP.spec_mono (hfire s a σ hS hR hN hP) fun _ ⟨σ1, h1, h2, h3, h4, h5⟩ => ⟨σ1, h1, h2, h3, h4, h5.toW h2⟩)
    hA hsni hsend hT
end
end
end Fl4Proofs.P3.Sched
