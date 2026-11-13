/-
P3 (DESIGN.md §9), notifications: the scheduler interface, and
**`send_signal` on a waiting notification, and on an idle one whose bound
TCB is receiving, refines l4v `send_signal`** (`Z = Unit`), relative to the
scheduler and IPC refinements, which are hypotheses.

Waking a thread (seL4 `sendSignal`'s waiting and bound-receiver cases) is:
dequeue it (waiting case) or cancel its IPC (bound case), set it running
(`set_thread_state`: the state word, then `schedule_tcb`), write the badge
to its badge register, then the scheduler tail `rustWakeTail` (donate the
notification's SC, `possible_switch_to` if schedulable, the sporadic
unblock check) against the spec's `specWakeTail`. The notification and TCB
parts are proved here; the rest is the parameter `SR` (the relation of the
other subsystems: scheduler state, SCs, endpoints, ...; left abstract) with
the hypotheses `SchedHyps`:

* `stable`: `SR` ignores what the notification code itself changes: FL4
  words the notification code writes (`NWrite`) and, in the spec, `ntfn_obj` of
  notifications and the state and user context of TCBs (`NtfnStep`);
* `scheduleTcb`: `schedule_tcb t` refines `set_thread_state_act t` (whose
  single outcome is `stsAct`), keeping the footprint;
* `wakeTail`: `rustWakeTail` refines `specWakeTail` for a running TCB:
  the spec does not fail, FL4's outcome is matched by one of the spec's,
  FL4 keeps the footprint and the spec `KView` (notifications; TCB state,
  badge register, priority), and `SR` holds after;
* `cancelIpc`: `cancel_ipc t` of a TCB blocked on a receive refines
  `cancel_ipc t`, with a single spec outcome, keeping `NtfnStateRel` and
  `SR`, and leaving the TCB inactive.

Results (`send_signal_waiting`, `send_signal_idle_bound_recv`): the spec
does not fail, and every FL4 outcome is related (`NtfnStateRel ∧ SR`) to
one of the spec's.
-/
import Fl4Proofs.P3.NtfnQueue
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Notif
open fl4_core Fl4Proofs.P1

noncomputable section

/-! ## The tails -/

section Defs
variable {S A : Type} (st : machine.Store S) (ar : machine.Arch A)

/-- FL4's scheduler tail of a wake-up (notification.rs `send_signal`, after
the badge is written). -/
def rustWakeTail (s : S) (a : A) (t : obj.Tcb) (n : U64) : Result (S × A) := do
  let (s4, a2) ← notification.maybe_donate_sched_context st ar s a t n
  let b1 ← sched.is_schedulable st s4 t
  let s5 ← if b1 then sched.possible_switch_to st s4 t else ok s4
  let s6 ← notification.unblock_sporadic st s5 t
  ok (s6, a2)

/-- FL4's wake-up of `t` by `n` with `badge`, after the dequeue / cancel. -/
def rustWake (s : S) (a : A) (t : obj.Tcb) (n badge : U64) : Result (S × A) := do
  let s2 ← sched.set_thread_state st s t sched.TS_RUNNING
  let s3 ← obj.Tcb.set_reg st t s2 layout.reg.BADGE badge
  rustWakeTail st ar s3 a t n

end Defs

section SpecDefs
open Fl4Spec

/-- The spec's scheduler tail of a wake-up (Ipc_A `send_signal`,
`update_waiting_ntfn`, after `as_user … setRegister`). -/
def specWakeTail (t n : ObjRef) : SMonad Unit Unit := do
  maybeDonateSc t n
  let sched ← NonDet.gets (schedulable t)
  NonDet.when sched <| possibleSwitchTo t
  let scopt ← getTcbObjRef Tcb.tcbSchedContext t
  ifSporadicCurScTestRefillUnblockCheck scopt

/-- The spec's wake-up of `t` by `n` with `badge`. -/
def specWake (t n : ObjRef) (badge : Badge) : SMonad Unit Unit := do
  setThreadState t .running
  asUser t <| setRegister badge_register badge
  specWakeTail t n

end SpecDefs

/-! ## The hypotheses -/

section Hyps
variable {S A : Type} (st : machine.Store S) (ar : machine.Arch A) [L : LawfulStore st]

/-- What the notification proofs assume of the other subsystems' relation
`SR` (see the module docstring). -/
structure SchedHyps (N T : Set U64) (SR : S → Fl4Spec.State Unit → Prop) : Prop where
  stable : ∀ s s' σ σ', SR s σ → WritesIn st s s' (NWrite N T) → NtfnStep σ σ' → SR s' σ'
  scheduleTcb : ∀ s σ (t : U64), NtfnStateRel N T (L.mem s) σ → SR s σ → t ∈ T →
    sched.schedule_tcb st s t ⦃ s' => FootEq N T (L.mem s) (L.mem s') ∧ SR s' (stsAct σ t.bv) ⦄
  wakeTail : ∀ s (a : A) σ (t n : U64) (x : Fl4Spec.Tcb), NtfnStateRel N T (L.mem s) σ → SR s σ → t ∈ T →
    n ∈ N → σ.kheap t.bv = some (.tcb x) → x.tcbState = .running →
    rustWakeTail st ar s a t n ⦃ r => ¬ (specWakeTail t.bv n.bv σ).2 ∧ ∃ σ', ((), σ') ∈ (specWakeTail t.bv n.bv σ).1 ∧
      FootEq N T (L.mem s) (L.mem r.1) ∧ KView σ σ' ∧ SR r.1 σ' ⦄
  cancelIpc : ∀ s (a : A) σ (t : U64) (x : Fl4Spec.Tcb), NtfnStateRel N T (L.mem s) σ → SR s σ → t ∈ T →
    σ.kheap t.bv = some (.tcb x) → Fl4Spec.receiveBlocked x.tcbState = true →
    ipc.cancel_ipc st ar s a t ⦃ r => ∃ σ' x', Fl4Spec.cancelIpc (Z := Unit) t.bv σ = ({((), σ')}, False) ∧
      NtfnStateRel N T (L.mem r.1) σ' ∧ SR r.1 σ' ∧ σ'.kheap t.bv = some (.tcb x') ∧ x'.tcbState = .inactive ⦄

end Hyps

/-! ## The spec side -/

section Spec
open Fl4Spec
variable {Z : Type}

theorem assert_true {P : Prop} (h : P) (σ : State Z) : NonDet.assert P σ = ({((), σ)}, False) := by
  simp [NonDet.assert, h]

theorem stsAct_kheap (σ : State Z) (t : ObjRef) : (stsAct σ t).kheap = σ.kheap := by
  unfold stsAct; split_ifs <;> rfl

theorem KView.stsAct (σ : State Z) (t : ObjRef) : KView σ (stsAct σ t) := by
  refine ⟨fun p x h => ?_, fun p x h => ⟨x, ?_, rfl, rfl, rfl⟩⟩ <;> rw [stsAct_kheap] <;> exact h

theorem setThreadState_eq {σ : State Z} {p : ObjRef} {x : Tcb} (ts : ThreadState)
    (hk : σ.kheap p = some (.tcb x)) :
    setThreadState (Z := Z) p ts σ = ({((), stsAct (updK σ p (.tcb { x with tcbState := ts })) p)}, False) := by
  unfold setThreadState
  rw [nd_bind_one (threadSet_eq _ hk)]
  exact setThreadStateAct_eq _ _

theorem removeAll_map {xs : List U64} (h : xs.Nodup) (d : U64) :
    removeAll d.bv (xs.map UScalar.bv) = (xs.erase d).map UScalar.bv := by
  unfold removeAll
  rw [h.erase_eq_filter, List.filter_map]
  congr 1
  apply List.filter_congr
  intro y _
  simp only [Function.comp, ne_eq, decide_not]
  by_cases e : y = d
  · subst e; simp
  · simp [e, Ne.symm (bv_inj e)]

/-- `tcb_ntfn_dequeue` of a member. -/
theorem tcbNtfnDequeue_eq {σ : State Z} {p t : ObjRef} {x : Notification}
    (hk : σ.kheap p = some (.notification x)) (ht : t ∈ ntfnQueueOf x) :
    tcbNtfnDequeue (Z := Z) t p σ = ({((), updK σ p (.notification (ntfnObjUpdate (fun _ =>
      match removeAll t (ntfnQueueOf x) with
      | [] => Ntfn.idleNtfn
      | _ => Ntfn.waitingNtfn (removeAll t (ntfnQueueOf x))) x)))}, False) := by
  unfold tcbNtfnDequeue
  rw [nd_bind_one (getNotification_eq hk), nd_pure_bind', nd_bind_one (assert_true ht σ), nd_pure_bind',
    nd_pure_bind']
  exact setNotification_eq _ hk

theorem badgeOf_setReg (x : Tcb) (v : Word) : badgeOf (setReg x badge_register v) = v := by
  simp [badgeOf, setReg, setRegUc, archTcbContextSet, archTcbContextGet]

theorem setReg_state (x : Tcb) (r : Register) (v : Word) : (setReg x r v).tcbState = x.tcbState := rfl
theorem setReg_prio (x : Tcb) (r : Register) (v : Word) : (setReg x r v).tcbPriority = x.tcbPriority := rfl

end Spec

/-! ## Waking a thread -/

section Wake
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st] {N T : Set U64}
  {SR : S → Fl4Spec.State Unit → Prop}

/-- The state word of a TCB in no notification queue, set to running:
related, and `SR` kept. -/
theorem set_thread_state_running (hH : SchedHyps st ar N T SR) (hP : NPlaced T N) (s : S)
    (σ : Fl4Spec.State Unit) (hR : NtfnStateRel N T (L.mem s) σ) (hSR : SR s σ) {t : U64} (ht : t ∈ T)
    {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x))
    (hq : ∀ n ∈ N, ∀ z, σ.kheap n.bv = some (.notification z) → t.bv ∉ z.ntfnObj.ntfnQueue) :
    sched.set_thread_state st s t sched.TS_RUNNING ⦃ s' =>
      NtfnStateRel N T (L.mem s') (stsAct (updK σ t.bv (.tcb { x with tcbState := .running })) t.bv) ∧
      SR s' (stsAct (updK σ t.bv (.tcb { x with tcbState := .running })) t.bv) ⦄ := by
  unfold sched.set_thread_state
  step
  subst s1_post
  have hx := hR.at_tcb ht hk
  obtain ⟨hw, hoth⟩ := twr_wr (st := st) hP ht (K := 3328#u64) (Or.inl rfl) s sched.TS_RUNNING
  rw [← tStA_eq] at hw hoth
  have hR1 : NtfnStateRel N T (L.mem (L.wr s (tStA t) sched.TS_RUNNING))
      (updK σ t.bv (.tcb { x with tcbState := .running })) := by
    refine hR.upd_tcb ht _ hw.ntfn hw.tcb hw.links (Or.inl hq) ⟨?_, ?_, ?_, ?_⟩
    · rw [rd_wr_eq (foot_st hP ht).1, tsVals.1]; rfl
    · intro n hn; cases hn
    · show (L.mem _ (badgeRegA t)).bv = badgeOf x
      rw [badgeRegA_eq, hoth _ (by simp) (by simp) (by simp), ← badgeRegA_eq]; exact hx.badge
    · show (L.mem _ (prioA t)).val = x.tcbPriority.toNat
      rw [prioA_eq', hoth _ (by simp) (by simp) (by simp), ← prioA_eq']; exact hx.prio
  have hSR1 := hH.stable _ _ _ _ hSR hw.foot (NtfnStep.tcb hk .running x.tcbArch)
  refine WP.spec_mono (hH.scheduleTcb _ _ t hR1 hSR1 ht) ?_
  rintro s2 ⟨hf, hS⟩
  exact ⟨hR1.frame hP hf (KView.stsAct _ _), hS⟩

/-- The wake-up of a TCB in no notification queue refines the spec's. -/
theorem wake_refines (hH : SchedHyps st ar N T SR) (hP : NPlaced T N) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) (hR : NtfnStateRel N T (L.mem s) σ) (hSR : SR s σ) {t n : U64} (ht : t ∈ T)
    (hn : n ∈ N) {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x))
    (hq : ∀ n ∈ N, ∀ z, σ.kheap n.bv = some (.notification z) → t.bv ∉ z.ntfnObj.ntfnQueue) (badge : U64) :
    rustWake st ar s a t n badge ⦃ r => ¬ (specWake t.bv n.bv badge.bv σ).2 ∧
      ∃ σ', ((), σ') ∈ (specWake t.bv n.bv badge.bv σ).1 ∧ NtfnStateRel N T (L.mem r.1) σ' ∧ SR r.1 σ' ⦄ := by
  set x1 : Fl4Spec.Tcb := { x with tcbState := .running }
  set σ2 := stsAct (updK σ t.bv (.tcb x1)) t.bv
  have hk2 : σ2.kheap t.bv = some (.tcb x1) := by simp [σ2, stsAct_kheap]
  set σ3 := updK σ2 t.bv (.tcb (setReg x1 Fl4Spec.badge_register badge.bv))
  have hspec : specWake t.bv n.bv badge.bv σ = specWakeTail t.bv n.bv σ3 := by
    unfold specWake
    rw [nd_bind_one (setThreadState_eq _ hk), nd_bind_one (asUser_setRegister_eq _ _ hk2)]
  rw [hspec]
  unfold rustWake
  refine WP.spec_bind (set_thread_state_running hH hP s σ hR hSR ht hk hq) ?_
  rintro s2 ⟨hR2, hSR2⟩
  step
  subst s3_post
  have hx1 := hR2.at_tcb ht hk2
  obtain ⟨hw, hoth⟩ := twr_wr (st := st) hP ht (K := 256#u64) (Or.inr (Or.inr rfl)) s2 badge
  rw [← badgeRegA_eq] at hw hoth
  have hR3 : NtfnStateRel N T (L.mem (L.wr s2 (badgeRegA t) badge)) σ3 := by
    refine hR2.upd_tcb ht _ hw.ntfn hw.tcb hw.links (Or.inr ⟨?_, ?_⟩) ⟨?_, ?_, ?_, ?_⟩
    · rw [tStA_eq, hoth _ (by simp) (by simp) (by simp)]
    · rw [tBlockA_eq, hoth _ (by simp) (by simp) (by simp)]
    · show (L.mem _ (tStA t)).val = tsCode (setReg x1 _ _).tcbState
      rw [setReg_state, tStA_eq, hoth _ (by simp) (by simp) (by simp), ← tStA_eq]; exact hx1.st
    · intro n' hn'; cases hn'
    · show (L.mem _ (badgeRegA t)).bv = badgeOf (setReg x1 _ _)
      rw [badgeOf_setReg, rd_wr_eq (foot_breg hP ht).1]
    · show (L.mem _ (prioA t)).val = (setReg x1 _ _).tcbPriority.toNat
      rw [setReg_prio, prioA_eq', hoth _ (by simp) (by simp) (by simp), ← prioA_eq']; exact hx1.prio
  have hSR3 := hH.stable _ _ _ _ hSR2 hw.foot (by
    have := NtfnStep.tcb hk2 x1.tcbState (setReg x1 Fl4Spec.badge_register badge.bv).tcbArch
    exact this)
  have hk3 : σ3.kheap t.bv = some (.tcb (setReg x1 Fl4Spec.badge_register badge.bv)) := by simp [σ3]
  refine WP.spec_mono (hH.wakeTail _ a σ3 t n _ hR3 hSR3 ht hn hk3 rfl) ?_
  rintro r ⟨hnf, σ', hmem, hf, hv, hS⟩
  exact ⟨hnf, σ', hmem, hR3.frame hP hf hv, hS⟩

end Wake

end

end Fl4Proofs.P3.Notif
