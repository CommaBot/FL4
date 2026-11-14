/-
P3 (DESIGN.md §9), scheduler: **discharging the notification proofs'
`SchedHyps`** with `SR := SchedRel st N T C c`.

* `stable`: `SchedRel.stable` (SchedRel.lean), no hypothesis.
* `scheduleTcb`: `schedule_tcb_refines` (SchedTcb.lean), no hypothesis.
* `wakeTail`: the scheduler part (`is_schedulable`, then
  `possible_switch_to` ↔ `possible_switch_to`) is proved here; the two
  scheduling-context steps around it are hypotheses (`WakeHyps`):
  - `donate`: `maybe_donate_sched_context` refines `maybe_donate_sc` with a
    single outcome, keeping the footprint, `KView`, `SchedRel`, and leaving
    a state where `ActReady` holds (l4v `valid_sched_action`, needed by
    `reschedule_required`);
  - `unblock`: `unblock_sporadic` refines `get_tcb_obj_ref
    tcb_sched_context t >>= if_sporadic_cur_sc_test_refill_unblock_check`.
  Both are about scheduling contexts and refills (SchedContext_A,
  Sporadic_A), the next subsystem.
* `cancelIpc`: an IPC hypothesis, passed through.
-/
import Fl4Proofs.P3.SchedSwitch
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]

/-- The spec's tail after `possible_switch_to` in a wake-up. -/
def specUnblock (t : Fl4Spec.ObjRef) : Fl4Spec.SMonad Unit Unit := do
  let scopt ← Fl4Spec.getTcbObjRef Fl4Spec.Tcb.tcbSchedContext t
  Fl4Spec.ifSporadicCurScTestRefillUnblockCheck scopt

/-- The scheduling-context hypotheses of a wake-up (see the module
docstring). -/
structure WakeHyps (st : machine.Store S) (ar : machine.Arch A) [L : LawfulStore st] (N T C : Set U64)
    (c : U64) : Prop where
  donate : ∀ s (a : A) σ (t n : U64) (x : Fl4Spec.Tcb), NtfnStateRel N T (L.mem s) σ → SchedRel st N T C c s σ →
    t ∈ T → n ∈ N → σ.kheap t.bv = some (.tcb x) → x.tcbState = .running →
    notification.maybe_donate_sched_context st ar s a t n ⦃ r => ∃ σ1,
      Fl4Spec.maybeDonateSc (Z := Unit) t.bv n.bv σ = ({((), σ1)}, False) ∧ FootEq N T (L.mem s) (L.mem r.1) ∧
      KView σ σ1 ∧ SchedRel st N T C c r.1 σ1 ∧ ActReady σ1 ⦄
  unblock : ∀ s σ (t : U64), NtfnStateRel N T (L.mem s) σ → SchedRel st N T C c s σ → t ∈ T →
    notification.unblock_sporadic st s t ⦃ s' => ¬ (specUnblock t.bv σ).2 ∧
      ∃ σ', ((), σ') ∈ (specUnblock t.bv σ).1 ∧ FootEq N T (L.mem s) (L.mem s') ∧ KView σ σ' ∧
        SchedRel st N T C c s' σ' ⦄

theorem KView.of_kheap {σ σ' : Fl4Spec.State Unit} (h : σ'.kheap = σ.kheap) : KView σ σ' :=
  ⟨fun p x hx => by rw [h]; exact hx, fun p x hx => ⟨x, by rw [h]; exact hx, rfl, rfl, rfl⟩⟩

/-- **`SchedHyps.wakeTail`** from `WakeHyps`. -/
theorem wakeTail_of {N T C : Set U64} {c : U64} (hW : WakeHyps st ar N T C c) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) (t n : U64) (x : Fl4Spec.Tcb) (hR : NtfnStateRel N T (L.mem s) σ)
    (hS : SchedRel st N T C c s σ) (ht : t ∈ T) (hn : n ∈ N) (hk : σ.kheap t.bv = some (.tcb x))
    (hx : x.tcbState = .running) :
    rustWakeTail st ar s a t n ⦃ r => ¬ (specWakeTail t.bv n.bv σ).2 ∧ ∃ σ', ((), σ') ∈ (specWakeTail t.bv n.bv σ).1 ∧
      FootEq N T (L.mem s) (L.mem r.1) ∧ KView σ σ' ∧ SchedRel st N T C c r.1 σ' ⦄ := by
  have hP := hS.placed
  unfold rustWakeTail
  refine WP.spec_bind (hW.donate s a σ t n x hR hS ht hn hk hx) ?_
  rintro ⟨s4, a2⟩ ⟨σ1, hd, hf1, hv1, hS1, hr1⟩
  have hS1 : SchedRel st N T C c s4 σ1 := hS1
  have hf1 : FootEq N T (L.mem s) (L.mem s4) := hf1
  have hR1 : NtfnStateRel N T (L.mem s4) σ1 := hR.frame hP hf1 hv1
  step as ⟨b1, b1_post⟩
  rw [schedulable_eq hR1 hS1 ht] at b1_post
  -- the middle: `possible_switch_to` when schedulable
  have hmid : (if b1 = true then sched.possible_switch_to st s4 t else ok s4) ⦃ s5 => ∃ σ2,
      (Fl4Spec.NonDet.when (Fl4Spec.schedulable t.bv σ1 = true) (Fl4Spec.possibleSwitchTo t.bv)) σ1 =
        ({((), σ2)}, False) ∧ FootEq N T (L.mem s4) (L.mem s5) ∧ σ2.kheap = σ1.kheap ∧
        SchedRel st N T C c s5 σ2 ⦄ := by
    rw [b1_post]
    by_cases e : Fl4Spec.schedulable t.bv σ1 = true
    · simp only [e, ↓reduceIte, Fl4Spec.NonDet.when]
      refine WP.spec_mono (possible_switch_to_refines s4 σ1 hR1 hS1 hr1 t ht) ?_
      rintro s5 ⟨σ2, hp, hk2, hf, hS2⟩
      exact ⟨σ2, hp, hf, hk2, hS2⟩
    · simp only [e, Bool.false_eq_true, ↓reduceIte, Fl4Spec.NonDet.when, WP.spec_ok]
      exact ⟨σ1, rfl, FootEq.rfl', rfl, hS1⟩
  refine WP.spec_bind hmid ?_
  rintro s5 ⟨σ2, hw2, hf2, hk2, hS2⟩
  have hR2 : NtfnStateRel N T (L.mem s5) σ2 := hR1.frame hP hf2 (KView.of_kheap hk2)
  refine WP.spec_bind (hW.unblock s5 σ2 t hR2 hS2 ht) ?_
  rintro s6 ⟨hnf, σ', hm, hf3, hv3, hS3⟩
  simp only [WP.spec_ok]
  have hspec : specWakeTail t.bv n.bv σ = specUnblock t.bv σ2 := by
    unfold specWakeTail
    rw [nd_bind_one hd, nd_gets_bind, nd_bind_one hw2]
    rfl
  rw [hspec]
  exact ⟨hnf, σ', hm, FootEq.trans' (FootEq.trans' hf1 hf2) hf3,
    KView.trans (KView.trans hv1 (KView.of_kheap hk2)) hv3, hS3⟩

/-- **The notification proofs' `SchedHyps`, discharged** for `SchedRel`, from
the scheduling-context hypotheses `WakeHyps` and the IPC hypothesis
`cancel_ipc` (passed through). -/
theorem schedHyps {N T C : Set U64} {c : U64} (hW : WakeHyps st ar N T C c)
    (hC : ∀ s (a : A) σ (t : U64) (x : Fl4Spec.Tcb), NtfnStateRel N T (L.mem s) σ → SchedRel st N T C c s σ →
      t ∈ T → σ.kheap t.bv = some (.tcb x) → Fl4Spec.receiveBlocked x.tcbState = true →
      ipc.cancel_ipc st ar s a t ⦃ r => ∃ σ' x', Fl4Spec.cancelIpc (Z := Unit) t.bv σ = ({((), σ')}, False) ∧
        NtfnStateRel N T (L.mem r.1) σ' ∧ SchedRel st N T C c r.1 σ' ∧ σ'.kheap t.bv = some (.tcb x') ∧
        x'.tcbState = .inactive ∧ RelIfBound σ' t.bv ⦄)
    (hNQ : ∀ s σ (t : U64) (x : Fl4Spec.Tcb), SchedRel st N T C c s σ → σ.kheap t.bv = some (.tcb x) →
      Fl4Spec.runnable x.tcbState = false → NotQueued σ t.bv) :
    SchedHyps st ar N T (SchedRel st N T C c) where
  stable := fun _ _ _ _ hS hw hn _ => hS.stable hw hn
  block := fun _ _ _ _ _ hS _ _ _ _ hw hn _ => hS.stable hw hn
  scheduleTcb := fun s σ t hR hS ht => schedule_tcb_refines s σ hR hS t ht
  wakeTail := fun s a σ t n x hR hS ht hn hk hx _ => wakeTail_of hW s a σ t n x hR hS ht hn hk hx
  cancelIpc := hC
  notQueued := hNQ

/-- **`set_thread_state` refines `set_thread_state`** (state word, then
`schedule_tcb` ↔ `set_thread_state_act`), for a new state that is not
`BlockedOnNotification` (FL4 writes the block object separately for that
one) and a thread in no notification queue. -/
theorem set_thread_state_refines {N T C : Set U64} {c : U64} (s : S) (σ : Fl4Spec.State Unit)
    (hR : NtfnStateRel N T (L.mem s) σ) (hS : SchedRel st N T C c s σ) {t : U64} (ht : t ∈ T)
    {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x))
    (hq : ∀ n ∈ N, ∀ z, σ.kheap n.bv = some (.notification z) → t.bv ∉ z.ntfnObj.ntfnQueue)
    (v : U64) (ts : Fl4Spec.ThreadState) (hv : v.val = tsCode ts) (hnb : ∀ n, ts ≠ .blockedOnNotification n) :
    sched.set_thread_state st s t v ⦃ s' => ∃ σ', Fl4Spec.setThreadState (Z := Unit) t.bv ts σ = ({((), σ')}, False) ∧
      NtfnStateRel N T (L.mem s') σ' ∧ SchedRel st N T C c s' σ' ⦄ := by
  have hP := hS.placed
  unfold sched.set_thread_state
  step
  subst s1_post
  have hx := hR.at_tcb ht hk
  obtain ⟨hw, hoth⟩ := twr_wr (st := st) hP ht (K := 3328#u64) (Or.inl rfl) s v
  rw [← tStA_eq] at hw hoth
  have hR1 : NtfnStateRel N T (L.mem (L.wr s (tStA t) v)) (updK σ t.bv (.tcb { x with tcbState := ts })) := by
    refine hR.upd_tcb ht _ hw.ntfn hw.tcb hw.links (Or.inl hq) ⟨?_, ?_, ?_, ?_⟩
    · rw [rd_wr_eq (foot_st hP ht).1]; exact hv
    · intro n hn; exact absurd hn (hnb n)
    · show (L.mem _ (badgeRegA t)).bv = badgeOf x
      rw [badgeRegA_eq, hoth _ (by simp) (by simp) (by simp), ← badgeRegA_eq]; exact hx.badge
    · show (L.mem _ (prioA t)).val = x.tcbPriority.toNat
      rw [prioA_eq', hoth _ (by simp) (by simp) (by simp), ← prioA_eq']; exact hx.prio
  have hS1 := hS.stable hw.foot (NtfnStep.tcb hk ts x.tcbArch)
  refine WP.spec_mono (schedule_tcb_refines _ _ hR1 hS1 t ht) ?_
  rintro s2 ⟨hf, hS2⟩
  exact ⟨_, setThreadState_eq ts hk, hR1.frame hP hf (KView.stsAct _ _), hS2⟩

end

end

end Fl4Proofs.P3.Sched
