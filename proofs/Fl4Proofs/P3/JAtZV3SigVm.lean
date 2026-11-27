/-
P3 (line mmuAD, gen 35): **`send_signal` to an idle notification bound to a `RunningVM` thread, at `JAtZV3`,
against `sendSignalVF`** (the branch gen 31/32 left as `SignalRestJHyp` / `SignalRestJHypB` [J]).

Why not against the ported `sendSignal`: when FL4's `signal_completes` holds (a VCPU without a pending exit, and the
thread on this core or a full-state caller not current on its own core), FL4 runs `vcpu::report` (the thread
becomes running, the notification stays idle) while `sendSignal` makes the notification active and leaves the
thread `runningVM`; no spec outcome relates to FL4's notification words. So **`SignalRestJHypB` (stated against
`sendSignal`, gen 32 docstring) and gen 32's `SignalJHypB` [J] are false as stated at such a `JAtZV3` state**
(counterexample shape: `n` idle, bound to `t` in `runningVM`, `t`'s VCPU word `v ≠ 0` with `PENDING = 0`, `t`'s
affinity = the executing core). Over `JAtZ` (no VCPU: `JExt`) `signal_completes` is false and the old statement
is the badge branch below. This module states and proves the branch against `sendSignalVF` instead.

* **`SigVmTailJ3`** [J]: from a `JAtZV3` state where `t` (a TCB of the typed heap) is `running` and `n ∈ N` is idle
  and bound to `t`, FL4's tail after the report (`sigVmTailF`: `maybe_donate_sched_context`, `possible_switch_to`
  if schedulable, the sporadic `unblock_check` unless the thread is in the release queue, FL4 #114) refines the
  spec's (`sigVmTailS`: `maybeDonateSc`, `possibleSwitchTo`, `refillUnblockCheck`), deterministically, domain time
  kept, `JAtZV3` after. (sync114: `sigVmTailS` / `sendSignalVF` do not yet have #114's `in release queue` condition;
  until they do, this premise is false for a thread in the release queue whose sporadic SC would be checked.) Why not
  proved:
  it is the wake tail of P3/ScSignalDonJ (`wake_irelD` / `signal_boundDJ`), proved over `JAtZ` for a thread
  that was blocked, not over `JAtZV3` and not for a running (possibly current) thread (`JAtZV3.switchJ` takes
  `t ≠ curThread`). Not false: FL4's tail is the code of the woken-receiver branch with `unblock_sporadic`
  inlined, which ScSignalDonJ relates to exactly these spec calls; the spec's `possibleSwitchTo` of the current
  thread is l4v's (seL4 `possibleSwitchTo` enqueues or sets `switch_thread`), which FL4's `possible_switch_to` ports.
* **`JAtZV3.signalVmJ`**: FL4's `send_signal n badge` at such a notification, from `JAtZV3`: one outcome of
  `sendSignalVF (v3OnCore st s) (v3RemCur st s) n badge`, domain time kept, `JAtZV3` after. Not completing (P3/
  JAtZV3SigComp's `sigCompR` false): `set_active` + `kick_guest` (writes nothing, `AR` kept by `ARKeep`) =
  `sendSignal`'s activation (`v3_ssVF_nc`), by P3/JAtZV3Ntfn's `ntfnPost` with P1's `send_signal.tinv`;
  completing: `vcpu::report` = `vmReportF` (gen 34's `reportJ3`), then `SigVmTailJ3`.

Premises: `SigVmTailJ3` [J] (above), [P] `ZvVirtAgree`, `P0.ArchTotal`, `ARKeep`. No existing statement changed.
-/
import Fl4Proofs.P3.JAtZV3SigComp
import Fl4Proofs.P3.JAtZBSchedR
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

noncomputable section

/-- **The tail of `send_signal` after a completing report refines `sigVmTailS`** [J] (module docstring). -/
def SigVmTailJ3 {S : Type} (st : machine.Store S) [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
    (V X : Set U64) (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs : Set U64) (D : Set U64) : Prop :=
  ∀ (Ac : Set U64) (Lst : U64 → List U64) (s1 : S) (a : A) (σr : Fl4Spec.State Unit) (t n : U64),
    JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s1 a σr → Z.th t = some .tcb → n ∈ Z.N →
    (∃ x, σr.kheap t.bv = some (.tcb x) ∧ x.tcbState = .running) →
    (∃ y, σr.kheap n.bv = some (.notification y) ∧ y.ntfnObj = .idleNtfn ∧ y.ntfnBoundTcb = some t.bv) →
    sigVmTailF st arI s1 a t n ⦃ r => ∃ (σ' : Fl4Spec.State Unit) (Ac' : Set U64) (Lst' : U64 → List U64),
      sigVmTailS n.bv t.bv σr = ({((), σ')}, False) ∧ σ'.domainTime = σr.domainTime ∧
      JAtZV3 (L := L) arI V X AR Z H Cs Ac' Lst' D r.1 r.2 σ' ⦄

section
open Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {V X : Set U64}

set_option maxHeartbeats 16000000 in
/-- **FL4's walk of `send_signal` to the `RunningVM` branch** (module docstring): completing, the whole outcome;
not completing, the activation as `SingleRelI` with `AR` kept. -/
theorem JAtZV3.signalVmW (hAT : P0.ArchTotal arI) (hVA : ZvVirtAgree arI) (hK : ARKeep arI AR)
    (hTl : SigVmTailJ3 st arI V X AR Z H Cs D)
    (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {n : U64} (hn : n ∈ Z.N)
    {x : Fl4Spec.Notification} (hk : σ.kheap n.bv = some (.notification x)) (hidle : x.ntfnObj = .idleNtfn)
    {t : U64} (hb : x.ntfnBoundTcb = some t.bv) {y : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb y))
    (hrs : y.tcbState = .runningVM) (badge : U64) :
    notification.send_signal st arI s a n badge ⦃ r =>
      (∃ (σ' : Fl4Spec.State Unit) (Ac' : Set U64) (Lst' : U64 → List U64),
        Fl4Spec.sendSignalVF (Z := Unit) (v3OnCore st s) (v3RemCur st s) n.bv badge.bv σ = ({((), σ')}, False) ∧
        σ'.domainTime = σ.domainTime ∧ JAtZV3 (L := L) arI V X AR Z H Cs Ac' Lst' D r.1 r.2 σ') ∨
      (Fl4Spec.sendSignalVF (Z := Unit) (v3OnCore st s) (v3RemCur st s) n.bv badge.bv σ =
          Fl4Spec.sendSignal n.bv badge.bv σ ∧ AR r.2 σ.archState.x64CurrentCr3 ∧
        SingleRelI (st := st) Z.N Z.T Z.E Z.R Z.B s σ (Fl4Spec.sendSignal n.bv badge.bv σ) r.1) ⦄ := by
  have B := J.z2.zv.base
  have hI := B.xtop.irelK B.ks B.buf
  have hR := hI.1
  have hAR : AR a σ.archState.x64CurrentCr3 := B.xtop.fin.1.1.2.2.2.2.2.2
  have hx := hR.toN.at_ntfn hn hk
  obtain ⟨hb0, hbt⟩ := Notif.optRef_some (hx.bound.symm.trans hb)
  have hbw : L.mem s (nBoundA n) = t := P1.eq_of_bv hbt
  have hbT : t ∈ Z.T := hbw ▸ hx.bound_mem hb0
  have ht0 : t ≠ 0#u64 := hbw ▸ hb0
  have hth : Z.th t = some .tcb := B.thTcb hbT
  have hy := hR.toN.at_tcb hbT hkt
  have h8 : L.mem s (tStA t) = sched.TS_RUNNING_VM := by
    apply UScalar.eq_of_val_eq
    rw [hy.st, hrs]
    simp [tsCode, sched.TS_RUNNING_VM]
  have hns : L.mem s (tStA t) ≠ sched.TS_BLOCKED_ON_RECV := by
    rw [h8]; unfold sched.TS_RUNNING_VM sched.TS_BLOCKED_ON_RECV; decide
  unfold notification.send_signal
  refine WP.spec_bind (P1.obj.Ntfn.state.spec s n) fun nst enst => ?_
  rw [if_pos (by rw [enst, epState_eq]; exact stOf_idle hx.obj hidle)]
  refine WP.spec_bind (Notif.obj.Ntfn.bound_tcb.spec s n) fun i ei => ?_
  rw [hbw] at ei
  rw [ei]
  refine WP.spec_bind (P1.obj.Tcb.is_null.spec t) fun b eb => ?_
  have hb' : b = false := by rw [eb]; exact decide_eq_false ht0
  rw [hb']
  rw [if_neg Bool.false_ne_true]
  refine WP.spec_bind (Notif.obj.Tcb.state.spec s t) fun i1 ei1 => ?_
  have hns2 : i1 ≠ sched.TS_BLOCKED_ON_RECV := by rw [ei1]; exact hns
  have hvm2 : i1 = sched.TS_RUNNING_VM := by rw [ei1]; exact h8
  rw [if_neg hns2, if_neg Bool.false_ne_true, if_pos hvm2]
  refine WP.spec_bind (J.sigCompR hth hkt) fun c hc => ?_
  cases c with
  | true =>
    rw [if_pos rfl]
    refine WP.spec_bind (J.reportJ3 hAT hVA hth ⟨y, hkt, hrs⟩ badge) ?_
    rintro s1 ⟨σr, Ac1, Lst1, hr, J1, -, -⟩
    obtain ⟨hkh, hrun, hdt⟩ := J.repKh hth hkt hr
    have hnt : n.bv ≠ t.bv := by intro e; rw [e, hkt] at hk; cases hk
    have hkn : σr.kheap n.bv = some (.notification x) := by
      rw [hkh n.bv hnt (fun vs e => by rw [hk] at e; cases e)]; exact hk
    refine WP.spec_mono (hTl Ac1 Lst1 s1 a σr t n J1 hth hn hrun ⟨x, hkn, hidle, hb⟩) ?_
    rintro r ⟨σ', Ac', Lst', h1, h2, J'⟩
    refine Or.inl ⟨σ', Ac', Lst', ?_, h2.trans hdt, J'⟩
    rw [v3_ssVF_comp _ _ _ hk hidle hb hkt hc hrs hr]
    exact h1
  | false =>
    rw [if_neg Bool.false_ne_true]
    have hnc := v3_ssVF_nc (v3OnCore st s) (v3RemCur st s) badge.bv hk hidle hb hkt hc (fun h => Bool.false_ne_true h.2)
    refine WP.spec_bind (Notif.notification.set_active.spec s n badge) fun s1 s1_post => ?_
    subst s1_post
    rw [if_neg Bool.false_ne_true]
    obtain ⟨hR', hW⟩ := set_active_relI B.ip hR hn hk hidle badge
    have hst' : L.mem (L.wr (L.wr s (P1.epTSA n)
        ((L.mem s (P1.epTSA n) &&& ~~~3#u64) ||| (obj.NTFN_ACTIVE &&& 3#u64))) (nBadgeA n) badge)
        (tStA t) = L.mem s (tStA t) := by
      have h1 := nwr_wr (L := L) B.ip.n (K := 8#u64) hn (by simp) (by simp) s
        ((L.mem s (P1.epTSA n) &&& ~~~3#u64) ||| (obj.NTFN_ACTIVE &&& 3#u64))
      rw [← epTSA_eq] at h1
      have h2 := nwr_wr (L := L) B.ip.n (K := 16#u64) hn (by simp) (by simp)
        (L.wr s (P1.epTSA n) ((L.mem s (P1.epTSA n) &&& ~~~3#u64) ||| (obj.NTFN_ACTIVE &&& 3#u64))) badge
      rw [← nBadgeA_eq] at h2
      exact ((h1.trans h2).tcb _ hbT).1.st
    have hrb' : Fl4Spec.receiveBlocked y.tcbState = false := by rw [hrs]; rfl
    have hSR : SingleRelI (st := st) Z.N Z.T Z.E Z.R Z.B s σ (Fl4Spec.sendSignal n.bv badge.bv σ)
        (L.wr (L.wr s (P1.epTSA n) ((L.mem s (P1.epTSA n) &&& ~~~3#u64) ||| (obj.NTFN_ACTIVE &&& 3#u64)))
          (nBadgeA n) badge) :=
      ⟨_, sendSignal_activate hk hidle (Or.inr ⟨t.bv, y, hb, hkt, hrb'⟩) badge.bv, hR',
        NtfnStep.ntfn hk rfl rfl, hW, NoBlock.ntfnUpd _ _ _⟩
    refine WP.spec_bind (Notif.obj.Tcb.state.spec _ t) fun vm_state hvs => ?_
    rw [if_pos (by rw [hvs, hst', h8])]
    refine WP.spec_mono (v3_kick hAT hK _ a t hAR) ?_
    rintro r ⟨e1, hA1⟩
    rw [e1]
    exact Or.inr ⟨hnc, hA1, hSR⟩

set_option maxHeartbeats 16000000 in
/-- **`send_signal` to an idle notification bound to a `RunningVM` thread, at `JAtZV3`, against
`sendSignalVF`** (module docstring). -/
theorem JAtZV3.signalVmJ (hAT : P0.ArchTotal arI) (hVA : ZvVirtAgree arI) (hK : ARKeep arI AR)
    (hTl : SigVmTailJ3 st arI V X AR Z H Cs D)
    (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {n : U64} (hn : n ∈ Z.N)
    {x : Fl4Spec.Notification} (hk : σ.kheap n.bv = some (.notification x)) (hidle : x.ntfnObj = .idleNtfn)
    {t : U64} (hb : x.ntfnBoundTcb = some t.bv) {y : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb y))
    (hrs : y.tcbState = .runningVM) (badge : U64) :
    notification.send_signal st arI s a n badge ⦃ r =>
      ∃ (σ' : Fl4Spec.State Unit) (Ac' : Set U64) (Lst' : U64 → List U64),
        Fl4Spec.sendSignalVF (Z := Unit) (v3OnCore st s) (v3RemCur st s) n.bv badge.bv σ = ({((), σ')}, False) ∧
        σ'.domainTime = σ.domainTime ∧ JAtZV3 (L := L) arI V X AR Z H Cs Ac' Lst' D r.1 r.2 σ' ⦄ := by
  have B := J.z2.zv.base
  have hNt : ∀ m ∈ P1.Heap.ntfns H, H m = some .ntfn := fun _ h => h
  have hnH : n ∈ P1.Heap.ntfns H := B.zH.2.2.2 n hn
  have hP1 := P1.notification.send_signal.tinv hAT s a n badge B.blk hnH (hNt n hnH) B.bufAtJ.1 B.bufAtJ.2
  refine WP.spec_mono (WP.spec_and (J.signalVmW hAT hVA hK hTl hn hk hidle hb hkt hrs badge) hP1) ?_
  rintro ⟨s', a'⟩ ⟨h1, hbk⟩
  try simp only [WP.uncurry'_pair] at hbk
  rcases h1 with h | ⟨hnc, hA1, hSR⟩
  · exact h
  · have hspec := sendSignal_activate hk hidle (Or.inr ⟨t.bv, y, hb, hkt, by rw [hrs]; rfl⟩) badge.bv
    have J1 := J.ntfnPost (y := Fl4Spec.ntfnObjUpdate (fun _ => .activeNtfn badge.bv) x) hn hk (by rw [hidle]; intro l e; cases e)
      (fun l e => by simp [Fl4Spec.ntfnObjUpdate] at e) rfl rfl hspec hSR hbk
    exact ⟨_, Ac, Lst, hnc.trans hspec, rfl, J1.archV hA1⟩

end

end

end Fl4Proofs.P3
