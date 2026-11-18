/-
P3 (DESIGN.md §9), IPC: **`send_signal`'s wake-ups with an SC donation on
`IRel`**, with the footprint `FinStep` and the slots kept (`IFrame`), toward
`SignalRestJHyp` (ScSignalJ).

* `donate_irelF`: IpcDonate's `donate_irel` with the arch value kept
  (`maybe_donate_refinesA`), the slots kept and the footprint `FinStep`
  (the donation writes `KFoot` words).
* `wake_irelD`: IpcSignalWake's `wake_irel` with `maybe_donate_sc` donating
  or not (`donate_irelF` in place of `maybe_donate_nodonate`); its `DonOK`
  from `Inv` after the wake's writes, `NSC`, and the thread in no ready
  queue; the platform's `MIN_BUDGET` (`TimeAgree`).
* `send_signal_wait_irelD`, `send_signal_bound_irelD`:
  `send_signal_wait_irel` (IpcSignalWake), `send_signal_bound_irel`
  (IpcSignalBound) with `wake_irelD`.
-/
import Fl4Proofs.P3.IpcSignalBound
import Fl4Proofs.P3.IpcDonate
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Ipc
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Sched

noncomputable section

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]
variable {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

set_option maxHeartbeats 1000000 in
/-- **`maybe_donate_sched_context` on `IRel` with its footprint** (module
docstring). -/
theorem donate_irelF (hP0 : IPlaced N T E R B)
    (hmb : ∀ a : A, sporadic.min_budget ar a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (hX : IRel st th cr N T C E R B c s σ) {t n : U64} (ht : t ∈ T)
    (hn : n ∈ N) (hD : DonOK st C s σ t n) :
    notification.maybe_donate_sched_context st ar s a t n ⦃ r => r.2 = a ∧ ∃ σ1,
      Fl4Spec.maybeDonateSc (Z := Unit) t.bv n.bv σ = ({((), σ1)}, False) ∧
      IRel st th cr N T C E R B c r.1 σ1 ∧ IFrame (L := L) th s r.1 ∧ FinStep (st := st) T N C c s σ r.1 σ1 ∧
      ActReady σ1 ⦄ := by
  have hSch := hX.2.2.1
  obtain ⟨hRel, hnC, hnq, hAct⟩ := hD
  refine WP.spec_mono (maybe_donate_refinesA s a σ hX.1.toN hSch hRel (hmb a) t n ht hn hnC hnq) ?_
  rintro r ⟨ha, σ1, he, hf, hv, hS1, hw, hA⟩
  have hK : ScTKw (fun p => p = σ.curThread) σ σ1 := ScTKw.ofFalse (NKT.of_eq (nkt_maybeDonateSc t.bv n.bv) he)
  have hN1 : NtfnStateRel N T (L.mem r.1) σ1 := hX.1.toN.frame hSch.placed hf hv
  have hI := tk_lift hP0 hX (hw.mono fun _ h => Or.inl h) hK hS1 hN1
  exact ⟨ha, σ1, he, hI, IRel.iframe_of hX hw (fun b hb => tfoot_oobj hSch (Or.inl hb)),
    ⟨hw.mono fun b hb => Or.inl hb, SzKeepC.of hK.szKeep⟩, hA hAct⟩

/-- The wake's writes keep the ready queues. -/
theorem wakeSt3_rq (σ : Fl4Spec.State Unit) (t : Fl4Spec.ObjRef) (x : Fl4Spec.Tcb) (b : Fl4Spec.Word) :
    (wakeSt3 σ t x b).readyQueues = σ.readyQueues := by
  show (Notif.stsAct (updK σ t (.tcb { x with tcbState := .running })) t).readyQueues = _
  unfold Notif.stsAct; split <;> rfl

/-- The wake's writes keep `NSC` (only the TCB `t` written). -/
theorem wakeSt3_nsc {σ : Fl4Spec.State Unit} {t : Fl4Spec.ObjRef} {x : Fl4Spec.Tcb} (hk : σ.kheap t = some (.tcb x))
    (b : Fl4Spec.Word) (hN : NSC N C σ) : NSC N C (wakeSt3 σ t x b) := by
  intro m hm y p hy hp
  have hkp : ∀ q, q ≠ t → (wakeSt3 σ t x b).kheap q = σ.kheap q := fun q hq => by
    show (updK (Notif.stsAct (updK σ t (.tcb { x with tcbState := .running })) t) t _).kheap q = _
    simp only [updK, Function.update_of_ne hq]
    rw [stsAct_kheap]; simp only [updK, Function.update_of_ne hq]
  have hmt : m.bv ≠ t := by
    intro e
    have : (wakeSt3 σ t x b).kheap t = some (.tcb (setReg { x with tcbState := .running } Fl4Spec.badge_register b)) := by
      show (updK _ t _).kheap t = _; simp [updK]
    rw [e, this] at hy; cases hy
  rw [hkp _ hmt] at hy
  exact hN m hm y p hy hp

set_option maxHeartbeats 8000000 in
/-- **FL4's wake-up with or without a donation on `IRel`** (module
docstring). -/
theorem wake_irelD (hP0 : IPlaced N T E R B)
    (hmb : ∀ a : A, sporadic.min_budget ar a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hX : IRel st th cr N T C E R B c s σ) {t n : U64} (ht : t ∈ T) (hn : n ∈ N)
    {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x)) (htn : t.bv ≠ n.bv)
    (hq : ∀ n ∈ N, ∀ z, σ.kheap n.bv = some (.notification z) → t.bv ∉ z.ntfnObj.ntfnQueue)
    (hqE : ∀ e ∈ E, ∀ z, σ.kheap e.bv = some (.endpoint z) → t.bv ∉ z.epQueue) (badge : U64)
    (hI3 : Inv (wakeSt3 σ t.bv x badge.bv)) (hN : NSC N C σ) (hnr : ∀ d p, t.bv ∉ σ.readyQueues d p) :
    rustWake st ar s a t n badge ⦃ r => r.2 = a ∧ ∃ σd,
      Fl4Spec.maybeDonateSc (Z := Unit) t.bv n.bv (wakeSt3 σ t.bv x badge.bv) = ({((), σd)}, False) ∧
      ∃ σ', specWake t.bv n.bv badge.bv σ = ({((), σ')}, False) ∧
        IRel st th cr N T C E R B c r.1 σ' ∧ IFrame (L := L) th s r.1 ∧ FinStep (st := st) T N C c s σ r.1 σ' ⦄ := by
  have hP := hP0.e
  have hN3 : NSC N C (wakeSt3 σ t.bv x badge.bv) := wakeSt3_nsc hk badge.bv hN
  have hq3 : (wakeSt3 σ t.bv x badge.bv).readyQueues = σ.readyQueues := wakeSt3_rq σ t.bv x badge.bv
  obtain ⟨hR, hSRT⟩ := hX
  set x1 : Fl4Spec.Tcb := { x with tcbState := .running } with hx1
  set σ2 := stsAct (updK σ t.bv (.tcb x1)) t.bv with hσ2
  have hk2 : σ2.kheap t.bv = some (.tcb x1) := by rw [hσ2, stsAct_kheap]; simp [updK]
  have hkp2 : ∀ q, q ≠ t.bv → σ2.kheap q = σ.kheap q := fun q hq' => by
    rw [hσ2, stsAct_kheap]; simp [updK, hq']
  set x3 : Fl4Spec.Tcb := setReg x1 Fl4Spec.badge_register badge.bv with hx3
  set σ3 := updK σ2 t.bv (.tcb x3) with hσ3
  have e3 : σ3 = wakeSt3 σ t.bv x badge.bv := rfl
  have hspec : specWake t.bv n.bv badge.bv σ = specWakeTail t.bv n.bv σ3 := by
    unfold specWake
    rw [nd_bind_one (Notif.setThreadState_eq _ hk), nd_bind_one (Notif.asUser_setRegister_eq _ _ hk2)]
  unfold rustWake
  -- the state `running`
  have hcode : sched.TS_RUNNING.val = tsCode .running := by unfold sched.TS_RUNNING; rfl
  refine WP.spec_bind (WP.spec_and (set_thread_state_cq (ipcCore_top hP) hP0 hP s σ hR.toE
    (IpcRel.toSRN hR hSRT) ht hk hqE hq .running (by decide) sched.TS_RUNNING hcode)
    (set_thread_state_sfoot hSRT.2.1 ht sched.TS_RUNNING)) ?_
  rintro s2 ⟨⟨hE2, hS2⟩, hw2⟩
  have hX2 : IRel st th cr N T C E R B c s2 σ2 := IpcRel.ofSRN hE2 hS2
  have hSS2 : IFrame (L := L) th s s2 :=
    IRel.iframe_of ⟨hR, hSRT⟩ hw2 fun b hb => tfoot_oobj hSRT.2.1 (Or.inl (KFoot.of_sfoot hb))
  have hTW2 : FinStep (st := st) T N C c s σ s2 σ2 :=
    ⟨hw2.mono fun b hb => Or.inl (KFoot.of_sfoot hb), SzKeepC.of (SzKeep.of_tcb (p := t.bv) (x' := x1) hkp2 hk2)⟩
  -- the badge register
  refine WP.spec_bind (Endp.obj.Tcb.set_reg.spec _ t layout.reg.BADGE badge) ?_
  rintro s3 rfl
  have hba : badgeRegA t = regA t layout.reg.BADGE := by rw [badgeRegA_eq_regA, Endp.regIdx_badge]
  obtain ⟨hR3', hW3, hK3⟩ := set_badge_reg_relI hP0 hX2.1 ht hk2 badge
  rw [hba] at hR3' hW3
  have hX3 : IRel st th cr N T C E R B c (L.wr s2 (regA t layout.reg.BADGE) badge) σ3 :=
    ⟨hR3', hX2.2.1.stableN hX2.2.2.1.placed hW3 hK3, hX2.2.2.1.stable hW3 hK3,
      hX2.2.2.2.mono hW3.1 (SzKeep.ntfnStep hK3)⟩
  have hSS3 : IFrame (L := L) th s2 (L.wr s2 (regA t layout.reg.BADGE) badge) :=
    IRel.iframe_of hX2 hW3 fun b hb => iwords_oobj (NWrite.iwords hP.tcb hb)
  have hTW3 : FinStep (st := st) T N C c s2 σ2 (L.wr s2 (regA t layout.reg.BADGE) badge) σ3 :=
    ⟨hW3.mono fun b hb => NWrite.finW hP.tcb hb, SzKeepC.of (SzKeep.ntfnStep hK3)⟩
  set s3 := L.wr s2 (regA t layout.reg.BADGE) badge with hs3
  -- the donation, or not
  have hDon : DonOK st C s3 σ3 t n :=
    ⟨hI3.relOK, fun h0 => NSC.mem hN3 hX3.1.toN hn h0, fun _ y _ => by rw [e3, hq3]; exact hnr _ _,
      hI3.actReady⟩
  unfold rustWakeTail
  refine WP.spec_bind (donate_irelF hP0 hmb s3 a σ3 hX3 ht hn hDon) ?_
  rintro ⟨s4, a4⟩ ⟨ea4, σd, hd, hX4, hSS4, hTW4, hA4⟩
  simp only at ea4
  subst ea4
  -- the switch, when schedulable
  step with Sched.sched.is_schedulable.spec' as ⟨b1, b1_post⟩
  rw [schedulable_eq hX4.1.toN hX4.2.2.1 ht] at b1_post
  have hmid : (if b1 = true then sched.possible_switch_to st s4 t else ok s4) ⦃ s5 => ∃ σ5,
      (Fl4Spec.NonDet.when (Fl4Spec.schedulable t.bv σd = true) (Fl4Spec.possibleSwitchTo t.bv)) σd =
        ({((), σ5)}, False) ∧ IRel st th cr N T C E R B c s5 σ5 ∧ IFrame (L := L) th s4 s5 ∧
        FinStep (st := st) T N C c s4 σd s5 σ5 ⦄ := by
    rw [b1_post]
    by_cases e : Fl4Spec.schedulable t.bv σd = true
    · simp only [e, ↓reduceIte, Fl4Spec.NonDet.when]
      refine WP.spec_mono (WP.spec_and (switch_top hP0 s4 σd hX4.1 hX4.2 hA4 t ht)
        (possible_switch_to_sfootI hX4.1.toN hX4.2.2.1 hA4 ht)) ?_
      rintro s5 ⟨⟨σ5, hps, hk5, hf5, hv5, hS5⟩, hw5⟩
      exact ⟨σ5, hps, ⟨hX4.1.frame hP0 hf5 hv5, hS5⟩, IRel.iframe_of hX4 hw5 fun b hb => sfootI_oobj hP.tcb hb,
        ⟨hw5.mono fun b hb => SFootI.finW hP.tcb hb, SzKeepC.of (SzKeep.of_kheap hk5)⟩⟩
    · simp only [e, Bool.false_eq_true, ↓reduceIte, Fl4Spec.NonDet.when, WP.spec_ok]
      exact ⟨σd, rfl, hX4, IFrame.refl _ _, FinStep.refl _ _⟩
  refine WP.spec_bind hmid ?_
  rintro s5 ⟨σ5, hw5, hX5, hSS5, hTW5⟩
  -- the sporadic check
  refine WP.spec_bind (WP.spec_and (unblock_irel hP0 s5 σ5 hX5 t ht) (unblock_sporadic_kfoot hX5.2.2.1 t ht)) ?_
  rintro s6 ⟨⟨σ6, hu, hf6, hv6, hX6⟩, hw6⟩
  have hSS6 : IFrame (L := L) th s5 s6 := IRel.iframe_of hX5 hw6 fun b hb => tfoot_oobj hX5.2.2.1 (Or.inl hb)
  have hTW6 : FinStep (st := st) T N C c s5 σ5 s6 σ6 := by
    refine ⟨hw6.mono fun b hb => Or.inl hb, SzKeepC.of fun p y k hp => ?_⟩
    have hmem : ((), σ6) ∈ ((Fl4Spec.getTcbObjRef (Z := Unit) Fl4Spec.Tcb.tcbSchedContext t.bv >>=
        Fl4Spec.ifSporadicCurScTestRefillUnblockCheck (Z := Unit)) σ5).1 := by
      rw [show (Fl4Spec.getTcbObjRef (Z := Unit) Fl4Spec.Tcb.tcbSchedContext t.bv >>=
        Fl4Spec.ifSporadicCurScTestRefillUnblockCheck (Z := Unit)) = specUnblock t.bv from rfl, hu]
      exact Set.mem_singleton _
    obtain ⟨y0, h0, -, -⟩ := MaxK.mk_unblock t.bv σ5 ((), σ6) hmem p y k hp
    exact ⟨y0, h0⟩
  simp only [WP.spec_ok]
  refine ⟨trivial, σd, hd, σ6, ?_, hX6, (((hSS2.trans hSS3).trans hSS4).trans hSS5).trans hSS6,
    (((hTW2.trans hTW3).trans hTW4).trans hTW5).trans hTW6⟩
  rw [hspec]
  unfold specWakeTail
  rw [nd_bind_one hd, nd_gets_bind, nd_bind_one hw5]
  exact hu

set_option maxHeartbeats 8000000 in
/-- **A waiting notification signalled on `IRel`, donating or not** (module
docstring). -/
theorem send_signal_wait_irelD (hP0 : IPlaced N T E R B)
    (hmb : ∀ a : A, sporadic.min_budget ar a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hX : IRel st th cr N T C E R B c s σ) (hI : Inv σ) (hN : NSC N C σ) {n : U64} (hn : n ∈ N)
    {x : Fl4Spec.Notification} (hk : σ.kheap n.bv = some (.notification x)) {q : List Fl4Spec.ObjRef}
    (hw : x.ntfnObj = .waitingNtfn q)
    (hbl : ∀ u ∈ Fl4Spec.ntfnQueueOf x, ∃ xu, σ.kheap u = some (.tcb xu) ∧
      xu.tcbState = .blockedOnNotification n.bv) (badge : U64) :
    notification.send_signal st ar s a n badge ⦃ r => r.2 = a ∧ ∃ (d : U64) (xd : Fl4Spec.Tcb) (σd σ' : Fl4Spec.State Unit),
      d.bv ∈ Fl4Spec.ntfnQueueOf x ∧ σ.kheap d.bv = some (.tcb xd) ∧ xd.tcbState = .blockedOnNotification n.bv ∧
      Fl4Spec.maybeDonateSc (Z := Unit) d.bv n.bv
          (wakeSt3 (updK σ n.bv (.notification (afterDequeue x d))) d.bv xd badge.bv) = ({((), σd)}, False) ∧
      Fl4Spec.sendSignal (Z := Unit) n.bv badge.bv σ = ({((), σ')}, False) ∧
      ((), σ') ∈ (specWake d.bv n.bv badge.bv (updK σ n.bv (.notification (afterDequeue x d)))).1 ∧
      IRel st th cr N T C E R B c r.1 σ' ∧ IFrame (L := L) th s r.1 ∧ FinStep (st := st) T N C c s σ r.1 σ' ⦄ := by
  have hP := hP0.e
  obtain ⟨hR, hSRT⟩ := hX
  have hx := hR.toN.at_ntfn hn hk
  have hobj := hx.obj
  rw [hw] at hobj
  obtain ⟨hst, xs, hne, rfl, hQ, hB⟩ := hobj
  obtain ⟨d, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
  have hd : d ∈ d :: rest := List.mem_cons_self
  have hdT : d ∈ T := hQ.mem d hd
  obtain ⟨xd, hkd, -⟩ := hR.tcb d hdT
  have hmem : d.bv ∈ Fl4Spec.ntfnQueueOf x := by
    show d.bv ∈ x.ntfnObj.ntfnQueue
    rw [hw]; simp [Fl4Spec.Ntfn.ntfnQueue]
  obtain ⟨xd', hkd', hxs⟩ := hbl d.bv hmem
  rw [hkd] at hkd'; cases hkd'
  have hdn : d.bv ≠ n.bv := by intro e; rw [e, hk] at hkd; cases hkd
  set σ1 := updK σ n.bv (.notification (afterDequeue x d)) with hσ1
  have hspec : Fl4Spec.sendSignal n.bv badge.bv σ = specWake d.bv n.bv badge.bv σ1 := by
    unfold Fl4Spec.sendSignal
    rw [nd_bind_one (getNotification_eq hk)]
    simp only [hw]
    unfold Fl4Spec.updateWaitingNtfn
    rw [nd_bind_one (assert_true (by simp) σ), nd_pure_bind', List.map_cons, the_head,
      nd_bind_one (tcbNtfnDequeue_eq hk hmem)]
    rfl
  have hk1 : σ1.kheap d.bv = some (.tcb xd) := by simp [hσ1, updK, hdn, hkd]
  have hI1 : Inv σ1 := hI.updNtfn hk (fun p hp => hI.ntfnSc n.bv x p hk hp)
  have hI3 : Inv (wakeSt3 σ1 d.bv xd badge.bv) := wake_inv3 hI1 hk1 hxs badge.bv
  have hN1 : NSC N C σ1 := hN.step (NtfnStep.ntfn (y := afterDequeue x d) hk rfl rfl)
  have hnr1 : ∀ dd pp, d.bv ∉ σ1.readyQueues dd pp := (hI1.notQueued hk1 (by rw [hxs]; rfl)).1
  -- FL4
  unfold notification.send_signal
  step with obj.Ntfn.state.spec as ⟨st0, st_post⟩
  have hsw : st0 = obj.NTFN_WAITING := by
    rw [st_post]
    first
      | exact stOf_waiting (q := _) hx.obj hw
      | (rw [epState_eq]; exact stOf_waiting (q := _) hx.obj hw)
  simp only [hsw, ntfn_consts.1, ntfn_consts.2.1, show (1#u64 : U64) ≠ 0#u64 by decide, ↓reduceIte]
  step with notification.get_queue.spec as ⟨q0, q_post⟩
  have hqh : q0.head = d := by rw [q_post, epQ_eq, hQ.head]; rfl
  rw [hqh]
  refine WP.spec_bind (ntfn_dequeue_full hP0.n s hn d _ hQ hd) ?_
  rintro s1 ⟨h1, h2, h3⟩
  obtain ⟨hR1, hq1⟩ := rel_after_dequeueI hP0 hR hn hk hw hQ hB hd h1 h2 h3 hst
  have hK := NtfnStep.ntfn (y := afterDequeue x d) hk rfl rfl
  have hS1 : SRT st th cr N T C E R B c (SRE st N T C E R B c) s1 σ1 :=
    ⟨hSRT.1.stableN hSRT.2.1.placed h3.foot hK, hSRT.2.1.stable h3.foot hK,
      hSRT.2.2.mono h3.foot.1 (SzKeep.ntfnStep hK)⟩
  have hSS1 : IFrame (L := L) th s s1 :=
    IRel.iframe_of ⟨hR, hSRT⟩ h3.foot fun b hb => iwords_oobj (NWrite.iwords hP.tcb hb)
  have hTW1 : FinStep (st := st) T N C c s σ s1 σ1 :=
    ⟨h3.foot.mono fun b hb => NWrite.finW hP.tcb hb, SzKeepC.of (SzKeep.ntfnStep hK)⟩
  have hqE := Notif.IpcRel.not_ep_queued hR1 (t := d) (by
    rw [(h3.tcb d hdT).st, (hB d hd).1]; decide)
  refine WP.spec_mono (wake_irelD hP0 hmb s1 a σ1 ⟨hR1, hS1⟩ hdT hn hk1 hdn hq1 hqE badge hI3 hN1 hnr1) ?_
  rintro r ⟨hra, σd, hdon, σ', hsw', hX', hSS', hTW'⟩
  exact ⟨hra, d, xd, σd, σ', hmem, hkd, hxs, hdon, by rw [hspec]; exact hsw',
    by rw [hsw']; exact Set.mem_singleton _, hX', hSS1.trans hSS', hTW1.trans hTW'⟩

set_option maxHeartbeats 8000000 in
/-- **The idle notification's bound receiver woken on `IRel`, donating or
not** (module docstring). -/
theorem send_signal_bound_irelD (hP0 : IPlaced N T E R B)
    (hmb : ∀ a : A, sporadic.min_budget ar a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hX : IRel st th cr N T C E R B c s σ) {n : U64} (hn : n ∈ N)
    {x : Fl4Spec.Notification} (hk : σ.kheap n.bv = some (.notification x)) (hidle : x.ntfnObj = .idleNtfn)
    {t : U64} {tcb : Fl4Spec.Tcb} (hb : x.ntfnBoundTcb = some t.bv) (hkt : σ.kheap t.bv = some (.tcb tcb))
    (hrb : Fl4Spec.receiveBlocked tcb.tcbState = true) (badge : U64)
    (hCR : ∀ t' : U64, t' = t → CancelRecvHyp E (L.mem s) σ t' tcb)
    (hA3 : ∀ σ1 x1, Fl4Spec.cancelIpc (Z := Unit) t.bv σ = ({((), σ1)}, False) →
      σ1.kheap t.bv = some (.tcb x1) → x1.tcbState = .inactive → RelIfBound σ1 t.bv →
      Inv (wakeSt3 σ1 t.bv x1 badge.bv) ∧ NSC N C σ1 ∧ ∀ d p, t.bv ∉ σ1.readyQueues d p) :
    notification.send_signal st ar s a n badge ⦃ r => r.2 = a ∧
      ∃ (s1 : S) (σ1 σd σ' : Fl4Spec.State Unit) (x1 : Fl4Spec.Tcb),
      Fl4Spec.cancelIpc (Z := Unit) t.bv σ = ({((), σ1)}, False) ∧ σ1.kheap t.bv = some (.tcb x1) ∧
      x1.tcbState = .inactive ∧ RelIfBound σ1 t.bv ∧ IRel st th cr N T C E R B c s1 σ1 ∧
      IFrame (L := L) th s s1 ∧ WritesIn st s s1 (CnW (st := st) T N C E R c s σ) ∧
      Fl4Spec.maybeDonateSc (Z := Unit) t.bv n.bv (wakeSt3 σ1 t.bv x1 badge.bv) = ({((), σd)}, False) ∧
      Fl4Spec.sendSignal (Z := Unit) n.bv badge.bv σ = ({((), σ')}, False) ∧
      ((), σ') ∈ (specWake t.bv n.bv badge.bv σ1).1 ∧
      IRel st th cr N T C E R B c r.1 σ' ∧ IFrame (L := L) th s1 r.1 ∧ FinStep (st := st) T N C c s1 σ1 r.1 σ' ⦄ := by
  have hP := hP0.e
  have hR := hX.1
  have hx := hR.toN.at_ntfn hn hk
  obtain ⟨hb0, hbt⟩ := Notif.optRef_some (hx.bound ▸ hb)
  have hbt' : L.mem s (nBoundA n) = t := eq_of_bv hbt
  have hiT : t ∈ T := hbt' ▸ hx.bound_mem hb0
  have hy := hR.toN.at_tcb hiT hkt
  have hs3 : L.mem s (tStA t) = sched.TS_BLOCKED_ON_RECV := by
    have h3 := hy.st
    rw [tsVals.2.2.1]
    apply UScalar.eq_of_val_eq
    revert hrb h3
    cases tcb.tcbState <;> simp [tsCode, Fl4Spec.receiveBlocked]
  have htn : t.bv ≠ n.bv := by intro e; rw [e, hk] at hkt; cases hkt
  unfold notification.send_signal
  step with obj.Ntfn.state.spec as ⟨st0, st_post⟩
  have hsi : st0 = obj.NTFN_IDLE := by
    rw [st_post]
    first
      | exact stOf_idle hx.obj hidle
      | (rw [epState_eq]; exact stOf_idle hx.obj hidle)
  simp only [hsi, ↓reduceIte]
  step with Notif.obj.Ntfn.bound_tcb.spec as ⟨i, i_post⟩
  step with obj.Tcb.is_null.spec as ⟨b, b_post⟩
  subst i_post
  simp only [b_post, hb0, decide_false, Bool.false_eq_true, ↓reduceIte]
  step with Notif.obj.Tcb.state.spec as ⟨i1, i1_post⟩
  have hs3' : i1 = sched.TS_BLOCKED_ON_RECV := by rw [i1_post, hbt']; exact hs3
  simp only [hs3', ↓reduceIte]
  rw [hbt']
  refine WP.spec_bind (cancel_ipc_recvF hP0 s a σ hX hiT hkt hrb (hCR t rfl)) ?_
  rintro ⟨s1, a1⟩ ⟨ea, σ1, x1, hc, hX1, hk1, hin, hrib, hW1⟩
  simp only at ea
  subst ea
  have hspec : Fl4Spec.sendSignal n.bv badge.bv σ = specWake t.bv n.bv badge.bv σ1 := by
    unfold Fl4Spec.sendSignal
    rw [nd_bind_one (getNotification_eq hk)]
    simp only [hidle, hb]
    rw [nd_bind_one (getThreadState_eq hkt)]
    simp only [hrb, ↓reduceIte]
    rw [nd_bind_one hc]
    rfl
  have hq1 : ∀ n' ∈ N, ∀ z, σ1.kheap n'.bv = some (.notification z) → t.bv ∉ z.ntfnObj.ntfnQueue := by
    intro n' hn' z hz hm
    obtain ⟨-, h6, -⟩ := (hX1.1.toN.at_ntfn hn' hz).obj.blocked hm
    have := (hX1.1.toN.at_tcb hiT hk1).st
    rw [hin, h6] at this
    cases this
  have hqE := IpcRel.not_ep_queued hX1.1 (t := t) (by
    rw [(hX1.1.toN.at_tcb hiT hk1).st, hin]; decide)
  obtain ⟨hI3, hN1, hnr1⟩ := hA3 σ1 x1 hc hk1 hin hrib
  have hF1 : IFrame (L := L) th s s1 := IRel.iframe_of hX hW1 fun b hb => CnW.oobj hX.2.2.1 hb
  refine WP.spec_mono (wake_irelD hP0 hmb s1 _ σ1 hX1 hiT hn hk1 htn hq1 hqE badge hI3 hN1 hnr1) ?_
  rintro r ⟨hra, σd, hdon, σ', hsw', hX', hSS', hTW'⟩
  exact ⟨hra, s1, σ1, σd, σ', x1, hc, hk1, hin, hrib, hX1, hF1, hW1, hdon, by rw [hspec]; exact hsw',
    by rw [hsw']; exact Set.mem_singleton _, hX', hSS', hTW'⟩

end

end

end Fl4Proofs.P3.Ipc
