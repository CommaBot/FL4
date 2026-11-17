/-
P3 (DESIGN.md §9), IPC: **`send_signal`'s wake-up of a waiting thread on
`IRel`**, with the footprint `FinStep` and the slots kept (`IFrame`), toward
`SignalRestJHyp` (ScSignalJ).

* `wake_irel`: FL4's wake-up (`rustWake`: the state `running`, the badge
  register, no SC donation, the switch when schedulable, the sporadic check)
  against the spec's `specWake`, from `IRel` to `IRel`, for a thread in no
  queue: `set_thread_state_cq`, the badge write (`set_badge_reg_relI`, the
  notification step), `maybe_donate_nodonate` (from `NoDon`, the spec's
  no-donation condition), `switch_top`, `unblock_irel`. The switch needs
  `ActReady` after the writes (`wake_inv3` gives it from `Inv`).
* `send_signal_wait_irel`: the waiting notification's head dequeued
  (`ntfn_dequeue_full`, `rel_after_dequeueI`), then `wake_irel`.
-/
import Fl4Proofs.P3.IpcCancelSignals
import Fl4Proofs.P3.IpcNtfnWake
import Fl4Proofs.P3.ScDonate
import Fl4Proofs.P3.IpcSignalWakeSpec
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Ipc
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Sched

noncomputable section

/-- **No SC donation to `t` from `n`** (`maybe_donate_sc` the identity): `t`
has an SC, or `n` has none, or `n`'s SC (of `C`) is bound to a thread. -/
def NoDon (C : Set U64) (σ : Fl4Spec.State Unit) (t n : Fl4Spec.ObjRef) : Prop :=
  ∀ xt xn, σ.kheap t = some (.tcb xt) → σ.kheap n = some (.notification xn) →
    xt.tcbSchedContext ≠ none ∨ xn.ntfnSc = none ∨
      ∃ cq ∈ C, xn.ntfnSc = some cq.bv ∧ ∃ y k, σ.kheap cq.bv = some (.schedContext y k) ∧ y.scTcb ≠ none

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]
variable {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

/-- `NoDon` at FL4's words (`maybe_donate_nodonate`'s premise). -/
theorem NoDon.words {s : S} {σ : Fl4Spec.State Unit} (hX : IRel st th cr N T C E R B c s σ) {t n : U64}
    (ht : t ∈ T) (hn : n ∈ N) (h : NoDon C σ t.bv n.bv) :
    L.mem s (scA t) ≠ 0#u64 ∨ L.mem s (nScA n) = 0#u64 ∨
      (L.mem s (nScA n) ∈ C ∧ L.mem s (scW (L.mem s (nScA n)) 24#u64) ≠ 0#u64) := by
  have hS := hX.2.2.1
  obtain ⟨Q, R0, hc, hs⟩ := hS.lists
  obtain ⟨xt, hkt, -, -, hsct, -⟩ := hs.tcb t ht
  obtain ⟨xn, hkn, hxn⟩ := hX.1.toN.ntfn n hn
  rcases h xt xn hkt hkn with h1 | h2 | ⟨cq, hcq, h3, y, k, hky, hyt⟩
  · left; intro e; rw [hsct, e, Notif.optRef_zero] at h1; exact h1 rfl
  · right; left
    by_contra e
    rw [hxn.sc, Notif.optRef_ne e] at h2; cases h2
  · right; right
    rw [hxn.sc] at h3
    obtain ⟨-, e⟩ := Notif.optRef_some h3
    have e' : L.mem s (nScA n) = cq := P1.eq_of_bv e
    rw [e']
    refine ⟨hcq, fun e0 => hyt ?_⟩
    obtain ⟨y', k', hky', hy'⟩ := hs.scs cq hcq
    rw [hky] at hky'; cases hky'
    rw [hy'.tcb, e0, Notif.optRef_zero]

set_option maxHeartbeats 8000000 in
/-- **FL4's wake-up of a thread in no queue on `IRel`** (module docstring). -/
theorem wake_irel (hP0 : IPlaced N T E R B) (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hX : IRel st th cr N T C E R B c s σ) {t n : U64} (ht : t ∈ T) (hn : n ∈ N)
    {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x)) (htn : t.bv ≠ n.bv)
    (hq : ∀ n ∈ N, ∀ z, σ.kheap n.bv = some (.notification z) → t.bv ∉ z.ntfnObj.ntfnQueue)
    (hqE : ∀ e ∈ E, ∀ z, σ.kheap e.bv = some (.endpoint z) → t.bv ∉ z.epQueue) (badge : U64)
    (hA3 : ActReady (wakeSt3 σ t.bv x badge.bv)) (hND : NoDon C σ t.bv n.bv) :
    rustWake st ar s a t n badge ⦃ r => r.2 = a ∧
      Fl4Spec.maybeDonateSc (Z := Unit) t.bv n.bv (wakeSt3 σ t.bv x badge.bv) =
        ({((), wakeSt3 σ t.bv x badge.bv)}, False) ∧
      ∃ σ', specWake t.bv n.bv badge.bv σ = ({((), σ')}, False) ∧
        IRel st th cr N T C E R B c r.1 σ' ∧ IFrame (L := L) th s r.1 ∧ FinStep (st := st) T N C c s σ r.1 σ' ⦄ := by
  have hP := hP0.e
  obtain ⟨hR, hSRT⟩ := hX
  set x1 : Fl4Spec.Tcb := { x with tcbState := .running } with hx1
  set σ2 := stsAct (updK σ t.bv (.tcb x1)) t.bv with hσ2
  have hk2 : σ2.kheap t.bv = some (.tcb x1) := by rw [hσ2, stsAct_kheap]; simp [updK]
  have hkp2 : ∀ q, q ≠ t.bv → σ2.kheap q = σ.kheap q := fun q hq' => by
    rw [hσ2, stsAct_kheap]; simp [updK, hq']
  set x3 : Fl4Spec.Tcb := setReg x1 Fl4Spec.badge_register badge.bv with hx3
  set σ3 := updK σ2 t.bv (.tcb x3) with hσ3
  have e3 : σ3 = wakeSt3 σ t.bv x badge.bv := rfl
  have hk3 : σ3.kheap t.bv = some (.tcb x3) := by simp [hσ3, updK]
  have hkp3 : ∀ q, q ≠ t.bv → σ3.kheap q = σ.kheap q := fun q hq' => by
    simp only [hσ3, updK, Function.update_of_ne hq']; exact hkp2 q hq'
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
  -- no donation
  have hND3 : NoDon C σ3 t.bv n.bv := by
    intro xt xn h1 h2
    rw [hk3] at h1; cases h1
    rw [hkp3 n.bv (Ne.symm htn)] at h2
    rcases hND x xn hk h2 with h | h | ⟨cq, hcq, h3, y, k, hky, hyt⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · have hct : cq.bv ≠ t.bv := by intro e; rw [e, hk] at hky; cases hky
      exact Or.inr (Or.inr ⟨cq, hcq, h3, y, k, by rw [hkp3 _ hct]; exact hky, hyt⟩)
  unfold rustWakeTail
  refine WP.spec_bind (maybe_donate_nodonate s3 a σ3 hX3.1.toN hX3.2.2.1 t n ht hn (hND3.words hX3 ht hn)) ?_
  rintro ⟨s4, a4⟩ ⟨e4, hd⟩
  simp only [Prod.mk.injEq] at e4
  obtain ⟨rfl, rfl⟩ := e4
  -- the switch, when schedulable
  step with Sched.sched.is_schedulable.spec' as ⟨b1, b1_post⟩
  rw [schedulable_eq hX3.1.toN hX3.2.2.1 ht] at b1_post
  have hmid : (if b1 = true then sched.possible_switch_to st s3 t else ok s3) ⦃ s5 => ∃ σ5,
      (Fl4Spec.NonDet.when (Fl4Spec.schedulable t.bv σ3 = true) (Fl4Spec.possibleSwitchTo t.bv)) σ3 =
        ({((), σ5)}, False) ∧ IRel st th cr N T C E R B c s5 σ5 ∧ IFrame (L := L) th s3 s5 ∧
        FinStep (st := st) T N C c s3 σ3 s5 σ5 ⦄ := by
    rw [b1_post]
    by_cases e : Fl4Spec.schedulable t.bv σ3 = true
    · simp only [e, ↓reduceIte, Fl4Spec.NonDet.when]
      refine WP.spec_mono (WP.spec_and (switch_top hP0 s3 σ3 hX3.1 hX3.2 hA3 t ht)
        (possible_switch_to_sfootI hX3.1.toN hX3.2.2.1 hA3 ht)) ?_
      rintro s5 ⟨⟨σ5, hps, hk5, hf5, hv5, hS5⟩, hw5⟩
      exact ⟨σ5, hps, ⟨hX3.1.frame hP0 hf5 hv5, hS5⟩, IRel.iframe_of hX3 hw5 fun b hb => sfootI_oobj hP.tcb hb,
        ⟨hw5.mono fun b hb => SFootI.finW hP.tcb hb, SzKeepC.of (SzKeep.of_kheap hk5)⟩⟩
    · simp only [e, Bool.false_eq_true, ↓reduceIte, Fl4Spec.NonDet.when, WP.spec_ok]
      exact ⟨σ3, rfl, hX3, IFrame.refl _ _, FinStep.refl _ _⟩
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
  refine ⟨trivial, hd, σ6, ?_, hX6, ((hSS2.trans hSS3).trans hSS5).trans hSS6,
    ((hTW2.trans hTW3).trans hTW5).trans hTW6⟩
  rw [hspec]
  unfold specWakeTail
  rw [nd_bind_one hd, nd_gets_bind, nd_bind_one hw5]
  exact hu

set_option maxHeartbeats 8000000 in
/-- **A waiting notification signalled on `IRel`** (module docstring): its
head `d` dequeued and woken, without SC donation (`NoDon`). -/
theorem send_signal_wait_irel (hP0 : IPlaced N T E R B) (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hX : IRel st th cr N T C E R B c s σ) (hI : Inv σ) {n : U64} (hn : n ∈ N)
    {x : Fl4Spec.Notification} (hk : σ.kheap n.bv = some (.notification x)) {q : List Fl4Spec.ObjRef}
    (hw : x.ntfnObj = .waitingNtfn q)
    (hbl : ∀ u ∈ Fl4Spec.ntfnQueueOf x, ∃ xu, σ.kheap u = some (.tcb xu) ∧
      xu.tcbState = .blockedOnNotification n.bv)
    (hND : ∀ d l, q = d :: l → NoDon C σ d n.bv) (badge : U64) :
    notification.send_signal st ar s a n badge ⦃ r => r.2 = a ∧ ∃ (d : U64) (xd : Fl4Spec.Tcb) (σ' : Fl4Spec.State Unit),
      d.bv ∈ Fl4Spec.ntfnQueueOf x ∧ σ.kheap d.bv = some (.tcb xd) ∧ xd.tcbState = .blockedOnNotification n.bv ∧
      Fl4Spec.maybeDonateSc (Z := Unit) d.bv n.bv
          (wakeSt3 (updK σ n.bv (.notification (afterDequeue x d))) d.bv xd badge.bv) =
        ({((), wakeSt3 (updK σ n.bv (.notification (afterDequeue x d))) d.bv xd badge.bv)}, False) ∧
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
  have hA3 : ActReady (wakeSt3 σ1 d.bv xd badge.bv) := (wake_inv3 hI1 hk1 hxs badge.bv).actReady
  have hND1 : NoDon C σ1 d.bv n.bv := by
    intro xt xn e1 e2
    rw [hk1] at e1; cases e1
    simp only [hσ1, updK, Function.update_self, Option.some.injEq, Fl4Spec.KernelObject.notification.injEq] at e2
    subst e2
    rcases hND d.bv _ rfl xd x hkd hk with h | h | ⟨cq, hcq, h3', y, k, hky, hyt⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · have hcn : cq.bv ≠ n.bv := by intro e; rw [e, hk] at hky; cases hky
      exact Or.inr (Or.inr ⟨cq, hcq, h3', y, k, by
        simp only [hσ1, updK, Function.update_of_ne hcn]; exact hky, hyt⟩)
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
  refine WP.spec_mono (wake_irel hP0 s1 a σ1 ⟨hR1, hS1⟩ hdT hn hk1 hdn hq1 hqE badge hA3 hND1) ?_
  rintro r ⟨hra, hdon, σ', hsw', hX', hSS', hTW'⟩
  exact ⟨hra, d, xd, σ', hmem, hkd, hxs, hdon, by rw [hspec]; exact hsw', by rw [hsw']; exact Set.mem_singleton _,
    hX', hSS1.trans hSS', hTW1.trans hTW'⟩

end

end

end Fl4Proofs.P3.Ipc
