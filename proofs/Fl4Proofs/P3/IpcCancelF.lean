/-
P3 (DESIGN.md §9), IPC: **`cancel_ipc` of a thread blocked sending or on a
notification, on `IRel`, with its footprint** `CnW` (IpcSignalBound), toward
`JAtZ.suspendJ`'s `hSd`/`hNt` (XTopJointSuspend; the J side is XTopJointCancel).

* `cancel_ipc_sendF`: IpcCancelAll's `cancel_ipc_sendI` with the footprint
  (as `cancel_ipc_recvF` without the reply): the fault word, `ep_dequeue`'s
  endpoint words and the waiters' links, `set_thread_state`'s `SFoot`.
* `cancel_ipc_ntfnF`: IpcCancelAll's `cancel_ipc_ntfnI` with the footprint:
  the fault word, `ntfn_dequeue`'s `NWrite` (`NWrite.finW`),
  `set_thread_state`'s `SFoot`.
-/
import Fl4Proofs.P3.IpcSignalBound
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Ipc
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Sched

noncomputable section

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]
variable {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

set_option maxHeartbeats 8000000 in
/-- **`cancel_ipc` of a thread blocked on a send, with its footprint**
(module docstring). -/
theorem cancel_ipc_sendF (hP0 : IPlaced N T E R B) (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hX : IRel st th cr N T C E R B c s σ) {t : U64} (ht : t ∈ T) {x : Fl4Spec.Tcb}
    (hk : σ.kheap t.bv = some (.tcb x)) {e : Fl4Spec.ObjRef} {d : Fl4Spec.SenderPayload}
    (hst : x.tcbState = .blockedOnSend e d)
    (hz : ∃ z, σ.kheap e = some (.endpoint z) ∧ t.bv ∈ z.epQueue) (heE : L.mem s (tBlockA t) ∈ E) :
    ipc.cancel_ipc st ar s a t ⦃ r => r.2 = a ∧ ∃ σ', Fl4Spec.cancelIpc (Z := Unit) t.bv σ = ({((), σ')}, False) ∧
      IRel st th cr N T C E R B c r.1 σ' ∧ WritesIn st s r.1 (CnW (st := st) T N C E R c s σ) ⦄ := by
  have hP := hP0.e
  have hH := ipcCore_top (st := st) (th := th) (cr := cr) (N := N) (C := C) (c := c) hP
  obtain ⟨hR, hSR⟩ := hX
  have hta := hP.tcb t ht
  obtain ⟨x0, hk0, hx⟩ := hR.tcb t ht
  rw [hk] at hk0; injection hk0 with hk0; injection hk0 with hk0; subst hk0
  have hevb : (L.mem s (tBlockA t)).bv = e := hx.blkE e (by simp [Fl4Spec.epBlocked, hst])
  subst hevb
  set ev := L.mem s (tBlockA t) with hev
  obtain ⟨z, hkz, hqz⟩ := hz
  -- clearing the fault
  set s1 := L.wr s (tFaultA t) 0#u64 with hs1
  set x1 : Fl4Spec.Tcb := { x with tcbFault := none } with hx1
  set σ1 := updK σ t.bv (.tcb x1) with hσ1
  have hR1 : IpcRel N T E R B (L.mem s1) σ1 := fault_clear_ipc hP0 hR ht hk
  have hS1 := fault_clear_top hSR ht hk
  have hfa := a_fault hta
  have g : ∀ w, Aligned w → w.val ≠ t.val + 3376 → L.mem s1 w = L.mem s w :=
    fun w hw hne => rd_wr_ne hfa.1 hw (fun e => hne (by rw [← e, val_fault hta]))
  have hW1 : WritesIn st s s1 (fun b => b.val = t.val + 3376) :=
    ⟨L.ksb_wr _ _ _, L.cpu_wr _ _ _, fun b hb hn => g b hb hn⟩
  have hk1 : σ1.kheap t.bv = some (.tcb x1) := by simp [hσ1, updK]
  have hte : t.bv ≠ ev.bv := by intro h; rw [h, hkz] at hk; cases hk
  have hkz1 : σ1.kheap ev.bv = some (.endpoint z) := by simp [hσ1, updK, Ne.symm hte, hkz]
  have hts : Fl4Spec.threadSet (Z := Unit) (fun tcb => { tcb with tcbFault := none }) t.bv σ =
      ({((), σ1)}, False) := threadSet_eq _ hk
  have hw4 : L.mem s1 (P1.stA t) = sched.TS_BLOCKED_ON_SEND := by
    rw [P1.stA_eq, ← tStA_eq, g _ (a_st hta).1 (by rw [val_st hta]; omega)]
    have h3 := hx.st
    rw [hst] at h3
    apply UScalar.eq_of_val_eq
    rw [h3, tsVals.2.2.2.1]; rfl
  have hb1 : L.mem s1 (tBlockA t) = ev := g _ (a_blk hta).1 (by rw [val_blk hta]; omega)
  have hSR' : sched.TS_BLOCKED_ON_SEND ≠ sched.TS_BLOCKED_ON_RECV := by
    rw [tsVals.2.2.1, tsVals.2.2.2.1]; decide
  -- the footprint, back to the start
  have hks1 : L.ksb s1 = L.ksb s := L.ksb_wr _ _ _
  have fin : ∀ s4 : S, ∀ W : U64 → Prop, WritesIn st s s4 W →
      (∀ b, W b → CnW (st := st) T N C E R c s σ b) → WritesIn st s s4 (CnW (st := st) T N C E R c s σ) :=
    fun _ _ h hm => h.mono hm
  have cF : ∀ b, b.val = t.val + 3376 → CnW (st := st) T N C E R c s σ b := fun b hb =>
    Or.inl (Or.inr ⟨t, ht, 3376, by omega, by omega, by omega, by omega, by omega, hb⟩)
  have cS : ∀ (s' : S), L.ksb s' = L.ksb s → ∀ b, SFoot st T c s' b → CnW (st := st) T N C E R c s σ b :=
    fun s' hk' b hb => Or.inl (Or.inl (KFoot.of_sfoot ((SFoot.ksb hk').1 hb)))
  have cE : ∀ (xs : List U64), (∀ w ∈ xs, w ∈ T) → ∀ b, (EW ev b ∨ ∃ w ∈ xs, TL w b) →
      CnW (st := st) T N C E R c s σ b := by
    intro xs hxs b hb
    rcases hb with h | ⟨w, hw, h | h⟩
    · exact Or.inr (Or.inl ⟨ev, heE, h⟩)
    · exact Or.inl (Or.inr ⟨w, hxs w hw, 3496, by omega, by omega, by omega, by omega, by omega, h⟩)
    · exact Or.inl (Or.inr ⟨w, hxs w hw, 3504, by omega, by omega, by omega, by omega, by omega, h⟩)
  unfold ipc.cancel_ipc faults.clear_fault
  step with Fl4Proofs.P1.obj.Tcb.set_fault_type.spec as ⟨s1', hs1'⟩
  have e1 : s1' = s1 := by rw [hs1']; unfold fl4_abi.consts.fault.NullFault; rfl
  subst e1
  step with Fl4Proofs.P1.obj.Tcb.state.spec as ⟨w, hw⟩
  rw [hw, hw4, if_pos rfl]
  step with Fl4Proofs.P1.obj.Tcb.block_obj.spec as ⟨ep, hep⟩
  have hep' : ep = ev := by rw [hep]; exact hb1
  subst hep'
  obtain ⟨xs, hQ, hxs, -⟩ := (hR1.toE.at_ep heE hkz1).queue
  have hdx : t ∈ xs := by
    rw [hxs, List.mem_map] at hqz
    obtain ⟨y, hy, ey⟩ := hqz
    rw [← eq_of_bv ey]; exact hy
  refine WP.spec_bind (WP.spec_and (ep_dequeue_c hH hP0 hP s1 σ1 hR1.toE (IpcRel.toSRN hR1 hS1) heE hkz1 hqz)
    (ep_dequeue_full hP s1 heE t xs hQ hdx)) ?_
  rintro s2 ⟨⟨hdq, hR2, hS2, hA2⟩, -, -, hQA, hWE, -, -⟩
  have hW2 : WritesIn st s1 s2 (fun b => EW ev b ∨ ∃ w ∈ xs, TL w b) :=
    ⟨hWE.1, hWE.2.1, fun b hb hn => hQA b hb ⟨fun h => hn (Or.inl h), fun h => hn (Or.inr h)⟩⟩
  have hks2 : L.ksb s2 = L.ksb s := hWE.1.trans hks1
  set σ2 := updK σ1 ev.bv (.endpoint (epDeq z t.bv)) with hσ2
  have hk2 : σ2.kheap t.bv = some (.tcb x1) := by simp [hσ2, updK, hte, hk1]
  have hb2 : L.mem s2 (tBlockA t) = ev := (hA2 _ (a_blk hta).1 ⟨t, ht, (a_blk hta).2⟩).trans hb1
  have hq2 : ∀ e ∈ E, ∀ z', σ2.kheap e.bv = some (.endpoint z') → t.bv ∉ z'.epQueue :=
    dequeued_not_queued hR2 heE hb2 (x := epDeq z t.bv) (by simp [hσ2, updK]) (epDeq_not_mem _)
  have hW02 : WritesIn st s s2 (CnW (st := st) T N C E R c s σ) :=
    fin _ _ (hW1.trans hW2) fun b hb => hb.elim (cF b) (cE xs hQ.mem b)
  rw [if_neg hSR']
  simp only [bind_ok]
  refine WP.spec_bind (WP.spec_and (set_thread_state_c hH hP0 hP s2 σ2 hR2 hS2 ht hk2 hq2
    (by simp [hx1, hst, tsCode]) .inactive (by simp [tsCode]) sched.TS_INACTIVE (by unfold sched.TS_INACTIVE; rfl))
    (set_thread_state_sfoot (IpcRel.ofSRN hR2 hS2).2.2.1 ht sched.TS_INACTIVE)) ?_
  rintro s4 ⟨⟨hR4, hS4⟩, hW4⟩
  simp only [WP.spec_ok]
  refine ⟨trivial, _, ?_, IpcRel.ofSRN hR4 hS4, ?_⟩
  · unfold Fl4Spec.cancelIpc
    rw [nd_bind_one (getThreadState_eq hk), nd_bind_one hts, hst]
    show Fl4Spec.blockedCancelIpc (Z := Unit) (.blockedOnSend ev.bv d) t.bv none σ1 = _
    unfold Fl4Spec.blockedCancelIpc Fl4Spec.getBlockingObject
    rw [nd_bind_one (show Fl4Spec.NonDet.assertOpt (σ := Fl4Spec.State Unit)
      (Fl4Spec.epBlocked (.blockedOnSend ev.bv d)) σ1 = ({(ev.bv, σ1)}, False) from rfl), nd_bind_one hdq]
    dsimp only
    rw [Notif.setThreadState_eq _ hk2]
  · refine fin _ _ (hW02.trans hW4) fun b hb => ?_
    rcases hb with hb | hb
    · exact hb
    · exact cS _ hks2 b hb

set_option maxHeartbeats 8000000 in
/-- **`cancel_ipc` of a thread blocked on a notification, with its
footprint** (module docstring). -/
theorem cancel_ipc_ntfnF (hP0 : IPlaced N T E R B) (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hX : IRel st th cr N T C E R B c s σ) {t : U64} (ht : t ∈ T) {x : Fl4Spec.Tcb}
    (hk : σ.kheap t.bv = some (.tcb x)) {n0 : Fl4Spec.ObjRef} (hst : x.tcbState = .blockedOnNotification n0)
    (hz : ∃ xn, σ.kheap n0 = some (.notification xn) ∧ t.bv ∈ Fl4Spec.ntfnQueueOf xn)
    (hnN : L.mem s (tBlockA t) ∈ N) :
    ipc.cancel_ipc st ar s a t ⦃ r => r.2 = a ∧ ∃ σ', Fl4Spec.cancelIpc (Z := Unit) t.bv σ = ({((), σ')}, False) ∧
      IRel st th cr N T C E R B c r.1 σ' ∧ WritesIn st s r.1 (CnW (st := st) T N C E R c s σ) ⦄ := by
  have hP := hP0.e
  have hta := hP.tcb t ht
  obtain ⟨hR, hSRT⟩ := hX
  obtain ⟨x0, hk0, hx⟩ := hR.tcb t ht
  rw [hk] at hk0; injection hk0 with hk0; injection hk0 with hk0; subst hk0
  have hnb : (L.mem s (tBlockA t)).bv = n0 := hx.blkN n0 hst
  subst hnb
  set n := L.mem s (tBlockA t) with hn
  obtain ⟨xn, hkn, hqn⟩ := hz
  -- clearing the fault
  set s1 := L.wr s (tFaultA t) 0#u64 with hs1
  set x1 : Fl4Spec.Tcb := { x with tcbFault := none } with hx1
  set σ1 := updK σ t.bv (.tcb x1) with hσ1
  have hR1 : IpcRel N T E R B (L.mem s1) σ1 := fault_clear_ipc hP0 hR ht hk
  have hS1 : SRT st th cr N T C E R B c (SRE st N T C E R B c) s1 σ1 := fault_clear_top hSRT ht hk
  have hfa := a_fault hta
  have g : ∀ w, Aligned w → w.val ≠ t.val + 3376 → L.mem s1 w = L.mem s w :=
    fun w hw hne => rd_wr_ne hfa.1 hw (fun e => hne (by rw [← e, val_fault hta]))
  have hW1 : WritesIn st s s1 (fun b => b.val = t.val + 3376) :=
    ⟨L.ksb_wr _ _ _, L.cpu_wr _ _ _, fun b hb hn => g b hb hn⟩
  have hk1 : σ1.kheap t.bv = some (.tcb x1) := by simp [hσ1, updK]
  have htn : t.bv ≠ n.bv := by intro h; rw [h, hkn] at hk; cases hk
  have hkn1 : σ1.kheap n.bv = some (.notification xn) := by simp [hσ1, updK, Ne.symm htn, hkn]
  have hts : Fl4Spec.threadSet (Z := Unit) (fun tcb => { tcb with tcbFault := none }) t.bv σ =
      ({((), σ1)}, False) := threadSet_eq _ hk
  have hw6 : L.mem s1 (P1.stA t) = sched.TS_BLOCKED_ON_NTFN := by
    rw [P1.stA_eq, ← tStA_eq, g _ (a_st hta).1 (by rw [val_st hta]; omega)]
    have h3 := hx.st
    rw [hst] at h3
    apply UScalar.eq_of_val_eq
    rw [h3, tsVals.2.2.2.2]; rfl
  have hb1 : L.mem s1 (tBlockA t) = n := g _ (a_blk hta).1 (by rw [val_blk hta]; omega)
  have h64 : sched.TS_BLOCKED_ON_NTFN ≠ sched.TS_BLOCKED_ON_SEND := by
    rw [tsVals.2.2.2.2, tsVals.2.2.2.1]; decide
  have h63 : sched.TS_BLOCKED_ON_NTFN ≠ sched.TS_BLOCKED_ON_RECV := by
    rw [tsVals.2.2.2.2, tsVals.2.2.1]; decide
  -- the footprint, back to the start
  have hks1 : L.ksb s1 = L.ksb s := L.ksb_wr _ _ _
  have cF : ∀ b, b.val = t.val + 3376 → CnW (st := st) T N C E R c s σ b := fun b hb =>
    Or.inl (Or.inr ⟨t, ht, 3376, by omega, by omega, by omega, by omega, by omega, hb⟩)
  have cS : ∀ (s' : S), L.ksb s' = L.ksb s → ∀ b, SFoot st T c s' b → CnW (st := st) T N C E R c s σ b :=
    fun s' hk' b hb => Or.inl (Or.inl (KFoot.of_sfoot ((SFoot.ksb hk').1 hb)))
  have cN : ∀ b, NWrite N T b → CnW (st := st) T N C E R c s σ b := fun b hb =>
    Or.inl (NWrite.finW hP.tcb hb)
  -- the queue of `n`
  have hx2 := hR1.toN.at_ntfn hnN hkn1
  obtain ⟨xs, hQ, hxs, hB⟩ := hx2.obj.queue
  have htxs : t ∈ xs := by
    have : t.bv ∈ xn.ntfnObj.ntfnQueue := hqn
    rw [hxs] at this; obtain ⟨y, hy, ey⟩ := List.mem_map.1 this; rw [← eq_of_bv ey]; exact hy
  have hnd := hQ.nodup
  unfold ipc.cancel_ipc faults.clear_fault
  step with Fl4Proofs.P1.obj.Tcb.set_fault_type.spec as ⟨s1', hs1'⟩
  have e1 : s1' = s1 := by rw [hs1']; unfold fl4_abi.consts.fault.NullFault; rfl
  subst e1
  step with Fl4Proofs.P1.obj.Tcb.state.spec as ⟨w, hw⟩
  rw [hw, hw6, if_neg h64, if_neg h63, if_pos rfl]
  step with Fl4Proofs.P1.obj.Tcb.block_obj.spec as ⟨i, hi⟩
  have hi' : i = n := by rw [hi]; exact hb1
  subst hi'
  unfold notification.cancel_signal
  simp only [Std.bind_assoc]
  refine WP.spec_bind (ntfn_dequeue_full hP0.n s1 hnN t xs hQ htxs) ?_
  rintro s2 ⟨hA1, hA2, hA3⟩
  have hks2 : L.ksb s2 = L.ksb s := hA3.foot.1.trans hks1
  have hW02 : WritesIn st s s2 (CnW (st := st) T N C E R c s σ) :=
    (hW1.trans hA3.foot).mono fun b hb => hb.elim (cF b) (cN b)
  obtain ⟨q', hq'⟩ : ∃ q', Fl4Spec.removeAll t.bv (Fl4Spec.ntfnQueueOf xn) = q' := ⟨_, rfl⟩
  have hrm : q' = (xs.erase t).map UScalar.bv := by
    rw [← hq']; show Fl4Spec.removeAll t.bv xn.ntfnObj.ntfnQueue = _; rw [hxs]; exact removeAll_map hnd t
  set xn' : Fl4Spec.Notification :=
    { xn with ntfnObj := if q' = [] then Fl4Spec.Ntfn.idleNtfn else Fl4Spec.Ntfn.waitingNtfn q' } with hxn'
  have hdeq : Fl4Spec.tcbNtfnDequeue (Z := Unit) t.bv n.bv σ1 = ({((), updK σ1 n.bv (.notification xn'))}, False) := by
    rw [tcbNtfnDequeue_eq hkn1 hqn, hq', hxn']
    cases q' <;> simp [Fl4Spec.ntfnObjUpdate]
  set σ2 := updK σ1 n.bv (.notification xn') with hσ2
  have hbw : ∀ w ∈ xs, w ∈ T ∧ L.mem s1 (tBlockA w) = n := fun w hw => ⟨hQ.mem w hw, (hB w hw).2⟩
  have hR2 : IpcRel N T E R B (L.mem s2) σ2 := by
    refine hR1.upd_ntfn hP0 hnN _ (fun b hb ⟨_, hnw, hnl⟩ => hA3.agree b hb
        (fun w hw => by
          obtain ⟨hwT, hwb⟩ := hbw w hw
          have hwa := hP.tcb w hwT
          exact ⟨fun e => hnl ⟨w, hwT, hwb, Or.inl (by rw [e, val_next hwa])⟩,
            fun e => hnl ⟨w, hwT, hwb, Or.inr (by rw [e, val_prev hwa])⟩⟩)
        (fun e => hnw (e ▸ (nw_words hP0 hnN).1)) (fun e => hnw (e ▸ (nw_words hP0 hnN).2.1)))
      ⟨?_, ?_, ?_, ?_⟩
    · show NtfnObjRel _ T n (if q' = [] then Fl4Spec.Ntfn.idleNtfn else Fl4Spec.Ntfn.waitingNtfn q')
      by_cases hemp : xs.erase t = []
      · have : q' = [] := by rw [hrm, hemp]; rfl
        rw [if_pos this]
        rw [hemp] at hA1
        exact ⟨by rw [hA2, if_pos hemp], hA1⟩
      · have hne : q' ≠ [] := by rw [hrm]; simpa using hemp
        rw [if_neg hne]
        have hstn : stOf (L.mem s1) n = 1#u64 := by
          have := hx2.obj
          cases h : xn.ntfnObj with
          | idleNtfn => rw [h] at hxs; simp [Fl4Spec.Ntfn.ntfnQueue] at hxs; subst hxs; simp at htxs
          | activeNtfn b => rw [h] at hxs; simp [Fl4Spec.Ntfn.ntfnQueue] at hxs; subst hxs; simp at htxs
          | waitingNtfn q => rw [h] at this; exact this.1
        refine ⟨by rw [hA2, if_neg hemp]; exact hstn, xs.erase t, hemp, hrm, hA1, fun y hy => ?_⟩
        have hyx := List.mem_of_mem_erase hy
        have e := hA3.tcb y (hQ.mem y hyx)
        exact ⟨by rw [e.st]; exact (hB y hyx).1, by rw [e.blk]; exact (hB y hyx).2⟩
    · show xn.ntfnBoundTcb = _; rw [hA3.bound]; exact hx2.bound
    · rw [hA3.bound]; exact hx2.bound_mem
    · show xn.ntfnSc = _; rw [hA3.sc]; exact hx2.sc
  have hK := NtfnStep.ntfn (y := xn') hkn1 rfl rfl
  have hS2 : SRT st th cr N T C E R B c (SRE st N T C E R B c) s2 σ2 :=
    ⟨hS1.1.stableN hS1.2.1.placed hA3.foot hK, hS1.2.1.stable hA3.foot hK,
      hS1.2.2.mono hA3.foot.1 (SzKeep.ntfnStep hK)⟩
  have hk2 : σ2.kheap t.bv = some (.tcb x1) := by simp [hσ2, updK, htn, hk1]
  have hb2 : (L.mem s2 (tStA t)).val = 6 := by
    rw [(hA3.tcb t ht).st, g _ (a_st hta).1 (by rw [val_st hta]; omega), hx.st, hst]; rfl
  have hq2 : ∀ e ∈ E, ∀ z', σ2.kheap e.bv = some (.endpoint z') → t.bv ∉ z'.epQueue :=
    Notif.IpcRel.not_ep_queued hR2 (by rw [hb2]; omega)
  have hqn2 : ∀ n' ∈ N, ∀ z', σ2.kheap n'.bv = some (.notification z') → t.bv ∉ z'.ntfnObj.ntfnQueue := by
    intro n' hn' z' hz' hm
    by_cases e : n' = n
    · subst e
      simp [hσ2, updK] at hz'; subst hz'
      change t.bv ∈ (if q' = [] then Fl4Spec.Ntfn.idleNtfn else Fl4Spec.Ntfn.waitingNtfn q').ntfnQueue at hm
      by_cases hq2 : q' = []
      · rw [if_pos hq2] at hm; simp [Fl4Spec.Ntfn.ntfnQueue] at hm
      · rw [if_neg hq2] at hm; simp only [Fl4Spec.Ntfn.ntfnQueue] at hm
        rw [hrm, mem_map_bv] at hm
        exact hnd.not_mem_erase hm
    · obtain ⟨z0, hz0, hzr⟩ := hR2.toN.ntfn n' hn'
      rw [hz'] at hz0; cases hz0
      obtain ⟨ys, -, hys, hBy⟩ := hzr.obj.queue
      rw [hys, mem_map_bv] at hm
      have hb := (hBy t hm).2
      have hbt : L.mem s2 (tBlockA t) = n := by rw [(hA3.tcb t ht).blk, hb1]
      exact e (hb.symm.trans hbt)
  have hX2 : IRel st th cr N T C E R B c s2 σ2 := ⟨hR2, hS2⟩
  refine WP.spec_bind (WP.spec_and (set_thread_state_cq (ipcCore_top hP) hP0 hP s2 σ2 hR2.toE
    (IpcRel.toSRN hR2 hS2) ht hk2 hq2 hqn2 .inactive (by simp [tsCode]) sched.TS_INACTIVE
    (by unfold sched.TS_INACTIVE; rfl)) (set_thread_state_sfoot hX2.2.2.1 ht sched.TS_INACTIVE)) ?_
  rintro s4 ⟨⟨hR4, hS4⟩, hW4⟩
  simp only [WP.spec_ok]
  refine ⟨trivial, _, ?_, IpcRel.ofSRN hR4 hS4, ?_⟩
  · unfold Fl4Spec.cancelIpc
    rw [nd_bind_one (getThreadState_eq hk), nd_bind_one hts, hst]
    show Fl4Spec.cancelSignal (Z := Unit) t.bv n.bv σ1 = _
    unfold Fl4Spec.cancelSignal
    rw [nd_bind_one hdeq]
    exact Notif.setThreadState_eq .inactive hk2
  · refine (hW02.trans hW4).mono fun b hb => ?_
    rcases hb with hb | hb
    · exact hb
    · exact cS _ hks2 b hb

end

end

end Fl4Proofs.P3.Ipc
