/-
P3 (DESIGN.md §9), IPC: **the blocking `receive_signal` on the merged
relation** (NtfnBlock.lean with `IpcRel`, `IpcSchedHyps` and `IpcRecvHyps`).
The receiver is in no endpoint queue (`hqE`), so writing its state and block
words keeps the endpoint part; `ntfn_append` writes only the notification's
queue words and the links of TCBs blocked on it (`QKeeps.agree`).
-/
import Fl4Proofs.P3.IpcNtfnRecv
import Fl4Proofs.P3.NtfnBlock
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Notif
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc

noncomputable section

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st] {N T E R : Set U64}
  {B : Set (U64 × Fl4Spec.Word)} {SR : S → Fl4Spec.State Unit → Prop}

/-- **Blocking receive** on an idle or waiting notification. -/
theorem receive_signal_blockI (hH : IpcSchedHyps st ar N T E R B SR) (hV : IpcRecvHyps st ar N T E R B SR)
    (hP : IPlaced N T E R B)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (hR : IpcRel N T E R B (L.mem s) σ) (hSR : SR s σ)
    {t : U64} (ht : t ∈ T) {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt))
    (hnb : ∀ m, xt.tcbState ≠ .blockedOnNotification m)
    (hqE : ∀ e ∈ E, ∀ z, σ.kheap e.bv = some (.endpoint z) → t.bv ∉ z.epQueue)
    {n : U64} (hn : n ∈ N) {x : Fl4Spec.Notification} (hk : σ.kheap n.bv = some (.notification x))
    (hna : ∀ b, x.ntfnObj ≠ .activeNtfn b)
    (hsort : ∀ xs, QueueRel (L.mem s) T .Ep (qOf (L.mem s) n) xs → PrioSorted (fun y => L.mem s (prioA y)) xs)
    (cb : Fl4Spec.Badge) (cr : Fl4Spec.CapRights) (hAR : ActReady σ) (hNQ : NotQueued σ t.bv)
    (hRB : RelIfBound σ t.bv) (hsane : ∀ u, σ.schedulerAction = .switchThread u → u ≠ t.bv)
    (hnidle : t.bv ≠ σ.idleThread) :
    notification.receive_signal st ar s a t n true ⦃ r =>
      ¬ (Fl4Spec.receiveSignal t.bv (.notificationCap n.bv cb cr) true σ).2 ∧
      ∃ σ', ((), σ') ∈ (Fl4Spec.receiveSignal t.bv (.notificationCap n.bv cb cr) true σ).1 ∧
        IpcRel N T E R B (L.mem r.1) σ' ∧ SR r.1 σ' ⦄ := by
  have hx := hR.toN.at_ntfn hn hk
  have hta := hP.e.tcb t ht
  obtain ⟨xt', hkx, hxt⟩ := hR.tcb t ht
  rw [hkt] at hkx; injection hkx with hkx; injection hkx with hkx; subst hkx
  have hnm := not_member hR.toN ht hkt hnb
  -- the queue
  obtain ⟨xs, hQ, hxs, hB, hst⟩ : ∃ xs, QueueRel (L.mem s) T .Ep (qOf (L.mem s) n) xs ∧
      x.ntfnObj.ntfnQueue = xs.map UScalar.bv ∧ (∀ y ∈ xs, BlockedOn (L.mem s) n y) ∧
      (stOf (L.mem s) n = obj.NTFN_IDLE ∨ stOf (L.mem s) n = obj.NTFN_WAITING) := by
    have := hx.obj
    cases h : x.ntfnObj with
    | idleNtfn =>
      rw [h] at this
      exact ⟨[], this.2, rfl, by simp, Or.inl (stOf_idle (T := T) (h ▸ hx.obj) rfl)⟩
    | waitingNtfn q =>
      rw [h] at this
      obtain ⟨h1, xs, -, rfl, h2, h3⟩ := this
      exact ⟨xs, h2, rfl, h3, Or.inr (stOf_waiting (T := T) (h ▸ hx.obj) rfl)⟩
    | activeNtfn b => exact absurd h (hna b)
  have htxs : t ∉ xs := fun h => hnm n hn x hk (by rw [hxs]; exact List.mem_map_of_mem h)
  have hsorted := hsort xs hQ
  -- step 1: the state and block-object words
  set x1 : Fl4Spec.Tcb := { xt with tcbState := .blockedOnNotification n.bv }
  set σ1 := updK σ t.bv (.tcb x1)
  set s2 := L.wr (L.wr s (tStA t) sched.TS_BLOCKED_ON_NTFN) (tBlockA t) n
  obtain ⟨hw1, hoth1⟩ := twr_wr (st := st) hP.n ht (K := 3328#u64) (Or.inl rfl) s sched.TS_BLOCKED_ON_NTFN
  obtain ⟨hw2, hoth2⟩ := twr_wr (st := st) hP.n ht (K := 3336#u64) (Or.inr (Or.inl rfl))
    (L.wr s (tStA t) sched.TS_BLOCKED_ON_NTFN) n
  rw [← tStA_eq] at hw1 hoth1
  rw [← tBlockA_eq] at hw2 hoth2
  have hw := hw1.trans hw2
  have hsa := (a_st hta).1
  have hba := (a_blk hta).1
  have hstv := val_st hta
  have hbl := val_blk hta
  have two : ∀ b, Aligned b → b.val ≠ t.val + 3328 → b.val ≠ t.val + 3336 → L.mem s2 b = L.mem s b := by
    intro b hb h1 h2
    show L.mem (L.wr (L.wr s _ _) _ _) b = _
    rw [wr_agree (st := st) hba b hb (by rw [hbl]; exact h2), wr_agree (st := st) hsa b hb (by rw [hstv]; exact h1)]
  have hR1 : IpcRel N T E R B (L.mem s2) σ1 := by
    refine hR.upd_tcb hP ht _ (fun b hb ⟨_, hnt⟩ => two b hb
      (fun e => hnt (Or.inl (TF.of_val (a_st hta).2 (by rw [e, hstv]))))
      (fun e => hnt (Or.inl (TF.of_val (a_blk hta).2 (by rw [e, hbl]))))) (Or.inl ⟨hnm, hqE⟩) ?_
    refine TcbRel.of_words hta hxt _ (fun b hb _ hv => two b hb (fun e => hv (Or.inl e))
        (fun e => hv (Or.inr (Or.inl e))))
      ?_ (fun e h => by cases h) (fun m hm => ?_) (Or.inr (by simp [NoEpPayload])) (fun r => ?_) rfl rfl rfl rfl
    · show (L.mem s2 (tStA t)).val = 6
      show (L.mem (L.wr (L.wr s _ _) _ _) _).val = 6
      rw [wr_agree (st := st) hba _ hsa (by rw [hbl, hstv]; omega), rd_wr_eq hsa, six_val]
    · cases hm
      show (L.mem s2 (tBlockA t)).bv = n.bv
      rw [rd_wr_eq hba]
    · rw [two _ (a_reg hta r).1 (by rw [regA_val hta (regIdx_lt r)]; have := regIdx_lt r; omega)
        (by rw [regA_val hta (regIdx_lt r)]; have := regIdx_lt r; omega)]
      exact hxt.regs r
  have hSR1 := hH.block _ _ _ _ t hSR hNQ hRB hsane hnidle hw.foot (NtfnStep.tcb hkt (.blockedOnNotification n.bv) xt.tcbArch)
    (fun p x y h1 h2 hp => by
      simp only [Function.update_apply, hp, ↓reduceIte] at h2; rw [h1] at h2; cases h2; rfl)
  set σ2 := stsAct σ1 t.bv
  have hnt : n.bv ≠ t.bv := by intro e; rw [e, hkt] at hk; cases hk
  have hk2 : σ2.kheap n.bv = some (.notification x) := by simp [σ2, σ1, stsAct_kheap, hnt, hk]
  have hkt2 : σ2.kheap t.bv = some (.tcb x1) := by simp [σ2, σ1, stsAct_kheap]
  -- step 2: `schedule_tcb`
  have key : (do
      let s1 ← obj.Tcb.set_state st t s sched.TS_BLOCKED_ON_NTFN
      let s2 ← obj.Tcb.set_block_obj st t s1 n
      let s3 ← sched.schedule_tcb st s2 t
      let s4 ← notification.ntfn_append st s3 n t
      let s5 ← notification.maybe_return_sched_context st s4 n t
      ok (s5, a)) ⦃ r =>
      ¬ (Fl4Spec.receiveSignal t.bv (.notificationCap n.bv cb cr) true σ).2 ∧
      ∃ σ', ((), σ') ∈ (Fl4Spec.receiveSignal t.bv (.notificationCap n.bv cb cr) true σ).1 ∧
        IpcRel N T E R B (L.mem r.1) σ' ∧ SR r.1 σ' ⦄ := by
    step
    step
    subst s1_post s2_post
    refine WP.spec_bind (hH.scheduleTcb _ σ1 t hR1 hSR1 ht) ?_
    rintro s3 ⟨hf3, hS3⟩
    have hR3 : IpcRel N T E R B (L.mem s3) σ2 := hR1.frame hP hf3 (IKView.stsAct _ _)
    obtain ⟨xs3, hQ3, hxs3, hB3⟩ := (hR3.toN.at_ntfn hn hk2).obj.queue
    have e3 : xs3 = xs := by
      rw [hxs] at hxs3
      exact (List.map_injective_iff.2 (fun a b h => eq_of_bv h) hxs3).symm
    subst e3
    have hxt3 := hR3.toN.at_tcb ht hkt2
    -- priorities agree with those of `s`
    have hpr : ∀ y ∈ xs3, L.mem s3 (prioA y) = L.mem s (prioA y) := by
      intro y hy
      have hyT := hQ.mem y hy
      have hyt : y ≠ t := fun e => htxs (e ▸ hy)
      have hyA := hP.e.tcb y hyT
      exact (hf3 _ (a_prio hyA).1 (EFoot.ifoot (Or.inr (Or.inr (Or.inl ⟨y, hyT, Or.inl (a_prio hyA).2⟩))))).trans
        (hw.tcb y hyT hyt).prio
    have hsorted3 : PrioSorted (fun y => L.mem s3 (prioA y)) xs3 := prioSorted_congr hsorted hpr
    refine WP.spec_bind (ntfn_append_full hP.n s3 hn t xs3 hQ3 ht htxs) ?_
    rintro s4 ⟨hA1, hA2, hA3⟩
    set ys := insPrio (fun y => L.mem s3 (prioA y)) (L.mem s3 (prioA t)) t xs3
    have hblk3 : L.mem s3 (tBlockA t) = n := eq_of_bv (hxt3.blk n.bv rfl)
    have hR4 : IpcRel N T E R B (L.mem s4)
        (updK σ2 n.bv (.notification { x with ntfnObj := .waitingNtfn (ys.map UScalar.bv) })) := by
      have hx2 := hR3.toN.at_ntfn hn hk2
      have hbw : ∀ w ∈ t :: xs3, w ∈ T ∧ L.mem s3 (tBlockA w) = n := by
        intro w hw
        rcases List.mem_cons.1 hw with rfl | hw
        · exact ⟨ht, hblk3⟩
        · exact ⟨hQ.mem w hw, (hB3 w hw).2⟩
      refine hR3.upd_ntfn hP hn _ (fun b hb ⟨_, hnw, hnl⟩ => hA3.agree b hb
          (fun w hw => by
            obtain ⟨hwT, hwb⟩ := hbw w hw
            have hwa := hP.e.tcb w hwT
            exact ⟨fun e => hnl ⟨w, hwT, hwb, Or.inl (by rw [e, val_next hwa])⟩,
              fun e => hnl ⟨w, hwT, hwb, Or.inr (by rw [e, val_prev hwa])⟩⟩)
          (fun e => hnw (e ▸ (nw_words hP hn).1)) (fun e => hnw (e ▸ (nw_words hP hn).2.1)))
        ⟨?_, ?_, ?_, ?_⟩
      · refine ⟨hA2, ys, insPrio_ne_nil hsorted3, rfl, hA1, fun y hy => ?_⟩
        have hyT : y ∈ T := by
          rcases mem_insPrio_sorted hsorted3 hy with rfl | hy'
          · exact ht
          · exact hQ.mem y hy'
        have e := hA3.tcb y hyT
        rcases mem_insPrio_sorted hsorted3 hy with rfl | hy'
        · exact ⟨by rw [e.st, hxt3.st]; rfl, by rw [e.blk]; exact hblk3⟩
        · exact ⟨by rw [e.st]; exact (hB3 y hy').1, by rw [e.blk]; exact (hB3 y hy').2⟩
      · show x.ntfnBoundTcb = _; rw [hA3.bound]; exact hx2.bound
      · rw [hA3.bound]; exact hx2.bound_mem
      · show x.ntfnSc = _; rw [hA3.sc]; exact hx2.sc
    -- the spec
    have hq : ∀ y ∈ Fl4Spec.ntfnQueueOf x, ∃ z, σ2.kheap y = some (.tcb z) ∧ z.tcbPriority = prioOf σ2 y := by
      intro y hy
      have hy' : y ∈ x.ntfnObj.ntfnQueue := hy
      rw [hxs] at hy'
      obtain ⟨y', hy'x, rfl⟩ := List.mem_map.1 hy'
      obtain ⟨z, hz, -⟩ := hR3.toN.tcb y' (hQ.mem y' hy'x)
      exact ⟨z, hz, by simp [prioOf, hz]⟩
    have hlist : specIns (Fl4Spec.ntfnQueueOf x) (prioOf σ2) x1.tcbPriority t.bv = ys.map UScalar.bv := by
      have hq' : Fl4Spec.ntfnQueueOf x = xs3.map UScalar.bv := hxs
      rw [specIns, hq', List.takeWhile_map, List.dropWhile_map]
      simp only [ys, insPrio_eq_sorted _ _ t xs3 hsorted3, List.map_append, List.map_cons]
      have hc : ∀ y ∈ xs3, ((fun y => @decide (prioOf σ2 y ≥ x1.tcbPriority) (Classical.propDecidable _)) ∘
          UScalar.bv) y =
          (fun y => !decide (L.mem s3 (prioA t) > L.mem s3 (prioA y))) y := by
        intro y hy
        obtain ⟨z, hz, hzr⟩ := hR3.toN.tcb y (hQ.mem y hy)
        have hpz : prioOf σ2 y.bv = z.tcbPriority := by simp [prioOf, hz]
        simp only [Function.comp, hpz]
        convert (prio_ge_iff _ _ _ _ hxt3.prio hzr.prio).symm using 2
      rw [takeWhile_congr' hc, dropWhile_congr' hc]
    set σ3 := updK σ2 n.bv (.notification { x with ntfnObj := .waitingNtfn (ys.map UScalar.bv) })
    have hspec : Fl4Spec.receiveSignal (Z := Unit) t.bv (.notificationCap n.bv cb cr) true σ =
        Fl4Spec.maybeReturnSc n.bv t.bv σ3 := by
      rw [receiveSignal_notActive hk hna]
      unfold Fl4Spec.receiveSignalBlocked
      simp only [↓reduceIte]
      rw [nd_bind_one (setThreadState_eq _ hkt), nd_bind_one (tcbNtfnAppend_eq hk2 hkt2 (prioOf σ2) hq), hlist]
    rw [hspec]
    have hSR4 := hH.stableN _ _ _ _ hS3 hA3.foot
      (NtfnStep.ntfn (y := { x with ntfnObj := .waitingNtfn (ys.map UScalar.bv) }) hk2 rfl rfl)
      (NoBlock.ntfnUpd _ _ _)
    have hb : BlockStep σ σ3 t.bv n.bv := by
      refine ⟨?_, ?_, ?_, fun p h1 h2 => ?_,
        ⟨x, { x with ntfnObj := .waitingNtfn (ys.map UScalar.bv) }, hk, by simp [σ3, updK]⟩,
        ⟨xt, x1, hkt, by simp [σ3, updK, Ne.symm hnt, hkt2], rfl, rfl⟩⟩
      · show (stsAct σ1 t.bv).schedulerAction = σ.schedulerAction ∨
          (stsAct σ1 t.bv).schedulerAction = .chooseNewThread
        unfold stsAct; split_ifs
        · exact Or.inr rfl
        · exact Or.inl rfl
      · show (stsAct σ1 t.bv).curTime = σ.curTime
        unfold stsAct; split_ifs <;> rfl
      · show (stsAct σ1 t.bv).releaseQueue = σ.releaseQueue
        unfold stsAct; split_ifs <;> rfl
      · simp [σ3, σ2, σ1, updK, stsAct_kheap, h1, h2]
    have hid3 : σ3.idleThread = σ.idleThread := by
      show (stsAct σ1 t.bv).idleThread = _; unfold stsAct; split_ifs <;> rfl
    refine WP.spec_bind (hV.returnSc s4 σ σ3 t n hR4 hSR4 ht hn hAR hb (by rw [hid3]; exact hnidle)) ?_
    rintro s5 ⟨hnf, σ', hm, hf, hv, hS⟩
    simp only [WP.spec_ok]
    exact ⟨hnf, σ', hm, hR4.frame hP hf hv, hS⟩
  unfold notification.receive_signal
  step
  rw [st_post, epState_eq] at *
  rcases hst with hst | hst
  · simp only [hst, ↓reduceIte]
    exact key
  · simp only [hst, ntfn_consts.1, ntfn_consts.2.1, show (1#u64 : U64) ≠ 0#u64 by decide, ↓reduceIte]
    exact key

end

end

end Fl4Proofs.P3.Notif
