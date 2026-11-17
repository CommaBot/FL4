/-
P3 (DESIGN.md §9), IPC: **an endpoint's finalisation on `IRel`**
(`cancel_all_ipc`, toward `XFinHyps.ep`), the slots and the kernel-global
base kept (`IFrame`).

* `restart_irelF`: `restart_irel` with `IFrame`.
* `reply_unlink_iframe`: `reply_unlink`'s frame.
* `ep_restart_irel`: one queued thread's step (dequeue, reply unlink for a
  receiver with a reply, restart). Named: `ActReady` and the reply
  back-links (`ReplyBack`, l4v `sym_refs`) at the `IRel` states.
-/
import Fl4Proofs.P3.IpcCancelSignals
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Ipc
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Sched Classical

noncomputable section

section Restart
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

set_option maxHeartbeats 2000000 in
/-- `restart_irel` with the slots and the kernel-global base kept (`IFrame`). -/
theorem restart_irelF (hP0 : IPlaced N T E R B)
    (hAct : ∀ s σ, IRel st th cr N T C E R B c s σ → ActReady σ)
    (s : S) (σ : Fl4Spec.State Unit) (hX : IRel st th cr N T C E R B c s σ) {t : U64} (ht : t ∈ T)
    {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x)) (hns : tsCode x.tcbState ≠ 6)
    (hq : ∀ e ∈ E, ∀ z, σ.kheap e.bv = some (.endpoint z) → t.bv ∉ z.epQueue) :
    endpoint.restart_thread_if_no_fault st s t ⦃ s' => ∃ σ', ((), σ') ∈ (Fl4Spec.restartThreadIfNoFault (Z := Unit) t.bv σ).1 ∧
      IRel st th cr N T C E R B c s' σ' ∧
      (∀ p y, σ.kheap p = some (.endpoint y) → σ'.kheap p = some (.endpoint y)) ∧ IFrame (L := L) th s s' ⦄ := by
  have hP := hP0.e
  have hH := ipcCore_top (st := st) (th := th) (cr := cr) (N := N) (C := C) (c := c) hP
  have hTR := hX.1.toE.at_tcb ht hk
  have hkp : ∀ p y, σ.kheap p = some (.endpoint y) → p ≠ t.bv := fun p y hy e => by
    rw [e, hk] at hy; cases hy
  unfold endpoint.restart_thread_if_no_fault
  step with obj.Tcb.fault_type.spec as ⟨i, hi⟩
  by_cases h0 : i = fl4_abi.consts.fault.NullFault
  · rw [if_pos h0]
    have hf : x.tcbFault = none := hTR.fault0.1 (by rw [← hi, h0]; unfold fl4_abi.consts.fault.NullFault; rfl)
    have hcode : sched.TS_RESTART.val = tsCode .restart := by unfold sched.TS_RESTART; rfl
    refine WP.spec_bind (WP.spec_and (set_thread_state_c hH hP0 hP s σ hX.1.toE (IpcRel.toSRN hX.1 hX.2) ht hk hq hns
      .restart (by decide) sched.TS_RESTART hcode) (set_thread_state_sfoot hX.2.2.1 ht sched.TS_RESTART)) ?_
    rintro s1 ⟨⟨hE1, hS1⟩, hw1⟩
    have hF1 : IFrame (L := L) th s s1 :=
      IRel.iframe_of hX hw1 fun b hb => tfoot_oobj hX.2.2.1 (Or.inl (KFoot.of_sfoot hb))
    have hX1 := IpcRel.ofSRN hE1 hS1
    rw [endpoint_unblock_sporadic_eq]
    refine WP.spec_bind (WP.spec_and (unblock_irel hP0 s1 _ hX1 t ht) (unblock_sporadic_tfoot hX1.2.2.1 t ht)) ?_
    rintro s2 ⟨⟨σ2, hu, hf2, hv2, hX2⟩, hw2⟩
    have hF2 : IFrame (L := L) th s1 s2 := IRel.iframe_of hX1 hw2 fun b hb => tfoot_oobj hX1.2.2.1 hb
    refine WP.spec_mono (WP.spec_and (switch_top hP0 s2 σ2 hX2.1 hX2.2 (hAct _ _ hX2) t ht)
      (possible_switch_to_sfootI hX2.1.toN hX2.2.2.1 (hAct _ _ hX2) ht)) ?_
    rintro s3 ⟨⟨σ3, hps, hk3, hf3, hv3, hS3⟩, hw3⟩
    have hF3 : IFrame (L := L) th s2 s3 := IRel.iframe_of hX2 hw3 fun b hb => sfootI_oobj hP.tcb hb
    refine ⟨σ3, ?_, ⟨hX2.1.frame hP0 hf3 hv3, hS3⟩, fun p y hy => ?_, (hF1.trans hF2).trans hF3⟩
    · unfold Fl4Spec.restartThreadIfNoFault
      rw [nd_bind_one (threadGet_eq _ hk), hf]
      simp only [↓reduceIte]
      rw [nd_bind_one (Notif.setThreadState_eq .restart hk), restart_spec_eq, specSporadicAssert_eq,
        nd_bind_one hu, hps]
      rfl
    · have h1 : (stsAct (updK σ t.bv (.tcb { x with tcbState := .restart })) t.bv).kheap p = some (.endpoint y) := by
        rw [stsAct_kheap]; simp [updK, hkp p y hy, hy]
      rw [hk3]; exact hv2.2.1.1 _ _ h1
  · rw [if_neg h0]
    have hf : x.tcbFault ≠ none := fun e => h0 (by rw [hi, hTR.fault0.2 e]; unfold fl4_abi.consts.fault.NullFault; rfl)
    have hcode : sched.TS_INACTIVE.val = tsCode .inactive := by unfold sched.TS_INACTIVE; rfl
    refine WP.spec_mono (WP.spec_and (set_thread_state_c hH hP0 hP s σ hX.1.toE (IpcRel.toSRN hX.1 hX.2) ht hk hq hns
      .inactive (by decide) sched.TS_INACTIVE hcode) (set_thread_state_sfoot hX.2.2.1 ht sched.TS_INACTIVE)) ?_
    rintro s1 ⟨⟨hE1, hS1⟩, hw1⟩
    refine ⟨_, ?_, IpcRel.ofSRN hE1 hS1, fun p y hy => ?_,
      IRel.iframe_of hX hw1 fun b hb => tfoot_oobj hX.2.2.1 (Or.inl (KFoot.of_sfoot hb))⟩
    · unfold Fl4Spec.restartThreadIfNoFault
      rw [nd_bind_one (threadGet_eq _ hk)]
      simp only [hf, ↓reduceIte]
      rw [Notif.setThreadState_eq .inactive hk]
      rfl
    · rw [stsAct_kheap]; simp [updK, hkp p y hy, hy]


/-- **`reply_unlink`'s frame**: the reply's TCB word, then the thread's
state (`set_thread_state_sfoot`). -/
theorem reply_unlink_iframe (hP0 : IPlaced N T E R B) {s : S} {σ : Fl4Spec.State Unit}
    (hX : IRel st th cr N T C E R B c s σ) {t r : U64} (ht : t ∈ T) (hr : r ∈ R) {xr : Fl4Spec.Reply}
    (hkr : σ.kheap r.bv = some (.reply xr)) :
    ipc.reply_unlink st s r t ⦃ s' => IFrame (L := L) th s s' ⦄ := by
  have hP := hP0.e
  have hH := ipcCore_top (st := st) (th := th) (cr := cr) (N := N) (C := C) (c := c) hP
  have hSR := IpcRel.toSRN hX.1 hX.2
  obtain ⟨-, -, hS1, hA1⟩ := reply_write_rel (hH.epHyps hP0) hP s σ hX.1.toE hSR.1 hr hkr 0#u64
  obtain ⟨-, ⟨⟨G, hB⟩, hV⟩, -, -⟩ := hX
  obtain ⟨P, L4, L3, L2, L1, -, -, -, -, hPt⟩ := hV.ex
  have hF1 : IFrame (L := L) th s (L.wr s (Endp.rTcbA r) 0#u64) := by
    refine ⟨slotsSame_of_vobj hB.1 fun b hb hv => hA1 b hb fun e => hPt.disj b ?_ hv, L.ksb_wr _ _ _⟩
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨r, hr, by omega, by omega⟩))))
  unfold ipc.reply_unlink
  step as ⟨s1, hs1⟩
  subst hs1
  refine WP.spec_mono (set_thread_state_sfoot hS1.1.2.1 ht sched.TS_INACTIVE) fun s2 hw2 => ?_
  exact hF1.trans (SRT.iframe_of hS1.1 hw2 fun b hb => tfoot_oobj hS1.1.2.1 (Or.inl (KFoot.of_sfoot hb)))


open Fl4Spec in
/-- One step of the spec's loop. -/
abbrev rre (e : U64) (t : ObjRef) : SMonad Unit Unit := removeAndRestartEpQueuedThread t e.bv

/-- **The reply back-links of the threads blocked on a receive** (l4v
`sym_refs` for the reply's TCB). -/
def ReplyBack (σ : Fl4Spec.State Unit) : Prop :=
  ∀ t x e r d, σ.kheap t = some (.tcb x) → x.tcbState = .blockedOnReceive e (some r) d →
    ∃ xr, σ.kheap r = some (.reply xr) ∧ xr.replyTcb = some t

set_option maxHeartbeats 16000000 in
/-- **One thread queued on an endpoint restarted** (the head `t0` of its
queue) on `IRel`: dequeued, its reply unlinked if it waits to receive with
one, restarted (`restart_irelF`); the endpoint's queue `rest` after. -/
theorem ep_restart_irel (hP0 : IPlaced N T E R B)
    (hAct : ∀ s σ, IRel st th cr N T C E R B c s σ → ActReady σ)
    (hRB : ∀ s σ, IRel st th cr N T C E R B c s σ → ReplyBack σ)
    (s : S) (σ : Fl4Spec.State Unit) (hX : IRel st th cr N T C E R B c s σ) {e : U64} (he : e ∈ E)
    {y : Fl4Spec.Endpoint} (hky : σ.kheap e.bv = some (.endpoint y)) {t0 : U64} {rest : List U64}
    (hq : y.epQueue = (t0 :: rest).map UScalar.bv) {γ : Type} (k : S → Result γ) {Q : γ → Prop}
    (hkont : ∀ s' σ' y', ((), σ') ∈ (rre e t0.bv σ).1 → IRel st th cr N T C E R B c s' σ' →
      σ'.kheap e.bv = some (.endpoint y') → y'.epQueue = rest.map UScalar.bv → IFrame (L := L) th s s' →
      k s' ⦃ Q ⦄) :
    (do
      let s1 ← endpoint.ep_dequeue st s e t0
      let i ← obj.Tcb.state st t0 s1
      let s2 ← if i = sched.TS_BLOCKED_ON_RECV then do
          let i1 ← obj.Tcb.reply_obj st t0 s1
          if i1 != 0#u64 then ipc.reply_unlink st s1 i1 t0 else ok s1
        else ok s1
      let s3 ← endpoint.restart_thread_if_no_fault st s2 t0
      k s3) ⦃ Q ⦄ := by
  have hP := hP0.e
  have hH := ipcCore_top (st := st) (th := th) (cr := cr) (N := N) (C := C) (c := c) hP
  have hEP := hX.1.toE.at_ep he hky
  obtain ⟨xs, hQ, hxs, hB⟩ := hEP.queue
  have hxs' : xs = t0 :: rest := by
    rw [hq] at hxs
    exact (List.map_injective_iff.2 (fun a b h => eq_of_bv h) hxs).symm
  subst hxs'
  have ht0T : t0 ∈ T := hQ.mem t0 (by simp)
  have hta := hP.tcb t0 ht0T
  obtain ⟨xt, hkt, -⟩ := hX.1.tcb t0 ht0T
  have hTRE := hX.1.toE.at_tcb ht0T hkt
  have hd : t0.bv ∈ y.epQueue := by rw [hq]; simp
  obtain ⟨hbe, -⟩ := hB t0 (by simp)
  -- the thread waits on `e`, to send or to receive
  have hst : (∃ d, xt.tcbState = .blockedOnSend e.bv d) ∨ (∃ ro d, xt.tcbState = .blockedOnReceive e.bv ro d) := by
    cases y with
    | idleEP => simp [Fl4Spec.Endpoint.epQueue] at hq
    | sendEP q =>
      obtain ⟨-, ys, -, -, hQ', hqo⟩ := hEP
      have hu := hQ'.unique hP.tcb hQ
      rw [hu] at hqo
      have h4 := (hqo t0 (by simp)).1
      have h' := hTRE.st; rw [h4] at h'
      obtain ⟨e', d, hs⟩ : ∃ e' d, xt.tcbState = .blockedOnSend e' d := by
        cases h : xt.tcbState <;> rw [h] at h' <;> simp [tsCode] at h'; exact ⟨_, _, rfl⟩
      have he' : e' = e.bv := by rw [← hTRE.blk e' (by simp [hs, Fl4Spec.epBlocked]), hbe]
      exact Or.inl ⟨d, he' ▸ hs⟩
    | recvEP q =>
      obtain ⟨-, ys, -, -, hQ', hqo⟩ := hEP
      have hu := hQ'.unique hP.tcb hQ
      rw [hu] at hqo
      have h3 := (hqo t0 (by simp)).1
      have h' := hTRE.st; rw [h3] at h'
      obtain ⟨e', ro, d, hs⟩ : ∃ e' ro d, xt.tcbState = .blockedOnReceive e' ro d := by
        cases h : xt.tcbState <;> rw [h] at h' <;> simp [tsCode] at h'; exact ⟨_, _, _, rfl⟩
      have he' : e' = e.bv := by rw [← hTRE.blk e' (by simp [hs, Fl4Spec.epBlocked]), hbe]
      exact Or.inr ⟨ro, d, he' ▸ hs⟩
  -- the dequeue
  refine WP.spec_bind (WP.spec_and (ep_dequeue_c hH hP0 hP s σ hX.1.toE (IpcRel.toSRN hX.1 hX.2) he hky hd)
    (ep_dequeue_full hP s he t0 (t0 :: rest) hQ (by simp))) ?_
  rintro s1 ⟨⟨hdq, hR1, hS1, hA1⟩, -, -, -, hw1, -, -⟩
  have hX1 := IpcRel.ofSRN hR1 hS1
  have hF1 : IFrame (L := L) th s s1 := IRel.iframe_of hX hw1 fun b hb => iwords_oobj (EWrite.iwords hb)
  set σd := updK σ e.bv (.endpoint (epDeq y t0.bv)) with hσd
  have hte : t0.bv ≠ e.bv := by intro h; rw [h, hky] at hkt; cases hkt
  have hktd : σd.kheap t0.bv = some (.tcb xt) := by simp [hσd, updK, hte, hkt]
  have hkyd : σd.kheap e.bv = some (.endpoint (epDeq y t0.bv)) := by simp [hσd, updK]
  have hb1 : L.mem s1 (tBlockA t0) = e := (hA1 _ (a_blk hta).1 ⟨t0, ht0T, (a_blk hta).2⟩).trans hbe
  have hnd : (t0 :: rest).Nodup := hQ.nodup
  have hdq' : (epDeq y t0.bv).epQueue = rest.map UScalar.bv := by
    rw [Sched.epDeq_queue', hq, removeAll_map hnd, List.erase_cons_head]
  have hq1 := dequeued_not_queued hR1 he hb1 hkyd (epDeq_not_mem _)
  have hst1 : L.mem s1 (tStA t0) = L.mem s (tStA t0) := hA1 _ (a_st hta).1 ⟨t0, ht0T, (a_st hta).2⟩
  have hrp1 : L.mem s1 (tReplyA t0) = L.mem s (tReplyA t0) := hA1 _ (a_reply hta).1 ⟨t0, ht0T, (a_reply hta).2⟩
  -- the spec's step from the reply unlink and the restart
  have hrre : ∀ σ2 σ3, ((), σ2) ∈ (Fl4Spec.NonDet.maybeM (Fl4Spec.replyUnlinkTcb (Z := Unit) t0.bv)
        (if Fl4Spec.isBlockedOnReceive xt.tcbState then Fl4Spec.replyObject xt.tcbState else none) σd).1 →
      ((), σ3) ∈ (Fl4Spec.restartThreadIfNoFault (Z := Unit) t0.bv σ2).1 → ((), σ3) ∈ (rre e t0.bv σ).1 := by
    intro σ2 σ3 h2 h3
    show ((), σ3) ∈ (Fl4Spec.removeAndRestartEpQueuedThread (Z := Unit) t0.bv e.bv σ).1
    unfold Fl4Spec.removeAndRestartEpQueuedThread
    rw [nd_bind_one hdq, nd_bind_one (getThreadState_eq hktd), Notif.nd_pure_bind']
    exact mem_bind_nd (x := ((), σ2)) h2 h3
  -- the restart with no reply to unlink
  have plain : (if Fl4Spec.isBlockedOnReceive xt.tcbState then Fl4Spec.replyObject xt.tcbState else none) = none →
      tsCode xt.tcbState ≠ 6 →
      endpoint.restart_thread_if_no_fault st s1 t0 ⦃ fun s3 => k s3 ⦃ Q ⦄ ⦄ := by
    intro hnone hns
    refine WP.spec_mono (restart_irelF hP0 hAct s1 σd hX1 ht0T hktd hns hq1) ?_
    rintro s3 ⟨σ3, hres, hX3, hkeep, hF3⟩
    exact hkont s3 σ3 _ (hrre σd σ3 (by rw [hnone]; exact Set.mem_singleton _) hres) hX3 (hkeep _ _ hkyd) hdq'
      (hF1.trans hF3)
  step with Fl4Proofs.P1.obj.Tcb.state.spec as ⟨w, hw⟩
  have hv : w.val = tsCode xt.tcbState := by rw [hw, P1.stA_eq, ← tStA_eq, hst1]; exact hTRE.st
  rcases hst with ⟨d, hs⟩ | ⟨ro, d, hs⟩
  · have hne : w ≠ sched.TS_BLOCKED_ON_RECV := fun h => by
      rw [h, tsVals.2.2.1, hs] at hv; simp [tsCode] at hv
    simp only [hne, ↓reduceIte, bind_ok]
    exact WP.spec_bind (plain (by rw [if_neg]; rintro ⟨_, _, _, h⟩; rw [hs] at h; cases h)
      (by rw [hs]; simp [tsCode])) fun _ h => h
  · have heq : w = sched.TS_BLOCKED_ON_RECV := UScalar.eq_of_val_eq (by rw [hv, hs, tsVals.2.2.1]; rfl)
    simp only [heq, ↓reduceIte]
    step with Endp.obj.Tcb.reply_obj.spec as ⟨i1, hi1⟩
    obtain ⟨hro, hroR⟩ := hTRE.recv e.bv ro d hs
    have hi1' : i1 = L.mem s (tReplyA t0) := by rw [hi1, hrp1]
    have hob : Fl4Spec.isBlockedOnReceive xt.tcbState := ⟨_, _, _, hs⟩
    by_cases h0 : i1 = 0#u64
    · simp only [h0, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, bind_ok]
      have hrn : ro = none := by rw [← hro, ← hi1', h0, Notif.optRef_zero]
      exact WP.spec_bind (plain (by rw [if_pos hob, hs, hrn]; rfl) (by rw [hs]; simp [tsCode])) fun _ h => h
    have hne : (i1 != 0#u64) = true := by simpa using h0
    simp only [hne, ↓reduceIte]
    have hrs : ro = some i1.bv := by rw [← hro, ← hi1', Notif.optRef_ne h0]
    have hiR : i1 ∈ R := by rw [hi1']; exact hroR (by rw [hrs]; simp)
    rw [hrs] at hs
    obtain ⟨xr, hkr, hback⟩ := hRB s1 σd hX1 t0.bv xt e.bv i1.bv d hktd hs
    refine WP.spec_bind (WP.spec_and (reply_unlink_irelG hP0 s1 σd hX1 ht0T hktd (Or.inr ⟨_, _, hs⟩)
      (by rw [hs]; simp [tsCode]) hq1 hiR hkr hback) (reply_unlink_iframe hP0 hX1 ht0T hiR hkr)) ?_
    rintro s2 ⟨⟨he2, hX2⟩, hF2⟩
    set σ2 := unlinkSt σd t0.bv i1.bv xt xr with hσ2
    have hre : e.bv ≠ i1.bv := by intro h; rw [h, hkr] at hkyd; cases hkyd
    have hkE : ∀ p z, σ2.kheap p = some (.endpoint z) → σd.kheap p = some (.endpoint z) := by
      intro p z hp
      simp only [hσ2, unlinkSt, stsAct_kheap, updK, Function.update_apply] at hp
      split_ifs at hp <;> first | cases hp | exact hp
    have hk2 : σ2.kheap t0.bv = some (.tcb { xt with tcbState := .inactive }) := by
      simp [hσ2, unlinkSt, stsAct_kheap, updK]
    have hk2e : σ2.kheap e.bv = some (.endpoint (epDeq y t0.bv)) := by
      simp [hσ2, unlinkSt, stsAct_kheap, updK, hre, Ne.symm hte, hkyd]
    refine WP.spec_bind (restart_irelF hP0 hAct s2 σ2 hX2 ht0T hk2 (by simp [tsCode])
      (fun e' he' z hz => hq1 e' he' z (hkE _ _ hz))) ?_
    rintro s3 ⟨σ3, hres, hX3, hkeep, hF3⟩
    refine hkont s3 σ3 _ (hrre σ2 σ3 ?_ hres) hX3 (hkeep _ _ hk2e) hdq' ((hF1.trans hF2).trans hF3)
    rw [if_pos hob, hs]
    show ((), σ2) ∈ (Fl4Spec.replyUnlinkTcb (Z := Unit) t0.bv i1.bv σd).1
    rw [he2]; exact Set.mem_singleton _

end Restart

end

end Fl4Proofs.P3.Ipc
