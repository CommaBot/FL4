/-
P3 (DESIGN.md §9), IPC: **an endpoint's finalisation on `IRel`**
(`cancel_all_ipc`, toward `XFinHyps.ep`), the slots and the kernel-global
base kept (`IFrame`).

* `restart_irelF`: `restart_irel` with `IFrame`.
* `reply_unlink_iframe`: `reply_unlink`'s frame.
* `ep_restart_irel`: one queued thread's step (dequeue, reply unlink for a
  receiver with a reply, restart). The spec's facts carried along (as
  `SpecFinOutEp`'s `ep_iter`, the step deterministic,
  `det_removeAndRestartEp`): the queued threads' SCs ready and sufficient
  (`MemOK`) and receivers' replies bound back (`RepOK`), `ScBack`,
  `ActReady`.
* `cancel_all_ipc_irel`: the loop and the reschedule.
* `xFinEp_of`: **`XFinHyps.ep`**, at `Z.mv Z.G V'` (`XTopAt.irel_same`),
  the spec's finalisation keeping the caps (`finEp_nkc`). Named (`EpFinPre`,
  at the `XTopAt` states): `BufWordRel`, the IPC placement, `EpPre` at each
  endpoint of `Z.E` (the queued threads' facts, `ScBack`, `ActReady`), the
  endpoint caps' objects among `Z.E`.
-/
import Fl4Proofs.P3.IpcCancelSignals
import Fl4Proofs.P3.IpcFinNtfn
import Fl4Proofs.P3.SpecFinFrames
import Fl4Proofs.P3.SpecDet
import Fl4Proofs.P3.IpcSignalBound
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Ipc
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Sched Classical

noncomputable section

section DetEp
open Fl4Spec Fl4Proofs.P3.Det

theorem det_tcbEpDequeue (t e : ObjRef) : Det (tcbEpDequeue (Z := Unit) t e) := by
  unfold tcbEpDequeue; det
  all_goals first | exact det_getSimpleKo _ _ | exact det_setSimpleKo _ _ _

theorem det_replyUnlinkTcb (t r : ObjRef) : Det (replyUnlinkTcb (Z := Unit) t r) := by
  unfold replyUnlinkTcb getThreadState; det
  all_goals first | exact det_getSimpleKo _ _ | exact det_threadGet _ _ | exact det_setThreadState _ _ | exact det_updateSkObjRef _ _ _ _

theorem det_restartThreadIfNoFault (t : ObjRef) : Det (restartThreadIfNoFault (Z := Unit) t) := by
  unfold restartThreadIfNoFault getTcbObjRef; det
  all_goals first | exact det_threadGet _ _ | exact det_setThreadState _ _ | exact det_ifCondRefillUnblockCheck _ _ _ | exact det_possibleSwitchTo _

/-- **`remove_and_restart_ep_queued_thread` has at most one outcome.** -/
theorem det_removeAndRestartEp (t e : ObjRef) : Det (removeAndRestartEpQueuedThread (Z := Unit) t e) := by
  unfold removeAndRestartEpQueuedThread getThreadState; det
  all_goals first | exact det_tcbEpDequeue _ _ | exact det_threadGet _ _ | exact det_replyUnlinkTcb _ _ | exact det_restartThreadIfNoFault _

end DetEp

section Restart
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

/-- **A step of an endpoint's finalisation**: its writes `CnW` (at its start:
`FinW`, the endpoints' two words, the replies' `TCB` words), the SCs' sizes
kept. -/
def CnStep (T N C E R : Set U64) (c : U64) (s : S) (σ : Fl4Spec.State Unit) (s' : S) (σ' : Fl4Spec.State Unit) :
    Prop :=
  WritesIn st s s' (CnW (st := st) T N C E R c s σ) ∧ SzKeepC C σ σ'

theorem CnW.back {s s' : S} {σ σ' : Fl4Spec.State Unit} (hk : L.ksb s' = L.ksb s) (hz : SzKeepC C σ σ') {b : U64}
    (h : CnW (st := st) T N C E R c s' σ' b) : CnW (st := st) T N C E R c s σ b :=
  h.imp_left (FinW.back hk hz)

theorem CnStep.refl (s : S) (σ : Fl4Spec.State Unit) : CnStep (st := st) T N C E R c s σ s σ :=
  ⟨WritesIn.refl _ _, fun _ _ x _ h => ⟨x, h⟩⟩

theorem CnStep.trans {s1 s2 s3 : S} {σ1 σ2 σ3 : Fl4Spec.State Unit} (h1 : CnStep (st := st) T N C E R c s1 σ1 s2 σ2)
    (h2 : CnStep (st := st) T N C E R c s2 σ2 s3 σ3) : CnStep (st := st) T N C E R c s1 σ1 s3 σ3 :=
  ⟨h1.1.trans1 (h2.1.mono fun _ hb => CnW.back h1.1.1 h1.2 hb), SzKeepC.trans' h1.2 h2.2⟩

theorem CnStep.ofFin {s s' : S} {σ σ' : Fl4Spec.State Unit} (h : FinStep (st := st) T N C c s σ s' σ') :
    CnStep (st := st) T N C E R c s σ s' σ' :=
  ⟨h.1.mono fun _ hb => Or.inl hb, h.2⟩

set_option maxHeartbeats 2000000 in
/-- `restart_irel` with the slots and the kernel-global base kept (`IFrame`). -/
theorem restart_irelF (hP0 : IPlaced N T E R B)
    (s : S) (σ : Fl4Spec.State Unit) (hX : IRel st th cr N T C E R B c s σ) {t : U64} (ht : t ∈ T)
    {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x)) (hns : tsCode x.tcbState ≠ 6)
    (hq : ∀ e ∈ E, ∀ z, σ.kheap e.bv = some (.endpoint z) → t.bv ∉ z.epQueue)
    (hxs : ScOK σ x) (hBk : ScBack σ) (hAr : ActReady σ) :
    endpoint.restart_thread_if_no_fault st s t ⦃ s' => ∃ σ', ((), σ') ∈ (Fl4Spec.restartThreadIfNoFault (Z := Unit) t.bv σ).1 ∧
      IRel st th cr N T C E R B c s' σ' ∧
      (∀ p y, σ.kheap p = some (.endpoint y) → σ'.kheap p = some (.endpoint y)) ∧ IFrame (L := L) th s s' ∧
      CnStep (st := st) T N C E R c s σ s' σ' ∧ RtFacts σ σ' t.bv x ⦄ := by
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
    have hC1 : CnStep (st := st) T N C E R c s σ s1 (stsAct (updK σ t.bv (.tcb { x with tcbState := .restart })) t.bv) :=
      ⟨hw1.mono fun b hb => Or.inl (Or.inl (KFoot.of_sfoot hb)), SzKeepC.of (SzKeep.of_tcb (p := t.bv)
        (x' := { x with tcbState := .restart }) (fun q hq => by rw [stsAct_kheap]; simp [updK, hq])
        (by rw [stsAct_kheap]; simp [updK]))⟩
    have hX1 := IpcRel.ofSRN hE1 hS1
    rw [endpoint_unblock_sporadic_eq]
    refine WP.spec_bind (WP.spec_and (unblock_irel hP0 s1 _ hX1 t ht) (unblock_sporadic_kfoot hX1.2.2.1 t ht)) ?_
    rintro s2 ⟨⟨σ2, hu, hf2, hv2, hX2⟩, hw2⟩
    have hF2 : IFrame (L := L) th s1 s2 := IRel.iframe_of hX1 hw2 fun b hb => tfoot_oobj hX1.2.2.1 (Or.inl hb)
    have hC2 : CnStep (st := st) T N C E R c s1 (stsAct (updK σ t.bv (.tcb { x with tcbState := .restart })) t.bv)
        s2 σ2 := by
      refine ⟨hw2.mono fun b hb => Or.inl (Or.inl hb), SzKeepC.of fun p y k hp => ?_⟩
      have hmem : ((), σ2) ∈ ((Fl4Spec.getTcbObjRef (Z := Unit) Fl4Spec.Tcb.tcbSchedContext t.bv >>=
          Fl4Spec.ifSporadicCurScTestRefillUnblockCheck (Z := Unit))
            (stsAct (updK σ t.bv (.tcb { x with tcbState := .restart })) t.bv)).1 := by
        rw [show (Fl4Spec.getTcbObjRef (Z := Unit) Fl4Spec.Tcb.tcbSchedContext t.bv >>=
          Fl4Spec.ifSporadicCurScTestRefillUnblockCheck (Z := Unit)) = specUnblock t.bv from rfl, hu]
        exact Set.mem_singleton _
      obtain ⟨y0, h0, -, -⟩ := MaxK.mk_unblock t.bv _ ((), σ2) hmem p y k hp
      exact ⟨y0, h0⟩
    have hkt1 : (stsAct (updK σ t.bv (.tcb { x with tcbState := .restart })) t.bv).kheap t.bv =
        some (.tcb { x with tcbState := .restart }) := by rw [stsAct_kheap]; simp [updK]
    obtain ⟨σm, hmm, hktm, hBm, hAm, hTm, htm, hkpm⟩ := restart_tail_mid hk hxs hBk hAr
    have e2 : σm = σ2 := by
      have hmem : ((), σm) ∈ (specUnblock t.bv (stsAct (updK σ t.bv (.tcb { x with tcbState := .restart })) t.bv)).1 := by
        rw [← specSporadicAssert_eq]; unfold specSporadicAssert
        rw [nd_bind_one (show Fl4Spec.getTcbObjRef (Z := Unit) Fl4Spec.Tcb.tcbSchedContext t.bv _ = _ from
          threadGet_eq _ hkt1)]
        exact hmm
      rw [hu] at hmem
      exact (Prod.mk.inj (Set.mem_singleton_iff.1 hmem)).2
    rw [e2] at hktm hBm hAm hTm htm hkpm
    refine WP.spec_mono (WP.spec_and (switch_top hP0 s2 σ2 hX2.1 hX2.2 hAm t ht)
      (possible_switch_to_sfootI hX2.1.toN hX2.2.2.1 hAm ht)) ?_
    rintro s3 ⟨⟨σ3, hps, hk3, hf3, hv3, hS3⟩, hw3⟩
    have hF3 : IFrame (L := L) th s2 s3 := IRel.iframe_of hX2 hw3 fun b hb => sfootI_oobj hP.tcb hb
    have hC3 : CnStep (st := st) T N C E R c s2 σ2 s3 σ3 :=
      ⟨hw3.mono fun b hb => Or.inl (SFootI.finW hP.tcb hb), SzKeepC.of (SzKeep.of_kheap hk3)⟩
    obtain ⟨σ6, he6, hk6, ht6, hr6, ha6⟩ := pst_ok hktm hAm
    have e3 : σ6 = σ3 := by
      have h : ((), σ6) ∈ (Fl4Spec.possibleSwitchTo (Z := Unit) t.bv σ2).1 := by rw [he6]; rfl
      rw [hps] at h; exact (Prod.mk.inj (Set.mem_singleton_iff.1 h)).2
    rw [e3] at hk6 ht6 hr6 ha6
    have hRF : RtFacts σ σ3 t.bv x := ⟨(SFr.of_heap hk6 ht6 hr6).scBack hBm, pst_actReady hAm hTm hk6 ht6 hr6 ha6,
      by rw [ht6, htm], fun p hp hpc => by rw [hk6, hkpm p hp hpc]⟩
    refine ⟨σ3, ?_, ⟨hX2.1.frame hP0 hf3 hv3, hS3⟩, fun p y hy => ?_, (hF1.trans hF2).trans hF3,
      (hC1.trans hC2).trans hC3, hRF⟩
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
    obtain ⟨σi, hei, hBi, hAi, hti, -, hkpi⟩ := inactive_ok hk hBk hAr
    rw [Notif.setThreadState_eq .inactive hk] at hei
    have ei := (Prod.mk.inj (singleton_one_eq hei)).2
    have hRF : RtFacts σ (stsAct (updK σ t.bv (.tcb { x with tcbState := .inactive })) t.bv) t.bv x := by
      rw [ei]; exact ⟨hBi, hAi, hti, fun p hp _ => hkpi p hp⟩
    refine ⟨_, ?_, IpcRel.ofSRN hE1 hS1, fun p y hy => ?_,
      IRel.iframe_of hX hw1 fun b hb => tfoot_oobj hX.2.2.1 (Or.inl (KFoot.of_sfoot hb)),
      ⟨hw1.mono fun b hb => Or.inl (Or.inl (KFoot.of_sfoot hb)), SzKeepC.of (SzKeep.of_tcb (p := t.bv)
        (x' := { x with tcbState := .inactive }) (fun q hq => by rw [stsAct_kheap]; simp [updK, hq])
        (by rw [stsAct_kheap]; simp [updK]))⟩, hRF⟩
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


/-- **`reply_unlink`'s footprint** (`CnW`): the reply's TCB word, then the
thread's state (`set_thread_state_sfoot`). -/
theorem reply_unlink_cn (hP0 : IPlaced N T E R B) {s : S} {σ : Fl4Spec.State Unit}
    (hX : IRel st th cr N T C E R B c s σ) {t r : U64} (ht : t ∈ T) (hr : r ∈ R) {xr : Fl4Spec.Reply}
    (hkr : σ.kheap r.bv = some (.reply xr)) :
    ipc.reply_unlink st s r t ⦃ s' => WritesIn st s s' (CnW (st := st) T N C E R c s σ) ⦄ := by
  have hP := hP0.e
  have hH := ipcCore_top (st := st) (th := th) (cr := cr) (N := N) (C := C) (c := c) hP
  have hSR := IpcRel.toSRN hX.1 hX.2
  obtain ⟨-, -, hS1, hA1⟩ := reply_write_rel (hH.epHyps hP0) hP s σ hX.1.toE hSR.1 hr hkr 0#u64
  unfold ipc.reply_unlink
  step as ⟨s1, hs1⟩
  subst hs1
  refine WP.spec_mono (set_thread_state_sfoot hS1.1.2.1 ht sched.TS_INACTIVE) fun s2 hw2 => ?_
  have hw4 : WritesIn st s (L.wr s (Endp.rTcbA r) 0#u64) (fun b => b.val = r.val) :=
    ⟨L.ksb_wr _ _ _, L.cpu_wr _ _ _, fun b hb hn => hA1 b hb hn⟩
  refine (hw4.trans hw2).mono fun b hb => ?_
  rcases hb with hb | hb
  · exact Or.inr (Or.inr ⟨r, hr, hb⟩)
  · exact Or.inl (Or.inl (KFoot.of_sfoot ((SFoot.ksb (L.ksb_wr _ _ _)).1 hb)))

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
    (s : S) (σ : Fl4Spec.State Unit) (hX : IRel st th cr N T C E R B c s σ) {e : U64} (he : e ∈ E)
    {y : Fl4Spec.Endpoint} (hky : σ.kheap e.bv = some (.endpoint y)) {t0 : U64} {rest : List U64}
    (hq : y.epQueue = (t0 :: rest).map UScalar.bv)
    (hm : ∀ u ∈ y.epQueue, MemOK σ u ∧ RepOK σ u) (hBk : ScBack σ) (hAr : ActReady σ)
    {γ : Type} (k : S → Result γ) {Q : γ → Prop}
    (hkont : ∀ s' σ' y', ((), σ') ∈ (rre e t0.bv σ).1 → IRel st th cr N T C E R B c s' σ' →
      σ'.kheap e.bv = some (.endpoint y') → y'.epQueue = rest.map UScalar.bv → IFrame (L := L) th s s' →
      CnStep (st := st) T N C E R c s σ s' σ' →
      (∀ u ∈ rest.map UScalar.bv, MemOK σ' u ∧ RepOK σ' u) → ScBack σ' → ActReady σ' → k s' ⦃ Q ⦄) :
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
  rintro s1 ⟨⟨hdq, hR1, hS1, hA1⟩, -, -, hQA, hw1, -, -⟩
  have hX1 := IpcRel.ofSRN hR1 hS1
  have hF1 : IFrame (L := L) th s s1 := IRel.iframe_of hX hw1 fun b hb => iwords_oobj (EWrite.iwords hb)
  have hCd : CnStep (st := st) T N C E R c s σ s1 (updK σ e.bv (.endpoint (epDeq y t0.bv))) := by
    refine ⟨⟨hw1.1, hw1.2.1, fun b hb hn => hQA b hb ⟨fun h => hn (Or.inr (Or.inl ⟨e, he, h⟩)), ?_⟩⟩,
      SzKeepC.of (SzKeep.updK hky (fun _ _ h => by cases h))⟩
    rintro ⟨w, hw, h | h⟩
    · exact hn (Or.inl (Or.inr ⟨w, hQ.mem w hw, 3496, by omega, by omega, by omega, by omega, by omega, h⟩))
    · exact hn (Or.inl (Or.inr ⟨w, hQ.mem w hw, 3504, by omega, by omega, by omega, by omega, by omega, h⟩))
  set σd := updK σ e.bv (.endpoint (epDeq y t0.bv)) with hσd
  have hte : t0.bv ≠ e.bv := by intro h; rw [h, hky] at hkt; cases hkt
  have hktd : σd.kheap t0.bv = some (.tcb xt) := by simp [hσd, updK, hte, hkt]
  have hkyd : σd.kheap e.bv = some (.endpoint (epDeq y t0.bv)) := by simp [hσd, updK]
  have hb1 : L.mem s1 (tBlockA t0) = e := (hA1 _ (a_blk hta).1 ⟨t0, ht0T, (a_blk hta).2⟩).trans hbe
  have hnd : (t0 :: rest).Nodup := hQ.nodup
  -- the spec's facts after the step (`ep_iter`, the step deterministic)
  have hndq : ((t0 :: rest).map UScalar.bv).Nodup := hnd.map (fun a b h => eq_of_bv h)
  obtain ⟨σ5, hm5, -, hmm5, hB5, hA5⟩ := ep_iter hky hq hndq (fun u hu => hm u (by rw [hq]; exact hu)) hBk hAr
  have fin3 : ∀ σ3, ((), σ3) ∈ (rre e t0.bv σ).1 →
      (∀ u ∈ rest.map UScalar.bv, MemOK σ3 u ∧ RepOK σ3 u) ∧ ScBack σ3 ∧ ActReady σ3 := by
    intro σ3 h3
    have e35 : ((), σ3) = ((), σ5) := (det_removeAndRestartEp t0.bv e.bv).det σ _ _ h3 hm5
    rw [(Prod.mk.inj e35).2]; exact ⟨hmm5, hB5, hA5⟩
  -- the spec's facts at the dequeued state
  have hFd : SFr σ (updK σ e.bv (.endpoint (epDeq y t0.bv))) := SFr.updOther hky (fun _ h => by cases h)
    (fun _ _ h => by cases h) (fun _ h => by cases h) (fun _ _ h => by cases h)
  have hm0 : MemOK σ t0.bv ∧ RepOK σ t0.bv := hm t0.bv (by rw [hq]; simp)
  have hdq' : (epDeq y t0.bv).epQueue = rest.map UScalar.bv := by
    rw [Sched.epDeq_queue', hq, removeAll_map hnd, List.erase_cons_head]
  have hq1 := dequeued_not_queued hR1 he hb1 hkyd (epDeq_not_mem _)
  have hBd : ScBack σd := hFd.scBack hBk
  have hAd : ActReady σd := hFd.actReady hAr (Or.inl rfl)
  have hxsd : ScOK σd xt := by
    obtain ⟨x', hk', hsc⟩ := hFd.memOK hm0.1
    rw [hktd] at hk'; cases hk'; exact hsc
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
    refine WP.spec_mono (restart_irelF hP0 s1 σd hX1 ht0T hktd hns hq1 hxsd hBd hAd) ?_
    rintro s3 ⟨σ3, hres, hX3, hkeep, hF3, hC3, -⟩
    have hr3 := hrre σd σ3 (by rw [hnone]; exact Set.mem_singleton _) hres
    obtain ⟨f1, f2, f3⟩ := fin3 σ3 hr3
    exact hkont s3 σ3 _ hr3 hX3 (hkeep _ _ hkyd) hdq' (hF1.trans hF3) (hCd.trans hC3) f1 f2 f3
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
    obtain ⟨xr, hkr0, hback⟩ := hm0.2 xt hkt e.bv i1.bv d hs
    have hie : i1.bv ≠ e.bv := fun h => by rw [h, hky] at hkr0; cases hkr0
    have hkr : σd.kheap i1.bv = some (.reply xr) := by simp [hσd, updK, hie, hkr0]
    refine WP.spec_bind (WP.spec_and (WP.spec_and (reply_unlink_irelG hP0 s1 σd hX1 ht0T hktd (Or.inr ⟨_, _, hs⟩)
      (by rw [hs]; simp [tsCode]) hq1 hiR hkr hback) (reply_unlink_iframe hP0 hX1 ht0T hiR hkr))
      (reply_unlink_cn hP0 hX1 ht0T hiR hkr)) ?_
    rintro s2 ⟨⟨⟨he2, hX2⟩, hF2⟩, hW2⟩
    set σ2 := unlinkSt σd t0.bv i1.bv xt xr with hσ2
    have hC2 : CnStep (st := st) T N C E R c s1 σd s2 σ2 := ⟨hW2, SzKeepC.of fun p y0 n hp => ⟨y0, by
      simp only [hσ2, unlinkSt, stsAct_kheap, updK, Function.update_apply] at hp
      split_ifs at hp <;> first | cases hp | exact hp⟩⟩
    have hre : e.bv ≠ i1.bv := by intro h; rw [h, hkr] at hkyd; cases hkyd
    have hkE : ∀ p z, σ2.kheap p = some (.endpoint z) → σd.kheap p = some (.endpoint z) := by
      intro p z hp
      simp only [hσ2, unlinkSt, stsAct_kheap, updK, Function.update_apply] at hp
      split_ifs at hp <;> first | cases hp | exact hp
    have hk2 : σ2.kheap t0.bv = some (.tcb { xt with tcbState := .inactive }) := by
      simp [hσ2, unlinkSt, stsAct_kheap, updK]
    have hk2e : σ2.kheap e.bv = some (.endpoint (epDeq y t0.bv)) := by
      simp [hσ2, unlinkSt, stsAct_kheap, updK, hre, Ne.symm hte, hkyd]
    -- the spec's facts at the unlinked state (`inactive_ok`)
    have htr : t0.bv ≠ i1.bv := fun h => by rw [h, hkr] at hktd; cases hktd
    have hFr : SFr σd (updK σd i1.bv (.reply { xr with replyTcb := none })) := SFr.updOther hkr
      (fun _ h => by cases h) (fun _ _ h => by cases h) (fun _ h => by cases h) (fun _ _ h => by cases h)
    have hktr : (updK σd i1.bv (.reply { xr with replyTcb := none })).kheap t0.bv = some (.tcb xt) := by
      simp only [updK, Function.update_of_ne htr]; exact hktd
    obtain ⟨σi, hei, hBi, hAi, hti, -, hkpi⟩ := inactive_ok hktr (hFr.scBack hBd) (hFr.actReady hAd (Or.inl rfl))
    rw [Notif.setThreadState_eq .inactive hktr] at hei
    have hσ2i : σ2 = σi := by rw [hσ2]; exact (Prod.mk.inj (singleton_one_eq hei)).2
    have hxs2 : ScOK σi { xt with tcbState := .inactive } := by
      intro c hc
      obtain ⟨y0, k0, h1, h2⟩ := hxsd c hc
      have hct : c ≠ t0.bv := by rintro rfl; rw [hktd] at h1; cases h1
      have hcr : c ≠ i1.bv := by rintro rfl; rw [hkr] at h1; cases h1
      refine ⟨y0, k0, ?_, by rw [hti]; exact h2⟩
      rw [hkpi c hct]; simp only [updK, Function.update_of_ne hcr]; exact h1
    refine WP.spec_bind (restart_irelF hP0 s2 σ2 hX2 ht0T hk2 (by simp [tsCode])
      (fun e' he' z hz => hq1 e' he' z (hkE _ _ hz)) (by rw [hσ2i]; exact hxs2) (by rw [hσ2i]; exact hBi)
      (by rw [hσ2i]; exact hAi)) ?_
    rintro s3 ⟨σ3, hres, hX3, hkeep, hF3, hC3, -⟩
    have hr3 : ((), σ3) ∈ (rre e t0.bv σ).1 := by
      refine hrre σ2 σ3 ?_ hres
      rw [if_pos hob, hs]
      show ((), σ2) ∈ (Fl4Spec.replyUnlinkTcb (Z := Unit) t0.bv i1.bv σd).1
      rw [he2]; exact Set.mem_singleton _
    obtain ⟨f1, f2, f3⟩ := fin3 σ3 hr3
    refine hkont s3 σ3 _ hr3 hX3 (hkeep _ _ hk2e) hdq' ((hF1.trans hF2).trans hF3) ((hCd.trans hC2).trans hC3)
      f1 f2 f3

set_option maxHeartbeats 4000000 in
/-- **A thread queued on an endpoint is blocked on it** (send or receive),
from the endpoint relation. -/
theorem ep_queue_blocked (hP0 : IPlaced N T E R B) {s : S} {σ : Fl4Spec.State Unit}
    (hX : IRel st th cr N T C E R B c s σ) {e : U64} (he : e ∈ E) {y : Fl4Spec.Endpoint}
    (hky : σ.kheap e.bv = some (.endpoint y)) {u : Fl4Spec.ObjRef} (hu : u ∈ y.epQueue) :
    ∃ xu, σ.kheap u = some (.tcb xu) ∧ Fl4Spec.epBlocked xu.tcbState = some e.bv := by
  have hP := hP0.e
  have hne : y ≠ .idleEP := by rintro rfl; simp [Fl4Spec.Endpoint.epQueue] at hu
  have hEP := hX.1.toE.at_ep he hky
  obtain ⟨xs, hQ, hxs, hB⟩ := hEP.queue
  rw [hxs, List.mem_map] at hu
  obtain ⟨t0, ht0, rfl⟩ := hu
  have ht0T : t0 ∈ T := hQ.mem t0 ht0
  obtain ⟨xt, hkt, -⟩ := hX.1.tcb t0 ht0T
  have hTRE := hX.1.toE.at_tcb ht0T hkt
  obtain ⟨hbe, -⟩ := hB t0 ht0
  refine ⟨xt, hkt, ?_⟩
  cases y with
  | idleEP => exact absurd rfl hne
  | sendEP q =>
    obtain ⟨-, ys, -, -, hQ', hqo⟩ := hEP
    have hu := hQ'.unique hP.tcb hQ
    rw [hu] at hqo
    have h4 := (hqo t0 ht0).1
    have h' := hTRE.st; rw [h4] at h'
    obtain ⟨e', d, hs⟩ : ∃ e' d, xt.tcbState = .blockedOnSend e' d := by
      cases h : xt.tcbState <;> rw [h] at h' <;> simp [tsCode] at h'; exact ⟨_, _, rfl⟩
    have he' : e' = e.bv := by rw [← hTRE.blk e' (by simp [hs, Fl4Spec.epBlocked]), hbe]
    simp only [hs, he', Fl4Spec.epBlocked]
  | recvEP q =>
    obtain ⟨-, ys, -, -, hQ', hqo⟩ := hEP
    have hu := hQ'.unique hP.tcb hQ
    rw [hu] at hqo
    have h3 := (hqo t0 ht0).1
    have h' := hTRE.st; rw [h3] at h'
    obtain ⟨e', ro, d, hs⟩ : ∃ e' ro d, xt.tcbState = .blockedOnReceive e' ro d := by
      cases h : xt.tcbState <;> rw [h] at h' <;> simp [tsCode] at h'; exact ⟨_, _, _, rfl⟩
    have he' : e' = e.bv := by rw [← hTRE.blk e' (by simp [hs, Fl4Spec.epBlocked]), hbe]
    simp only [hs, he', Fl4Spec.epBlocked]

end Restart

/-! ## The loop -/

section Loop
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

variable (st th cr N T C E R B c) in
/-- The loop invariant: the queue still to visit is the endpoint's, from
FL4's next thread, the spec's outcomes from it among the whole's, the slots
and the base kept since `s0`. -/
def AInv (e : U64) (s0 : S) (σ0 : Fl4Spec.State Unit) (q0 : List Fl4Spec.ObjRef) (x : S × U64 × U64) : Prop :=
  ∃ σ' y, ∃ rest : List U64, IRel st th cr N T C E R B c x.1 σ' ∧ σ'.kheap e.bv = some (.endpoint y) ∧
    y.epQueue = rest.map UScalar.bv ∧ x.2.1 = rest.headD 0#u64 ∧ rest.length ≤ x.2.2.val ∧
    (∀ z, z ∈ (Fl4Spec.NonDet.mapMx (rre e) (rest.map UScalar.bv) σ').1 →
      z ∈ (Fl4Spec.NonDet.mapMx (rre e) q0 σ0).1) ∧ IFrame (L := L) th s0 x.1 ∧
    CnStep (st := st) T N C E R c s0 σ0 x.1 σ' ∧
    (∀ u ∈ rest.map UScalar.bv, MemOK σ' u ∧ RepOK σ' u) ∧ ScBack σ' ∧ ActReady σ'

set_option maxHeartbeats 4000000 in
/-- **The loop of `cancel_all_ipc`** on `IRel`. -/
theorem all_ipc_loop (hP0 : IPlaced N T E R B)
    {e : U64} (he : e ∈ E) (s0 : S) (σ0 : Fl4Spec.State Unit) (q0 : List Fl4Spec.ObjRef) (x0 : S × U64 × U64)
    (h0 : AInv st th cr N T C E R B c e s0 σ0 q0 x0) :
    endpoint.cancel_all_ipc_loop st x0.1 e x0.2.1 x0.2.2 ⦃ s' => ∃ σf,
      ((), σf) ∈ (Fl4Spec.NonDet.mapMx (rre e) q0 σ0).1 ∧ IRel st th cr N T C E R B c s' σf ∧
      IFrame (L := L) th s0 s' ∧ CnStep (st := st) T N C E R c s0 σ0 s' σf ∧ ActReady σf ⦄ := by
  have hP := hP0.e
  unfold endpoint.cancel_all_ipc_loop
  apply loop.spec_decr_nat (measure := fun x : S × U64 × U64 => x.2.2.val)
    (inv := AInv st th cr N T C E R B c e s0 σ0 q0) _ _ x0 ?_ h0
  rintro ⟨s, t, fuel⟩ ⟨σ', y, rest, hX, hky, hq, ht, hlen, hinc, hss, hcs, hm, hBk, hAr⟩
  simp only at hX hky hq ht hlen hinc hss hcs hm hBk hAr ⊢
  have hEP := hX.1.toE.at_ep he hky
  obtain ⟨xs, hQ, hxs, -⟩ := hEP.queue
  have hxs' : xs = rest := by
    rw [hq] at hxs
    exact (List.map_injective_iff.2 (fun a b h => eq_of_bv h) hxs).symm
  subst hxs'
  unfold endpoint.cancel_all_ipc_loop.body
  step with obj.Tcb.is_null.spec as ⟨bn, hbn⟩
  cases xs with
  | nil =>
    simp only [List.headD_nil] at ht
    subst ht
    simp only [hbn, decide_true, ↓reduceIte, WP.spec_ok]
    exact ⟨σ', hinc _ rfl, hX, hss, hcs, hAr⟩
  | cons t0 rest' =>
    simp only [List.headD_cons] at ht
    subst t
    have ht00 : t0 ≠ 0#u64 := hQ.ne0 hP.tcb t0 (by simp)
    simp only [hbn, ht00, decide_false, Bool.false_eq_true, ↓reduceIte]
    have hf0 : fuel > 0#u64 := by
      simp only [List.length_cons] at hlen
      show (0#u64 : U64).val < fuel.val; simp; omega
    simp only [hf0, ↓reduceIte]
    step as ⟨fuel1, hfuel1⟩
    have hseg := hQ.seg
    rw [show t0 :: rest' = [] ++ t0 :: rest' from rfl, Seg_mid] at hseg
    obtain ⟨-, -, hnext, -⟩ := hseg
    unfold tcbqueue.next_of
    step with tcbqueue.next.spec as ⟨nx, hnx⟩
    try simp only [bind_ok]
    refine ep_restart_irel hP0 s σ' hX he hky hq (by rw [hq]; exact hm) hBk hAr _
      fun s4 σ'' y' hres hX4 hky4 hq4 hss4 hcs4 hm4 hB4 hA4 => ?_
    rw [WP.spec_ok]
    refine ⟨⟨σ'', y', rest', hX4, hky4, hq4, by rw [hnx, hnext], ?_, ?_, hss.trans hss4, hcs.trans hcs4, hm4, hB4,
      hA4⟩, ?_⟩
    · rw [hfuel1]; simp only [List.length_cons] at hlen; scalar_tac
    · exact fun z hz => hinc z (by rw [List.map_cons]; exact mapMx_cons_mem (l := rest'.map UScalar.bv) hres z hz)
    · rw [hfuel1]; scalar_tac

set_option maxHeartbeats 4000000 in
/-- **`cancel_all_ipc` on `IRel`**, the slots and the base kept. -/
theorem cancel_all_ipc_irel (hP0 : IPlaced N T E R B)
    (s : S) (σ : Fl4Spec.State Unit) (hX : IRel st th cr N T C E R B c s σ) {e : U64} (he : e ∈ E)
    (hpre : EpPre σ e.bv) :
    endpoint.cancel_all_ipc st s e ⦃ s' => ∃ σ',
      ((), σ') ∈ (Fl4Spec.cancelAllIpc (Z := Unit) e.bv σ).1 ∧ IRel st th cr N T C E R B c s' σ' ∧
      IFrame (L := L) th s s' ∧ CnStep (st := st) T N C E R c s σ s' σ' ⦄ := by
  have hP := hP0.e
  obtain ⟨y, hky, hEP⟩ := hX.1.toE.ep e he
  obtain ⟨y0, hky0, -, hm0', hB0, hA0⟩ := hpre
  have hm0 : ∀ u ∈ y.epQueue, MemOK σ u ∧ RepOK σ u := by
    have e0 : y0 = y := by rw [hky] at hky0; cases hky0; rfl
    rw [← e0]; exact hm0'
  unfold endpoint.cancel_all_ipc
  step with obj.Ep.state.spec as ⟨i, hi⟩
  rw [epState_eq] at hi
  have hsp : Fl4Spec.cancelAllIpc (Z := Unit) e.bv σ = (match y with
        | .idleEP => (pure () : Fl4Spec.SMonad Unit Unit)
        | _ => (do Fl4Spec.NonDet.mapMx (fun t => Fl4Spec.removeAndRestartEpQueuedThread t e.bv) y.epQueue
                   Fl4Spec.rescheduleRequired)) σ := by
    unfold Fl4Spec.cancelAllIpc
    rw [nd_bind_one (getEndpoint_eq hky)]
    cases y <;> first | rfl | simp only [Notif.nd_pure_bind']
  -- the walk over a nonempty queue
  have walk : ∀ q : List Fl4Spec.ObjRef, y.epQueue = q → i ≠ obj.EP_IDLE →
      (do
        let q ← endpoint.get_queue st s e
        let s1 ← endpoint.cancel_all_ipc_loop st s e q.head layout.WALK_FUEL
        sched.reschedule_required st s1) ⦃ s' => ∃ σ',
        ((), σ') ∈ ((Fl4Spec.NonDet.mapMx (rre e) q >>= fun _ => Fl4Spec.rescheduleRequired (Z := Unit)) σ).1 ∧
        IRel st th cr N T C E R B c s' σ' ∧ IFrame (L := L) th s s' ∧ CnStep (st := st) T N C E R c s σ s' σ' ⦄ := by
    intro q hyq _
    obtain ⟨xs, hQ, hqx, -⟩ := hEP.queue
    step with endpoint.get_queue.spec as ⟨qq, hqq⟩
    have hfuel : layout.WALK_FUEL.val = 2 ^ 64 - 1 := by simp [layout.WALK_FUEL, U64.rMax]
    have hI0 : AInv st th cr N T C E R B c e s σ q (s, qq.head, layout.WALK_FUEL) :=
      ⟨σ, y, xs, hX, hky, hqx, by rw [hqq, epQ_eq, hQ.head], by rw [hfuel]; exact len_le_max xs hQ.nodup (hQ.ne0 hP.tcb),
        fun z hz => by rw [← hyq, hqx]; exact hz, IFrame.refl _ _, CnStep.refl _ _, by rw [← hqx]; exact hm0, hB0,
        hA0⟩
    refine WP.spec_bind (all_ipc_loop hP0 he s σ q _ hI0) ?_
    rintro s1 ⟨σf, hmf, hXf, hss1, hcs1, hAf⟩
    refine WP.spec_mono (WP.spec_and (resched_irel hP0 s1 σf hXf hAf)
      (reschedule_required_sfootI hXf.2.2.1)) ?_
    rintro s2 ⟨⟨σr, hrs, hkr, hX2⟩, hw2⟩
    exact ⟨σr, ⟨((), σf), hmf, by show ((), σr) ∈ (Fl4Spec.rescheduleRequired σf).1; rw [hrs]; rfl⟩, hX2,
      hss1.trans (IRel.iframe_of hXf hw2 fun b hb => sfootI_oobj hP.tcb hb),
      hcs1.trans ⟨hw2.mono fun b hb => Or.inl (SFootI.finW hP.tcb hb), SzKeepC.of (SzKeep.of_kheap hkr)⟩⟩
  cases y with
  | idleEP =>
    have h0 : i = obj.EP_IDLE := by rw [hi, hEP.1, ep_state_vals.1]
    simp only [h0, ↓reduceIte, WP.spec_ok]
    exact ⟨σ, by rw [hsp]; exact Set.mem_singleton _, hX, IFrame.refl _ _, CnStep.refl _ _⟩
  | sendEP q =>
    have h0 : i ≠ obj.EP_IDLE := by rw [hi, hEP.1, ep_state_vals.1]; decide
    simp only [h0, ↓reduceIte]
    refine WP.spec_mono (walk q rfl h0) ?_
    rintro s' ⟨σ', hm, hX', hss, hcs⟩
    exact ⟨σ', by rw [hsp]; exact hm, hX', hss, hcs⟩
  | recvEP q =>
    have h0 : i ≠ obj.EP_IDLE := by rw [hi, hEP.1, ep_state_vals.1]; decide
    simp only [h0, ↓reduceIte]
    refine WP.spec_mono (walk q rfl h0) ?_
    rintro s' ⟨σ', hm, hX', hss, hcs⟩
    exact ⟨σ', by rw [hsp]; exact hm, hX', hss, hcs⟩

end Loop

end

end Fl4Proofs.P3.Ipc

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

theorem finWork_ep {e b : U64} {x1 x2 x3 x4 : Bool} {fb : Bool} (h : FinWork (.Endpoint e b x1 x2 x3 x4) fb) :
    fb = true := by
  unfold FinWork at h
  rcases h with ⟨hb | ⟨f, l, o, e, -⟩, -⟩ | ⟨p, sz, r, d, ep, asid, va, e⟩
  · exact hb
  · cases e
  · cases e

/-- **What an endpoint cap's finalisation at `XTop` reads** (module docstring). -/
def EpFinPre (Z : XSets) (s : S) (σ : Fl4Spec.State Unit) : Prop :=
  BufWordRel Z.T (L.mem s) σ ∧ IPlaced Z.N Z.T Z.E Z.R Z.B ∧
  (∀ e ∈ Z.E, EpPre σ e.bv) ∧
  ∀ sl e b x1 x2 x3 x4, AbsSlot Z.th sl → capAt (L.mem s) (cslotAddr sl) = ok (.Endpoint e b x1 x2 x3 x4) → e ∈ Z.E

set_option maxHeartbeats 8000000 in
/-- **`XFinHyps.ep` holds** (module docstring). -/
theorem xFinEp_of {AR : A → Fl4Spec.Cr3 → Prop} {th : TypedHeap}
    (hpre : ∀ (Z : XSets) s a σ, Z.th = th → XTopAt (L := L) AR Z s a σ → EpFinPre (L := L) Z s σ) :
    XFinAt (L := L) arI FinEpK AR th := by
  intro Z s a σ sl c hth hX hK hTh ⟨e, b, x1, x2, x3, x4, hc0⟩ hDS hA hc hk hw
  subst hth hc0
  obtain ⟨hBW, hP0, hEp, heE⟩ := hpre Z s a σ rfl hX
  have he := heE sl e b x1 x2 x3 x4 hA hc
  have hfin := finWork_ep hw
  set fin := decide (Fl4Spec.isFinalCap' (absCap (.Endpoint e b x1 x2 x3 x4)) σ) with hfd
  have hI := hX.irelK hK hBW
  have hAR : AR a σ.archState.x64CurrentCr3 := hX.fin.1.1.2.2.2.2.2.2
  have hfc : objects.finalise_cap st arI s a (.Endpoint e b x1 x2 x3 x4) fin false =
      objects.finalise_cap_object st arI s a (.Endpoint e b x1 x2 x3 x4) fin := by
    simp [objects.finalise_cap]
  rw [hfc]
  unfold objects.finalise_cap_object
  simp only [hfin, ↓reduceIte]
  refine WP.spec_bind (cancel_all_ipc_irel hP0 s σ hI he (hEp e he)) ?_
  rintro s3 ⟨σ3, hm3, hI3, hk3, -⟩
  rw [WP.spec_ok]
  have hmem : ((absCap capability.Cap.Null, absCap capability.Cap.Null), σ3) ∈
      (Fl4Spec.finaliseCap (Z := Unit) (absCap (.Endpoint e b x1 x2 x3 x4)) fin σ).1 := by
    rw [hfin]
    show _ ∈ (Fl4Spec.NonDet.liftM (fun _ => (Fl4Spec.Cap.nullCap, Fl4Spec.Cap.nullCap)) (Fl4Spec.NonDet.when true
      (Fl4Spec.cancelAllIpc e.bv)) σ).1
    unfold Fl4Spec.NonDet.liftM Fl4Spec.NonDet.when
    simp only [↓reduceIte]
    exact mem_bind_nd (x := ((), σ3)) hm3 (Set.mem_singleton _)
  have hck := finEp_nkc e.bv b.bv _ fin σ _ hmem
  obtain ⟨V', hX3⟩ := XTopAt.irel_same hX hI3 hAR hk3.1 hck.cdt hck.orig hck.ks hk3.2
  have hM := hDS.1.2.2.1
  refine ⟨rfl, trivial, trivial, σ3, Z.G, hmem, DState.of_same hDS hk3.1 hX3.rel.2.1 hck.ks, ?_,
    fun y hy _ => Or.inl (hk3.1.capV hy), MdbStep.of_same hM hk3.1, ⟨V', hX3⟩, hk3.2⟩
  rw [hk3.1.capV hA.isSlot]; exact capV_of_capAt hc

end

end

end Fl4Proofs.P3
