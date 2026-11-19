/-
P3 (DESIGN.md §9), IPC: **`cancel_badged_sends` on `IRel`** (the CNode
CancelBadgedSends invocation's IPC step, `XCancelBadgedHyp`).

FL4 walks the endpoint's send queue from its head, reading each thread's
successor before the thread's step; the spec runs
`remove_and_restart_badged_thread` over the queue (`mapM_x`), then
`reschedule_required`.

* `restart_irel`: `restart_thread_if_no_fault` (the restart, the sporadic
  unblock by `unblock_irel`, the switch by `switch_top`; or Inactive for a
  faulted thread), keeping the endpoints.
* `cancel_badged_irel`: the loop, by the queue still to visit, the spec's
  outcomes from it included in the whole's (`mapMx`); FL4's fuel
  (`WALK_FUEL`) exceeds any queue (`List.length` of distinct TCB
  addresses).
* `xCancelBadged`: `XCancelBadgedHyp` from the leaf on `IRel`
  (`xleaf_of_irel`).

Named: the switch target ready (`ActReady`, as for the endpoint tails) and
the endpoint in `E`.
-/
import Fl4Proofs.P3.IpcEpTail
import Fl4Proofs.P3.IpcXTop
import Fl4Proofs.P3.XTopCnode
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Ipc
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Sched

noncomputable section

section Restart
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

/-- The spec's restart after the fault check, as the sporadic check then the
switch. -/
theorem restart_spec_eq (t : Fl4Spec.ObjRef) :
    (do
      let scOpt ← Fl4Spec.getTcbObjRef (Z := Unit) Fl4Spec.Tcb.tcbSchedContext t
      Fl4Spec.ifSporadicCurScAssertRefillUnblockCheck scOpt
      Fl4Spec.possibleSwitchTo t : Fl4Spec.SMonad Unit Unit) =
      (specSporadicAssert t >>= fun _ => Fl4Spec.possibleSwitchTo t) := by
  unfold specSporadicAssert; rw [nd_bind_assoc_fun]

set_option maxHeartbeats 2000000 in
/-- **`restart_thread_if_no_fault` on `IRel`**, keeping the other
endpoints. -/
theorem restart_irel (hP0 : IPlaced N T E R B)
    (s : S) (σ : Fl4Spec.State Unit) (hX : IRel st th cr N T C E R B c s σ) {t : U64} (ht : t ∈ T)
    {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x)) (hns : tsCode x.tcbState ≠ 6)
    (hq : ∀ e ∈ E, ∀ z, σ.kheap e.bv = some (.endpoint z) → t.bv ∉ z.epQueue)
    (hxs : x.tcbFault = none → ScOK σ x) (hBk : ScBack σ) (hAr : ActReady σ) :
    endpoint.restart_thread_if_no_fault st s t ⦃ s' => ∃ σ', ((), σ') ∈ (Fl4Spec.restartThreadIfNoFault (Z := Unit) t.bv σ).1 ∧
      IRel st th cr N T C E R B c s' σ' ∧
      (∀ p y, σ.kheap p = some (.endpoint y) → σ'.kheap p = some (.endpoint y)) ∧ RtFacts σ σ' t.bv x ⦄ := by
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
    refine WP.spec_bind (set_thread_state_c hH hP0 hP s σ hX.1.toE (IpcRel.toSRN hX.1 hX.2) ht hk hq hns
      .restart (by decide) sched.TS_RESTART hcode) ?_
    rintro s1 ⟨hE1, hS1⟩
    have hX1 := IpcRel.ofSRN hE1 hS1
    rw [endpoint_unblock_sporadic_eq]
    refine WP.spec_bind (unblock_irel hP0 s1 _ hX1 t ht) ?_
    rintro s2 ⟨σ2, hu, hf2, hv2, hX2⟩
    have hkt1 : (stsAct (updK σ t.bv (.tcb { x with tcbState := .restart })) t.bv).kheap t.bv =
        some (.tcb { x with tcbState := .restart }) := by rw [stsAct_kheap]; simp [updK]
    obtain ⟨σm, hmm, hktm, hBm, hAm, hTm, htm, hkpm⟩ := restart_tail_mid hk (hxs hf) hBk hAr
    have e2 : σm = σ2 := by
      have hmem : ((), σm) ∈ (specUnblock t.bv (stsAct (updK σ t.bv (.tcb { x with tcbState := .restart })) t.bv)).1 := by
        rw [← specSporadicAssert_eq]; unfold specSporadicAssert
        rw [nd_bind_one (show Fl4Spec.getTcbObjRef (Z := Unit) Fl4Spec.Tcb.tcbSchedContext t.bv _ = _ from
          threadGet_eq _ hkt1)]
        exact hmm
      rw [hu] at hmem
      exact (Prod.mk.inj (Set.mem_singleton_iff.1 hmem)).2
    rw [e2] at hktm hBm hAm hTm htm hkpm
    refine WP.spec_mono (switch_top hP0 s2 σ2 hX2.1 hX2.2 hAm t ht) ?_
    rintro s3 ⟨σ3, hps, hk3, hf3, hv3, hS3⟩
    obtain ⟨σ6, he6, hk6, ht6, hr6, ha6⟩ := pst_ok hktm hAm
    have e3 : σ6 = σ3 := by
      have h : ((), σ6) ∈ (Fl4Spec.possibleSwitchTo (Z := Unit) t.bv σ2).1 := by rw [he6]; rfl
      rw [hps] at h; exact (Prod.mk.inj (Set.mem_singleton_iff.1 h)).2
    rw [e3] at hk6 ht6 hr6 ha6
    have hRF : RtFacts σ σ3 t.bv x := ⟨(SFr.of_heap hk6 ht6 hr6).scBack hBm, pst_actReady hAm hTm hk6 ht6 hr6 ha6,
      by rw [ht6, htm], fun p hp hpc => by rw [hk6, hkpm p hp hpc]⟩
    refine ⟨σ3, ?_, ⟨hX2.1.frame hP0 hf3 hv3, hS3⟩, fun p y hy => ?_, hRF⟩
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
    refine WP.spec_mono (set_thread_state_c hH hP0 hP s σ hX.1.toE (IpcRel.toSRN hX.1 hX.2) ht hk hq hns
      .inactive (by decide) sched.TS_INACTIVE hcode) ?_
    rintro s1 ⟨hE1, hS1⟩
    obtain ⟨σi, hei, hBi, hAi, hti, -, hkpi⟩ := inactive_ok hk hBk hAr
    rw [Notif.setThreadState_eq .inactive hk] at hei
    have ei := (Prod.mk.inj (singleton_one_eq hei)).2
    have hRF : RtFacts σ (stsAct (updK σ t.bv (.tcb { x with tcbState := .inactive })) t.bv) t.bv x := by
      rw [ei]; exact ⟨hBi, hAi, hti, fun p hp _ => hkpi p hp⟩
    refine ⟨_, ?_, IpcRel.ofSRN hE1 hS1, fun p y hy => ?_, hRF⟩
    · unfold Fl4Spec.restartThreadIfNoFault
      rw [nd_bind_one (threadGet_eq _ hk)]
      simp only [hf, ↓reduceIte]
      rw [Notif.setThreadState_eq .inactive hk]
      rfl
    · rw [stsAct_kheap]; simp [updK, hkp p y hy, hy]

/-- **`reschedule_required` on `IRel`** (as `switch_top`). -/
theorem resched_irel (hP0 : IPlaced N T E R B) (s : S) (σ : Fl4Spec.State Unit)
    (hX : IRel st th cr N T C E R B c s σ) (hr : ActReady σ) :
    sched.reschedule_required st s ⦃ s' => ∃ σ', Fl4Spec.rescheduleRequired (Z := Unit) σ = ({((), σ')}, False) ∧
      σ'.kheap = σ.kheap ∧ IRel st th cr N T C E R B c s' σ' ⦄ := by
  obtain ⟨hR, hS⟩ := hX
  refine WP.spec_mono (WP.spec_and (reschedule_required_refines s σ hR.toN hS.2.1 hr)
    (reschedule_required_sfootI hS.2.1)) ?_
  rintro s' ⟨⟨σ', heq, hk, -, -, hSch⟩, hW⟩
  have hmem : ((), σ') ∈ (Fl4Spec.rescheduleRequired (Z := Unit) σ).1 := by rw [heq]; rfl
  obtain ⟨hms, hdl, hds, har, hist, hino, hct⟩ := nkm_rescheduleRequired σ _ hmem
  have hck : CKeep σ σ' := nkc_rescheduleRequired σ _ hmem
  have hf : Agree (L.mem s) (L.mem s') (IFoot N T E R B) :=
    fun a ha hf => hW.mem_eq ha (fun hs => sfootI_not_ifoot hP0 hS.2.1 hS.2.2 hs hf)
  have hv : IKView σ σ' := IKView.of_kheap hk (by rw [hms])
  refine ⟨σ', heq, hk, hR.frame hP0 hf hv, hS.1.frameN hW (fun a ha => sfootI_iwords hP0.e.tcb ha) (fun a ha => sfootI_nobuf hP0.e.tcb ha) hck hdl hds
    (VsKeep.of_kheap hk har hist hino hct), hSch, hS.2.2.mono hW.1 (SzKeep.of_kheap hk)⟩

end Restart


/-! ## The loop -/

section Loop
open Fl4Spec in
/-- One step of the spec's loop. -/
abbrev rrb (e b : U64) (t : ObjRef) : SMonad Unit Unit := removeAndRestartBadgedThread t e.bv b.bv

theorem mapMx_cons_mem {σ' σ'' : Fl4Spec.State Unit} {g : Fl4Spec.ObjRef → Fl4Spec.SMonad Unit Unit}
    {a : Fl4Spec.ObjRef} {l : List Fl4Spec.ObjRef} (h : ((), σ'') ∈ (g a σ').1) :
    ∀ z, z ∈ (Fl4Spec.NonDet.mapMx g l σ'').1 → z ∈ (Fl4Spec.NonDet.mapMx g (a :: l) σ').1 :=
  fun z hz => ⟨((), σ''), h, hz⟩

theorem epDeq_send_queue {y : Fl4Spec.Endpoint} (hnr : ∀ q, y ≠ .recvEP q) (t : Fl4Spec.ObjRef) :
    (epDeq y t).epQueue = Fl4Spec.removeAll t y.epQueue ∧ ∀ q, epDeq y t ≠ .recvEP q := by
  unfold epDeq
  split
  · rename_i h; exact ⟨by rw [h]; rfl, fun q e => by cases e⟩
  · cases y with
    | idleEP => rename_i h; exact absurd rfl h
    | sendEP q => exact ⟨rfl, fun q' e => by cases e⟩
    | recvEP q => exact absurd rfl (hnr q)

theorem len_le_max (l : List U64) (hnd : l.Nodup) (h0 : ∀ x ∈ l, x ≠ 0#u64) : l.length ≤ 2 ^ 64 - 1 := by
  have hnd' : (l.map (fun x : U64 => x.val)).Nodup := hnd.map (fun a b h => UScalar.eq_of_val_eq h)
  calc l.length = (l.map (fun x : U64 => x.val)).toFinset.card := by
        rw [List.toFinset_card_of_nodup hnd', List.length_map]
    _ ≤ (Finset.Icc 1 (2 ^ 64 - 1)).card := by
        apply Finset.card_le_card
        intro v hv
        simp only [List.mem_toFinset, List.mem_map] at hv
        obtain ⟨x, hx, rfl⟩ := hv
        have h1 : x.val ≠ 0 := fun e => h0 x hx (UScalar.eq_of_val_eq (by simpa using e))
        have h2 := x.hBounds
        simp only [Finset.mem_Icc]
        constructor <;> scalar_tac
    _ = 2 ^ 64 - 1 := by simp

end Loop

section Loop2
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

variable (st th cr N T C E R B c) in
/-- The loop's invariant: the queue still to visit `rest` (after the kept
`kept`), FL4's cursor at its head, the spec's outcomes from it among the
whole loop's. -/
def BInv (e b : U64) (σ0 : Fl4Spec.State Unit) (q0 : List Fl4Spec.ObjRef) (x : S × U64 × U64) : Prop :=
  ∃ σ' y, ∃ kept rest : List U64, IRel st th cr N T C E R B c x.1 σ' ∧ σ'.kheap e.bv = some (.endpoint y) ∧
    y.epQueue = (kept ++ rest).map UScalar.bv ∧ (∀ q, y ≠ .recvEP q) ∧ x.2.1 = rest.headD 0#u64 ∧
    rest.length ≤ x.2.2.val ∧
    (∀ z, z ∈ (Fl4Spec.NonDet.mapMx (rrb e b) (rest.map UScalar.bv) σ').1 →
      z ∈ (Fl4Spec.NonDet.mapMx (rrb e b) q0 σ0).1) ∧
    (∀ u ∈ rest.map UScalar.bv, MemOKE σ' u) ∧ ScBack σ' ∧ ActReady σ'

set_option maxHeartbeats 4000000 in
/-- **The loop of `cancel_badged_sends`** on `IRel`. -/
theorem badged_loop (hP0 : IPlaced N T E R B)
    {e b : U64} (he : e ∈ E) (σ0 : Fl4Spec.State Unit) (q0 : List Fl4Spec.ObjRef) (x0 : S × U64 × U64)
    (h0 : BInv st th cr N T C E R B c e b σ0 q0 x0) :
    endpoint.cancel_badged_sends_loop st x0.1 e b x0.2.1 x0.2.2 ⦃ s' => ∃ σf,
      ((), σf) ∈ (Fl4Spec.NonDet.mapMx (rrb e b) q0 σ0).1 ∧ IRel st th cr N T C E R B c s' σf ∧
      ActReady σf ⦄ := by
  have hP := hP0.e
  have hH := ipcCore_top (st := st) (th := th) (cr := cr) (N := N) (C := C) (c := c) hP
  unfold endpoint.cancel_badged_sends_loop
  apply loop.spec_decr_nat (measure := fun x : S × U64 × U64 => x.2.2.val)
    (inv := BInv st th cr N T C E R B c e b σ0 q0) _ _ x0 ?_ h0
  rintro ⟨s, t, fuel⟩ ⟨σ', y, kept, rest, hX, hky, hq, hnr, ht, hlen, hinc, hmm, hBk, hAr⟩
  simp only at hX hky hq hnr ht hlen hinc hmm hBk hAr ⊢
  have hEP := hX.1.toE.at_ep he hky
  obtain ⟨xs, hQ, hxs, hB⟩ := hEP.queue
  have hxs' : xs = kept ++ rest := by
    rw [hq] at hxs
    exact (List.map_injective_iff.2 (fun a b h => eq_of_bv h) hxs).symm
  subst hxs'
  unfold endpoint.cancel_badged_sends_loop.body
  step with obj.Tcb.is_null.spec as ⟨bn, hbn⟩
  cases rest with
  | nil =>
    simp only [List.headD_nil] at ht
    subst ht
    simp only [hbn, decide_true, ↓reduceIte, WP.spec_ok]
    exact ⟨σ', hinc _ rfl, hX, hAr⟩
  | cons t0 rest' =>
    simp only [List.headD_cons] at ht
    subst t
    have ht0T : t0 ∈ T := hQ.mem t0 (by simp)
    have ht00 : t0 ≠ 0#u64 := hQ.ne0 hP.tcb t0 (by simp)
    simp only [hbn, ht00, decide_false, Bool.false_eq_true, ↓reduceIte]
    have hf0 : fuel > 0#u64 := by
      simp only [List.length_cons] at hlen
      show (0#u64 : U64).val < fuel.val; simp; omega
    simp only [hf0, ↓reduceIte]
    step as ⟨fuel1, hfuel1⟩
    -- the successor
    have hseg := hQ.seg
    rw [Seg_mid] at hseg
    obtain ⟨-, -, hnext, -⟩ := hseg
    unfold tcbqueue.next_of
    step with tcbqueue.next.spec as ⟨nx, hnx⟩
    try simp only [bind_ok]
    -- the thread's state
    obtain ⟨hbe, hcode⟩ := hB t0 (by simp)
    obtain ⟨xt, hkt, hTR⟩ := hX.1.tcb t0 ht0T
    have hTRE := hX.1.toE.at_tcb ht0T hkt
    have h4 : (L.mem s (tStA t0)).val = 4 := by
      cases y with
      | idleEP => simp [Fl4Spec.Endpoint.epQueue] at hq
      | recvEP q => exact absurd rfl (hnr q)
      | sendEP q =>
        obtain ⟨-, ys, -, hys, hQ', hqo⟩ := hEP
        have := hQ'.unique hP.tcb hQ
        rw [this] at hqo
        exact (hqo t0 (by simp)).1
    obtain ⟨e', d, hst⟩ : ∃ e' d, xt.tcbState = .blockedOnSend e' d := by
      have := hTRE.st; rw [h4] at this
      cases h : xt.tcbState <;> rw [h] at this <;> simp [tsCode] at this
      exact ⟨_, _, rfl⟩
    have he' : e' = e.bv := by
      rw [← hTRE.blk e' (by simp [hst, Fl4Spec.epBlocked]), hbe]
    subst he'
    have hbdg : (L.mem s (tBadgeA t0)).bv = d.senderBadge := (hTRE.send _ d hst).1
    step with obj.Tcb.block_badge.spec as ⟨i, hi⟩
    subst hi
    have hspec0 : ∀ m : Fl4Spec.SMonad Unit Unit,
        rrb e b t0.bv σ' = (Fl4Spec.NonDet.when (d.senderBadge = b.bv) m) σ' →
        True := fun _ _ => trivial
    by_cases hm : L.mem s (tBadgeA t0) = b
    · -- dequeued and restarted
      simp only [hm, ↓reduceIte]
      have hd : t0.bv ∈ y.epQueue := by rw [hq]; simp
      refine WP.spec_bind (ep_dequeue_c hH hP0 hP s σ' hX.1.toE (IpcRel.toSRN hX.1 hX.2) he hky hd) ?_
      rintro s1 ⟨hdq, hR1, hS1, hA1⟩
      have hX1 := IpcRel.ofSRN hR1 hS1
      set σd := updK σ' e.bv (.endpoint (epDeq y t0.bv)) with hσd
      have hte : t0.bv ≠ e.bv := by intro h; rw [h, hky] at hkt; cases hkt
      have hktd : σd.kheap t0.bv = some (.tcb xt) := by simp [hσd, updK, hte, hkt]
      have hkyd : σd.kheap e.bv = some (.endpoint (epDeq y t0.bv)) := by simp [hσd, updK]
      have hta := hP.tcb t0 ht0T
      have hb1 : L.mem s1 (tBlockA t0) = e := (hA1 _ (a_blk hta).1 ⟨t0, ht0T, (a_blk hta).2⟩).trans hbe
      obtain ⟨hdqq, hdnr⟩ := epDeq_send_queue hnr t0.bv
      have hnd : (kept ++ t0 :: rest').Nodup := hQ.nodup
      have hrm : Fl4Spec.removeAll t0.bv y.epQueue = (kept ++ rest').map UScalar.bv := by
        rw [hq, removeAll_map hnd]
        congr 1
        have hnk : t0 ∉ kept := fun h => by
          have := List.nodup_append.1 hnd
          exact this.2.2 _ h _ (by simp) rfl
        rw [List.erase_append_right _ hnk, List.erase_cons_head]
      have hnq : t0.bv ∉ (epDeq y t0.bv).epQueue := by
        rw [hdqq, hrm, List.mem_map]
        rintro ⟨z, hz, ez⟩
        have : z = t0 := eq_of_bv ez
        subst this
        have := List.nodup_append.1 hnd
        rcases List.mem_append.1 hz with h | h
        · exact this.2.2 _ h _ (by simp) rfl
        · exact (List.nodup_cons.1 this.2.1).1 h
      have hq1 := dequeued_not_queued hR1 he hb1 hkyd hnq
      -- the spec's facts at the dequeued state
      have hFd : SFr σ' σd := SFr.updOther hky (fun _ h => by cases h)
        (fun _ _ h => by cases h) (fun _ h => by cases h) (fun _ _ h => by cases h)
      have hBd : ScBack σd := hFd.scBack hBk
      have hxsd : xt.tcbFault = none → ScOK σd xt := by
        obtain ⟨x', hk', hsc⟩ := MemOKE.updOther (o' := .endpoint (epDeq y t0.bv)) hky (fun _ h => by cases h)
          (fun _ _ h => by cases h) (hmm t0.bv (by simp))
        rw [hktd] at hk'; cases hk'; exact hsc
      refine WP.spec_bind (restart_irel hP0 s1 σd hX1 ht0T hktd (by rw [hst]; simp [tsCode]) hq1 hxsd hBd
        (hFd.actReady hAr (Or.inl rfl))) ?_
      rintro s2 ⟨σ'', hres, hX2, hkeep, hB'', hA'', ht'', hkp''⟩
      have hnd' : t0 ∉ rest' := (List.nodup_cons.1 (List.nodup_append.1 hnd).2.1).1
      rw [WP.spec_ok]
      refine ⟨⟨σ'', epDeq y t0.bv, kept, rest', hX2, hkeep _ _ hkyd, by rw [hdqq, hrm], hdnr,
        by rw [hnx, hnext], ?_, ?_, fun u hu => ?_, hB'', hA''⟩, ?_⟩
      · rw [hfuel1]; simp only [List.length_cons] at hlen; scalar_tac
      · refine fun z hz => hinc z (mapMx_cons_mem (l := rest'.map UScalar.bv) ?_ z hz)
        show ((), σ'') ∈ (Fl4Spec.removeAndRestartBadgedThread (Z := Unit) t0.bv e.bv b.bv σ').1
        unfold Fl4Spec.removeAndRestartBadgedThread
        rw [nd_bind_one (getThreadState_eq hkt), hst]
        have hb' : Fl4Spec.blockingIpcBadge (.blockedOnSend e.bv d) = b.bv := by
          rw [Fl4Spec.blockingIpcBadge, ← hbdg, hm]
        simp only [Fl4Spec.NonDet.when, hb', ↓reduceIte]
        exact ⟨((), σd), by rw [hdq]; rfl, hres⟩
      · obtain ⟨u0, hu0, rfl⟩ := List.mem_map.1 hu
        exact memOK_after hktd hBd (fun h => hnd' (eq_of_bv h ▸ hu0))
          (MemOKE.updOther (o' := .endpoint (epDeq y t0.bv)) hky (fun _ h => by cases h) (fun _ _ h => by cases h)
            (hmm _ (List.mem_map_of_mem (List.mem_cons_of_mem _ hu0)))) hkp'' ht''
      · rw [hfuel1]; scalar_tac
    · -- kept
      simp only [hm, ↓reduceIte, WP.spec_ok]
      refine ⟨⟨σ', y, kept ++ [t0], rest', hX, hky, by rw [hq]; simp, hnr, by rw [hnx, hnext], ?_, ?_,
        fun u hu => hmm u (by simp only [List.map_cons, List.mem_cons]; exact Or.inr hu), hBk, hAr⟩, ?_⟩
      · rw [hfuel1]; simp only [List.length_cons] at hlen; scalar_tac
      · refine fun z hz => hinc z (mapMx_cons_mem (l := rest'.map UScalar.bv) ?_ z hz)
        show ((), σ') ∈ (Fl4Spec.removeAndRestartBadgedThread (Z := Unit) t0.bv e.bv b.bv σ').1
        unfold Fl4Spec.removeAndRestartBadgedThread
        rw [nd_bind_one (getThreadState_eq hkt), hst]
        have hb' : Fl4Spec.blockingIpcBadge (.blockedOnSend e.bv d) ≠ b.bv := by
          rw [Fl4Spec.blockingIpcBadge, ← hbdg]; exact fun h => hm (eq_of_bv h)
        simp only [Fl4Spec.NonDet.when, hb', ↓reduceIte]
        rfl
      · rw [hfuel1]; scalar_tac

set_option maxHeartbeats 4000000 in
/-- **`cancel_badged_sends` on `IRel`.** -/
theorem cancel_badged_irel (hP0 : IPlaced N T E R B)
    (s : S) (σ : Fl4Spec.State Unit) (hX : IRel st th cr N T C E R B c s σ) {e : U64} (he : e ∈ E) (b : U64)
    (hpre : EpQPre σ e.bv) :
    endpoint.cancel_badged_sends st s e b ⦃ s' => ∃ σ',
      ((), σ') ∈ (Fl4Spec.cancelBadgedSends (Z := Unit) e.bv b.bv σ).1 ∧ IRel st th cr N T C E R B c s' σ' ⦄ := by
  have hP := hP0.e
  obtain ⟨y, hky, hEP⟩ := hX.1.toE.ep e he
  obtain ⟨hm0, hB0, hA0⟩ := hpre y hky
  unfold endpoint.cancel_badged_sends
  step with obj.Ep.state.spec as ⟨i, hi⟩
  rw [epState_eq] at hi
  have hsp : ∀ (m : Fl4Spec.SMonad Unit Unit),
      Fl4Spec.cancelBadgedSends (Z := Unit) e.bv b.bv σ = (match y with
        | .sendEP queue => (do Fl4Spec.NonDet.mapMx (fun t => Fl4Spec.removeAndRestartBadgedThread t e.bv b.bv) queue
                               Fl4Spec.rescheduleRequired)
        | _ => return ()) σ := by
    intro _
    unfold Fl4Spec.cancelBadgedSends
    rw [nd_bind_one (getEndpoint_eq hky)]
    rfl
  cases y with
  | idleEP =>
    have h0 : i ≠ obj.EP_SEND := by rw [hi, hEP.1, ep_state_vals.2.1]; decide
    simp only [h0, bne_iff_ne, ne_eq, not_false_eq_true, ↓reduceIte, WP.spec_ok]
    exact ⟨σ, by rw [hsp (pure ())]; rfl, hX⟩
  | recvEP q =>
    have h0 : i ≠ obj.EP_SEND := by rw [hi, hEP.1, ep_state_vals.2.1]; decide
    simp only [h0, bne_iff_ne, ne_eq, not_false_eq_true, ↓reduceIte, WP.spec_ok]
    exact ⟨σ, by rw [hsp (pure ())]; rfl, hX⟩
  | sendEP q =>
    have h0 : i = obj.EP_SEND := by rw [hi, hEP.1, ep_state_vals.2.1]
    simp only [h0, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    obtain ⟨-, xs, -, hqx, hQ, -⟩ := hEP
    step with endpoint.get_queue.spec as ⟨qq, hqq⟩
    have hfuel : layout.WALK_FUEL.val = 2 ^ 64 - 1 := by simp [layout.WALK_FUEL, U64.rMax]
    have hI0 : BInv st th cr N T C E R B c e b σ q (s, qq.head, layout.WALK_FUEL) :=
      ⟨σ, .sendEP q, [], xs, hX, hky, by rw [hqx]; rfl, (fun q' e' => by cases e'),
        by rw [hqq, epQ_eq, hQ.head], by rw [hfuel]; exact len_le_max xs hQ.nodup (hQ.ne0 hP.tcb),
        fun z hz => by rw [hqx]; exact hz, fun u hu => hm0 u (by show u ∈ q; rw [hqx]; simpa using hu),
        hB0, hA0⟩
    refine WP.spec_bind (badged_loop hP0 he σ q _ hI0) ?_
    rintro s1 ⟨σf, hmf, hXf, hAf⟩
    refine WP.spec_mono (resched_irel hP0 s1 σf hXf hAf) ?_
    rintro s2 ⟨σr, hrs, -, hX2⟩
    refine ⟨σr, ?_, hX2⟩
    rw [hsp (pure ())]
    exact ⟨((), σf), hmf, by show ((), σr) ∈ (Fl4Spec.rescheduleRequired σf).1; rw [hrs]; rfl⟩

end Loop2

end

end Fl4Proofs.P3.Ipc

namespace Fl4Proofs.P3
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc

noncomputable section

/-! ## `XCancelBadgedHyp` -/

section X
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type}

set_option maxHeartbeats 4000000 in
/-- **`XCancelBadgedHyp`**: the caller's restart then `cancel_badged_sends`
on `IRel` at every `Z` the entry's `XTopAt` holds at. Named, at `Z`:
`KsApart`, `BufWordRel`, the placement, the caller in `Z.T`, the endpoint in `Z.E`; and
at the entry's spec state the endpoint's queued threads' facts, `ScBack`,
`ActReady` (`EpQPre`), the caller not the switch target. -/
theorem xCancelBadged {AR : A → Fl4Spec.Cr3 → Prop} {s : S} {ar : A} {σ σ1 : Fl4Spec.State Unit} {ct : U64}
    (hcur : σ.curThread = ct.bv) {xt : Fl4Spec.Tcb} (hkt : σ.kheap ct.bv = some (.tcb xt))
    (hrun : tsCode xt.tcbState < 3)
    (hst : Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False)) {p b : U64}
    (hZ : ∀ Z : XSets, XTopAt (L := L) AR Z s ar σ → KsApart Z.N Z.T Z.E Z.R Z.B (L.ksb s) ∧
      BufWordRel Z.T (L.mem s) σ ∧ IPlaced Z.N Z.T Z.E Z.R Z.B ∧ ct ∈ Z.T ∧ p ∈ Z.E)
    (hQ : Sched.EpQPre σ p.bv) (hsw : ∀ u, σ.schedulerAction = .switchThread u → u ≠ ct.bv) :
    XCancelBadgedHyp (L := L) AR s ar σ σ1 ct p b := by
  rintro ⟨Z, hX⟩
  obtain ⟨hKA, hBT, hP0, hct, hp⟩ := hZ Z hX
  have hI := hX.irelK hKA hBT
  have hP := hP0.e
  -- the leaf on `IRel`, with the arch state returned unchanged
  have leaf : (do
      let s1 ← sched.set_thread_state st s ct sched.TS_RESTART
      let s2 ← endpoint.cancel_badged_sends st s1 p b
      ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s2, ar)) ⦃ r => (r.1 = .Ok () ∧
        ∃ z ∈ (Fl4Spec.cancelBadgedSends (Z := Unit) p.bv b.bv σ1).1, RelTopM (L := L) r.2.1 z.2 ∧
          IRel st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c r.2.1 z.2) ∧ r.2.2 = ar ⦄ := by
    obtain ⟨hIR, hSRT⟩ := hI
    obtain ⟨xt0, hk0, hTR⟩ := hIR.tcb ct hct
    rw [hkt] at hk0; cases hk0
    have hq := IpcRel.not_ep_queued hIR (t := ct) (by rw [hTR.st]; omega)
    have hcode : sched.TS_RESTART.val = tsCode .restart := by unfold sched.TS_RESTART; rfl
    have hH := ipcCore_top (st := st) (th := Z.th) (cr := σ.archState.x64CurrentCr3) (N := Z.N) (C := Z.C)
      (c := Z.c) hP
    refine WP.spec_bind (set_thread_state_c hH hP0 hP s σ hIR.toE (IpcRel.toSRN hIR hSRT) hct hkt hq
      (by omega) .restart (by decide) sched.TS_RESTART hcode) ?_
    rintro s1 ⟨hE1, hS1⟩
    rw [hcur, Notif.setThreadState_eq .restart hkt] at hst
    have hσ1 : σ1 = stsAct (updK σ ct.bv (.tcb { xt with tcbState := .restart })) ct.bv := by
      have := congrArg (fun q => ((), σ1) ∈ q.1) hst
      simp only [Set.mem_singleton_iff, Prod.mk.injEq, true_and, iff_true] at this
      simpa using this.symm
    subst hσ1
    refine WP.spec_bind (cancel_badged_irel hP0 s1 _ (IpcRel.ofSRN hE1 hS1) hp b (Sched.epQPre_restart hkt hQ hsw)) ?_
    rintro s2 ⟨σ2, hm, hX2⟩
    rw [WP.spec_ok]
    exact ⟨⟨rfl, ((), σ2), hm, (SRT.relTop hX2).1, hX2⟩, rfl⟩
  have hAR : AR ar σ.archState.x64CurrentCr3 := hX.fin.1.1.2.2.2.2.2.2
  refine WP.spec_mono leaf ?_
  rintro r ⟨⟨h1, z, hz, hRT, hIz⟩, ha⟩
  obtain ⟨⟨Z', -, -, -, -, -, -, -, -, hZ'⟩, -⟩ := IRel.xtop (AR := AR) (a := r.2.2) hIz (by rw [ha]; exact hAR)
  exact ⟨h1, z, hz, hRT, Z', hZ'⟩

end X

end

end Fl4Proofs.P3
