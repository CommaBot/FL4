/-
P3 (DESIGN.md §9), IPC: **`send_signal`'s wake-up of the idle
notification's bound thread blocked receiving, on `IRel`**, with its
footprint, toward `SignalRestJHyp` (ScSignalJ).

* `CnW`: the words of a notification's finalisation (`FinW`), the endpoints'
  two words and the replies' `TCB` words: `cancel_ipc`'s footprint.
* `cancel_ipc_recvF`: IpcCancel's `cancel_ipc_recvI` for `SRT … SRE` with
  the footprint `CnW` (the fault word, `ep_dequeue`'s endpoint words and the
  waiters' links, `QAgree`; `reply_unlink`'s reply word; `set_thread_state`'s
  `SFoot`).
* `send_signal_bound_irel`: the idle notification `n` bound to `t` blocked
  receiving: `cancel_ipc_recvF`, then `wake_irel` (IpcSignalWake, no SC
  donation: `NoDon` after the cancel given), `IRel` after, the slots kept
  (`IFrame`), the footprints `CnW` then `FinStep`.
-/
import Fl4Proofs.P3.IpcSignalWake
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Ipc
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Sched

noncomputable section

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]
variable {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

/-- **`cancel_ipc`'s footprint** (module docstring). -/
def CnW (T N C E R : Set U64) (c : U64) (s : S) (σ : Fl4Spec.State Unit) (b : U64) : Prop :=
  FinW (st := st) T N C c s σ b ∨ (∃ e ∈ E, EW e b) ∨ (∃ r ∈ R, b.val = r.val)

/-- `CnW`'s words are words of the other objects. -/
theorem CnW.oobj {s : S} {σ : Fl4Spec.State Unit} (hS : SchedRel st N T C c s σ) {b : U64}
    (h : CnW (st := st) T N C E R c s σ b) : Vs.OObj st N T C E R B c s σ b := by
  rcases h with (hk | ⟨y, hy, K, h1, h2, -, -, -, e⟩) | ⟨e, he, h | h⟩ | ⟨r, hr, h⟩
  · exact tfoot_oobj hS (Or.inl hk)
  · exact Or.inr (Or.inr (Or.inl ⟨y, hy, by omega, by omega⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨e, he, by omega, by omega⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨e, he, by omega, by omega⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨r, hr, by omega, by omega⟩))))

set_option maxHeartbeats 8000000 in
/-- **`cancel_ipc` of a thread blocked on a receive, with its footprint**
(module docstring). -/
theorem cancel_ipc_recvF (hP0 : IPlaced N T E R B) (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hX : IRel st th cr N T C E R B c s σ) {t : U64} (ht : t ∈ T) {x : Fl4Spec.Tcb}
    (hk : σ.kheap t.bv = some (.tcb x)) (hrb : Fl4Spec.receiveBlocked x.tcbState = true)
    (hC : CancelRecvHyp E (L.mem s) σ t x) :
    ipc.cancel_ipc st ar s a t ⦃ r => r.2 = a ∧ ∃ σ' x', Fl4Spec.cancelIpc (Z := Unit) t.bv σ = ({((), σ')}, False) ∧
      IRel st th cr N T C E R B c r.1 σ' ∧ σ'.kheap t.bv = some (.tcb x') ∧
      x'.tcbState = .inactive ∧ RelIfBound σ' t.bv ∧ WritesIn st s r.1 (CnW (st := st) T N C E R c s σ) ⦄ := by
  have hP := hP0.e
  have hH := ipcCore_top (st := st) (th := th) (cr := cr) (N := N) (C := C) (c := c) hP
  obtain ⟨hR, hSR⟩ := hX
  have hta := hP.tcb t ht
  obtain ⟨e, ro, d, hst⟩ : ∃ e ro d, x.tcbState = .blockedOnReceive e ro d := by
    cases h : x.tcbState <;> simp [h, Fl4Spec.receiveBlocked] at hrb
    exact ⟨_, _, _, rfl⟩
  obtain ⟨x0, hk0, hx⟩ := hR.tcb t ht
  rw [hk] at hk0; injection hk0 with hk0; injection hk0 with hk0; subst hk0
  have hevb : (L.mem s (tBlockA t)).bv = e := hx.blkE e (by simp [Fl4Spec.epBlocked, hst])
  subst hevb
  set ev := L.mem s (tBlockA t) with hev
  obtain ⟨z, hkz, hqz⟩ := hC.ok.2.1 _ ro d hst
  have heE : ev ∈ E := hC.ep
  have hrec := hx.recv _ ro d hst
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
  have hst1 : x1.tcbState = .blockedOnReceive ev.bv ro d := hst
  have hts : Fl4Spec.threadSet (Z := Unit) (fun tcb => { tcb with tcbFault := none }) t.bv σ =
      ({((), σ1)}, False) := threadSet_eq _ hk
  have hw3 : L.mem s1 (P1.stA t) = sched.TS_BLOCKED_ON_RECV := by
    rw [P1.stA_eq, ← tStA_eq, g _ (a_st hta).1 (by rw [val_st hta]; omega)]
    have h3 := hx.st
    rw [hst] at h3
    apply UScalar.eq_of_val_eq
    rw [h3, tsVals.2.2.1]; rfl
  have hb1 : L.mem s1 (tBlockA t) = ev := g _ (a_blk hta).1 (by rw [val_blk hta]; omega)
  have hr1 : L.mem s1 (tReplyA t) = L.mem s (tReplyA t) := g _ (a_reply hta).1 (by rw [val_reply hta]; omega)
  have hRS : sched.TS_BLOCKED_ON_RECV ≠ sched.TS_BLOCKED_ON_SEND := by
    rw [tsVals.2.2.1, tsVals.2.2.2.1]; decide
  have hspec0 : ∀ (σ' : Fl4Spec.State Unit),
      Fl4Spec.blockedCancelIpc (Z := Unit) (.blockedOnReceive ev.bv ro d) t.bv ro σ1 = ({((), σ')}, False) →
      Fl4Spec.cancelIpc (Z := Unit) t.bv σ = ({((), σ')}, False) := by
    intro σ' h
    unfold Fl4Spec.cancelIpc
    rw [nd_bind_one (getThreadState_eq hk), nd_bind_one hts, hst]
    exact h
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
  rw [hw, hw3, if_neg hRS, if_pos rfl]
  simp only [↓reduceIte]
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
  have hr2 : L.mem s2 (tReplyA t) = L.mem s (tReplyA t) :=
    (hA2 _ (a_reply hta).1 ⟨t, ht, (a_reply hta).2⟩).trans hr1
  have hq2 : ∀ e ∈ E, ∀ z', σ2.kheap e.bv = some (.endpoint z') → t.bv ∉ z'.epQueue :=
    dequeued_not_queued hR2 heE hb2 (x := epDeq z t.bv) (by simp [hσ2, updK]) (epDeq_not_mem _)
  have hK2 : SKeep σ σ2 := (SKeep.updK (o := .tcb x1) (fun y h => ⟨x, hk, by cases h; rfl⟩)
    (fun _ _ h => by cases h)).trans (SKeep.updK (fun _ h => by cases h) (fun _ _ h => by cases h))
  have hW02 : WritesIn st s s2 (CnW (st := st) T N C E R c s σ) :=
    fin _ _ (hW1.trans hW2) fun b hb => hb.elim (cF b) (cE xs hQ.mem b)
  step with Fl4Proofs.P1.obj.Tcb.reply_obj.spec as ⟨i, hi⟩
  have hi' : i = L.mem s (tReplyA t) := by rw [hi]; exact hr2
  split
  · -- a reply object
    rename_i hnz
    have hi0 : i ≠ 0#u64 := by simpa using hnz
    have hro : ro = some i.bv := by rw [← hrec.1, ← hi', Notif.optRef_ne hi0]
    subst hro
    have hiR : i ∈ R := by rw [hi']; exact hrec.2 (by simp)
    obtain ⟨xr, hkr, hback⟩ := hC.ok.2.2.1 _ i.bv d hst
    have hit : i.bv ≠ t.bv := by intro h; rw [h, hk] at hkr; cases hkr
    have hie : i.bv ≠ ev.bv := by intro h; rw [h, hkz] at hkr; cases hkr
    have hkr2 : σ2.kheap i.bv = some (.reply xr) := by simp [hσ2, hσ1, updK, hit, hie, hkr]
    -- the reply unlink's footprint
    have hfoot3 : ipc.reply_unlink st s2 i t ⦃ s3 => WritesIn st s2 s3 (fun b => b.val = i.val ∨
        SFoot st T c (L.wr s2 (Endp.rTcbA i) 0#u64) b) ⦄ := by
      obtain ⟨-, -, hS1', hA1'⟩ := reply_write_rel (hH.epHyps hP0) hP s2 σ2 hR2 hS2.1 hiR hkr2 0#u64
      unfold ipc.reply_unlink
      step as ⟨s3', hs3'⟩
      subst hs3'
      refine WP.spec_mono (set_thread_state_sfoot hS1'.1.2.1 ht sched.TS_INACTIVE) fun s5 hw5 => ?_
      have hw4 : WritesIn st s2 (L.wr s2 (Endp.rTcbA i) 0#u64) (fun b => b.val = i.val) :=
        ⟨L.ksb_wr _ _ _, L.cpu_wr _ _ _, fun b hb hn => hA1' b hb hn⟩
      exact hw4.trans hw5
    refine WP.spec_bind (WP.spec_and (reply_unlink_c hH hP0 hP s2 σ2 hR2 hS2 ht hk2 hst1 hiR hkr2 hback hq2)
      hfoot3) ?_
    rintro s3 ⟨⟨e3, hR3, hS3⟩, hW3⟩
    have hks3 : L.ksb s3 = L.ksb s := hW3.1.trans hks2
    set x3 : Fl4Spec.Tcb := { x1 with tcbState := .inactive } with hx3
    set σ3 := stsAct (updK (updK σ2 i.bv (.reply { xr with replyTcb := none })) t.bv (.tcb x3)) t.bv with hσ3
    have hk3 : σ3.kheap t.bv = some (.tcb x3) := by simp [hσ3, stsAct_kheap, updK]
    have hq3 : ∀ e ∈ E, ∀ z', σ3.kheap e.bv = some (.endpoint z') → t.bv ∉ z'.epQueue := by
      intro e he z' hz'
      have h1 : e.bv ≠ t.bv := by intro h; rw [h, hk3] at hz'; cases hz'
      have h2 : e.bv ≠ i.bv := by
        intro h; rw [h] at hz'; simp [hσ3, stsAct_kheap, updK, hit] at hz'
      refine hq2 e he z' ?_
      simpa [hσ3, stsAct_kheap, updK, h1, h2] using hz'
    refine WP.spec_bind (WP.spec_and (set_thread_state_c hH hP0 hP s3 σ3 hR3 hS3 ht hk3 hq3
      (by simp [hx3, tsCode]) .inactive (by simp [tsCode]) sched.TS_INACTIVE (by unfold sched.TS_INACTIVE; rfl))
      (set_thread_state_sfoot (IpcRel.ofSRN hR3 hS3).2.2.1 ht sched.TS_INACTIVE)) ?_
    rintro s4 ⟨⟨hR4, hS4⟩, hW4⟩
    simp only [WP.spec_ok]
    have hK3 : SKeep σ2 σ3 := ((SKeep.updK (fun _ h => by cases h) (fun _ _ h => by cases h)).trans
      (SKeep.updK (o := .tcb x3) (fun y h => ⟨x1, by simp [updK, Ne.symm hit, hk2], by cases h; rfl⟩)
        (fun _ _ h => by cases h))).trans (SKeep.stsAct _ _)
    refine ⟨trivial, _, { x3 with tcbState := .inactive }, hspec0 _ ?_, IpcRel.ofSRN hR4 hS4,
      by simp [stsAct_kheap, updK], rfl, ?_, ?_⟩
    · unfold Fl4Spec.blockedCancelIpc Fl4Spec.getBlockingObject
      rw [nd_bind_one (show Fl4Spec.NonDet.assertOpt (σ := Fl4Spec.State Unit)
        (Fl4Spec.epBlocked (.blockedOnReceive ev.bv (some i.bv) d)) σ1 = ({(ev.bv, σ1)}, False) from rfl),
        nd_bind_one hdq]
      dsimp only
      rw [nd_bind_one e3, Notif.setThreadState_eq _ hk3]
    · refine Ipc.RelIfBound.of_keep hC.rib ((hK2.trans hK3).trans ?_)
      exact (SKeep.updK (o := .tcb { x3 with tcbState := .inactive }) (fun y h => ⟨x3, hk3, by cases h; rfl⟩)
        (fun _ _ h => by cases h)).trans (SKeep.stsAct _ _)
    · refine fin _ _ ((hW02.trans hW3).trans hW4) fun b hb => ?_
      rcases hb with (hb | hb | hb) | hb
      · exact hb
      · exact Or.inr (Or.inr ⟨i, hiR, hb⟩)
      · exact cS _ ((L.ksb_wr _ _ _).trans hks2) b hb
      · exact cS _ hks3 b hb
  · -- no reply object
    rename_i hz0
    have hi0 : i = 0#u64 := by apply UScalar.eq_of_val_eq; simpa using hz0
    have hro : ro = none := by rw [← hrec.1, ← hi', hi0, optRef_zero]
    subst hro
    simp only [bind_ok]
    refine WP.spec_bind (WP.spec_and (set_thread_state_c hH hP0 hP s2 σ2 hR2 hS2 ht hk2 hq2
      (by simp [hst1, tsCode]) .inactive (by simp [tsCode]) sched.TS_INACTIVE (by unfold sched.TS_INACTIVE; rfl))
      (set_thread_state_sfoot (IpcRel.ofSRN hR2 hS2).2.2.1 ht sched.TS_INACTIVE)) ?_
    rintro s4 ⟨⟨hR4, hS4⟩, hW4⟩
    simp only [WP.spec_ok]
    refine ⟨trivial, _, { x1 with tcbState := .inactive }, hspec0 _ ?_, IpcRel.ofSRN hR4 hS4,
      by simp [stsAct_kheap, updK], rfl, ?_, ?_⟩
    · unfold Fl4Spec.blockedCancelIpc Fl4Spec.getBlockingObject
      rw [nd_bind_one (show Fl4Spec.NonDet.assertOpt (σ := Fl4Spec.State Unit)
        (Fl4Spec.epBlocked (.blockedOnReceive ev.bv none d)) σ1 = ({(ev.bv, σ1)}, False) from rfl),
        nd_bind_one hdq]
      dsimp only
      rw [Notif.setThreadState_eq _ hk2]
    · refine Ipc.RelIfBound.of_keep hC.rib (hK2.trans ?_)
      exact (SKeep.updK (o := .tcb { x1 with tcbState := .inactive }) (fun y h => ⟨x1, hk2, by cases h; rfl⟩)
        (fun _ _ h => by cases h)).trans (SKeep.stsAct _ _)
    · refine fin _ _ (hW02.trans hW4) fun b hb => ?_
      rcases hb with hb | hb
      · exact hb
      · exact cS _ hks2 b hb

set_option maxHeartbeats 400000 in
/-- **The idle notification `n` bound to `t` blocked receiving, signalled on
`IRel`** (module docstring): `t`'s receive cancelled, then woken without SC
donation. -/
theorem send_signal_bound_irel (hP0 : IPlaced N T E R B) (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hX : IRel st th cr N T C E R B c s σ) {n : U64} (hn : n ∈ N)
    {x : Fl4Spec.Notification} (hk : σ.kheap n.bv = some (.notification x)) (hidle : x.ntfnObj = .idleNtfn)
    {t : U64} {tcb : Fl4Spec.Tcb} (hb : x.ntfnBoundTcb = some t.bv) (hkt : σ.kheap t.bv = some (.tcb tcb))
    (hrb : Fl4Spec.receiveBlocked tcb.tcbState = true) (badge : U64)
    (hCR : ∀ t' : U64, t' = t → CancelRecvHyp E (L.mem s) σ t' tcb)
    (hA3 : ∀ σ1 x1, Fl4Spec.cancelIpc (Z := Unit) t.bv σ = ({((), σ1)}, False) →
      σ1.kheap t.bv = some (.tcb x1) → x1.tcbState = .inactive → RelIfBound σ1 t.bv →
      ActReady (wakeSt3 σ1 t.bv x1 badge.bv) ∧ NoDon C σ1 t.bv n.bv) :
    notification.send_signal st ar s a n badge ⦃ r => r.2 = a ∧ ∃ (s1 : S) (σ1 σ' : Fl4Spec.State Unit) (x1 : Fl4Spec.Tcb),
      Fl4Spec.cancelIpc (Z := Unit) t.bv σ = ({((), σ1)}, False) ∧ σ1.kheap t.bv = some (.tcb x1) ∧
      x1.tcbState = .inactive ∧ RelIfBound σ1 t.bv ∧ IRel st th cr N T C E R B c s1 σ1 ∧
      IFrame (L := L) th s s1 ∧ WritesIn st s s1 (CnW (st := st) T N C E R c s σ) ∧
      Fl4Spec.maybeDonateSc (Z := Unit) t.bv n.bv (wakeSt3 σ1 t.bv x1 badge.bv) =
        ({((), wakeSt3 σ1 t.bv x1 badge.bv)}, False) ∧
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
  obtain ⟨hA, hND⟩ := hA3 σ1 x1 hc hk1 hin hrib
  have hF1 : IFrame (L := L) th s s1 := IRel.iframe_of hX hW1 fun b hb => CnW.oobj hX.2.2.1 hb
  refine WP.spec_mono (wake_irel hP0 s1 _ σ1 hX1 hiT hn hk1 htn hq1 hqE badge hA hND) ?_
  rintro r ⟨hra, hdon, σ', hsw', hX', hSS', hTW'⟩
  exact ⟨hra, s1, σ1, σ', x1, hc, hk1, hin, hrib, hX1, hF1, hW1, hdon, by rw [hspec]; exact hsw',
    by rw [hsw']; exact Set.mem_singleton _, hX', hSS', hTW'⟩

end

end

end Fl4Proofs.P3.Ipc
