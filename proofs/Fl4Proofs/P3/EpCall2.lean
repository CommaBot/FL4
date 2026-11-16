/-
P3 (DESIGN.md §9), endpoints: the remaining call branches.

* `send_ipc_call_inactive`: a call to a waiting receiver that has no reply
  object, or without a grant right: the caller becomes `Inactive` (l4v
  `send_ipc`, `set_thread_state thread Inactive`).
-/
import Fl4Proofs.P3.EpCall
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Endp
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section Spec
open Fl4Spec

/-- The spec's `send_ipc` (call) to a waiting receiver when the caller gets
no reply: it becomes `Inactive`. -/
theorem sendIpc_callInactive_eq {σ : State Unit} {t e d : ObjRef} {q : List ObjRef}
    (hk : σ.kheap e = some (.endpoint (.recvEP (d :: q)))) {xd : Tcb} (hkd : σ.kheap d = some (.tcb xd))
    (hde : d ≠ e) (htd : t ≠ d) {e' : ObjRef} {rep : Option ObjRef} {dd : ReceiverPayload}
    (hst : xd.tcbState = .blockedOnReceive e' rep dd) (blk : Bool) (badge : Badge) (g gr : Bool)
    (hcond : ¬ ((g = true ∨ gr = true) ∧ rep ≠ none)) {σ2 σ3 : State Unit}
    (hT : doIpcTransfer (Z := Unit) t (some e) badge g d (updK σ e (.endpoint (epDeq (.recvEP (d :: q)) d))) =
      ({((), σ2)}, False))
    (hU : NonDet.maybeM (replyUnlinkTcb (Z := Unit) d) rep σ2 = ({((), σ3)}, False))
    {xt3 x3 : Tcb} (hkt3 : σ3.kheap t = some (.tcb xt3)) (hkd3 : σ3.kheap d = some (.tcb x3)) :
    sendIpc (Z := Unit) blk true badge g gr false t e σ =
      specWakeTailE d (stsAct (updK (stsAct (updK σ3 t (.tcb { xt3 with tcbState := .inactive })) t) d
        (.tcb { x3 with tcbState := .running })) d) := by
  have hkd1 : (updK σ e (.endpoint (epDeq (.recvEP (d :: q)) d))).kheap d = some (.tcb xd) := by
    simp [hde, hkd]
  have hkd3' : (stsAct (updK σ3 t (.tcb { xt3 with tcbState := .inactive })) t).kheap d = some (.tcb x3) := by
    rw [stsAct_kheap]; simp [Ne.symm htd, hkd3]
  unfold sendIpc
  rw [nd_bind_one (getEndpoint_eq hk)]
  cases blk <;> dsimp only <;>
  · rw [nd_bind_one (tcbEpDequeue_eq hk (by simp [Endpoint.epQueue])), nd_bind_one (getThreadState_eq hkd1), hst]
    dsimp only
    rw [nd_pure_bind', nd_bind_one hT, nd_bind_one hU, nd_bind_one (getTcbObjRef_eq _ hkd3),
      nd_bind_one (threadGet_eq _ hkt3)]
    simp only [true_or, ↓reduceIte]
    rw [if_neg hcond, nd_bind_one (setThreadState_eq _ hkt3), nd_bind_one (setThreadState_eq _ hkd3')]
    rfl

end Spec

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st] {T E R : Set U64}
  {B : Set (U64 × Fl4Spec.Word)} {SR : S → Fl4Spec.State Unit → Prop}

/-- `send_ipc_call_inactive` over the bundled step lemmas (`EpSteps`). -/
theorem send_ipc_call_inactive_gen {NS : Fl4Spec.ThreadState → Prop} {GC : Prop} (hX : EpSteps st A ar T E R B SR NS GC) (hTl : EpTailHyps st A T E R B SR)
    (hP : EPlaced T E R B) (s : S) (a : A) (σ : Fl4Spec.State Unit) (hR : EpStateRel T E R B (L.mem s) σ)
    (hSR : SR s σ) {t : U64} (ht : t ∈ T) {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt))
    (hnb : tsCode xt.tcbState ≠ 3 ∧ tsCode xt.tcbState ≠ 4) (hft : xt.tcbFault = none) (hns : NS xt.tcbState)
    {e d : U64} (he : e ∈ E) {q : List Fl4Spec.ObjRef} (hk : σ.kheap e.bv = some (.endpoint (.recvEP (d.bv :: q))))
    {xd : Fl4Spec.Tcb} (hkd : σ.kheap d.bv = some (.tcb xd)) (hrb : ipcBufOf true xd = none)
    (badge : U64) (g gr : Bool)
    (hcaps : GC ∨ g = false ∨ ipcBufOf false xt = none ∨
      Fl4Spec.unat (Fl4Spec.dataToMessageInfo (xt.tcbArch.tcbContext.userRegs Fl4Spec.msg_info_register)).miExtraCaps = 0)
    (hback : ∀ e' r dd xr, xd.tcbState = .blockedOnReceive e' (some r) dd → σ.kheap r = some (.reply xr) →
      xr.replyTcb = some d.bv)
    (hno : (g = false ∧ gr = false) ∨ ∀ e' rep dd, xd.tcbState = .blockedOnReceive e' rep dd → rep = none)
    (blk : Bool) :
    endpoint.send_ipc st ar s a blk true badge g gr false t e ⦃ r => r.2 = a ∧
      ¬ (Fl4Spec.sendIpc (Z := Unit) blk true badge.bv g gr false t.bv e.bv σ).2 ∧
      ∃ σ', ((), σ') ∈ (Fl4Spec.sendIpc (Z := Unit) blk true badge.bv g gr false t.bv e.bv σ).1 ∧
        EpStateRel T E R B (L.mem r.1) σ' ∧ SR r.1 σ' ⦄ := by
  have hx := hR.at_ep he hk
  have hxt := hR.at_tcb ht hkt
  obtain ⟨hst2, xs, hxs0, hq, hQ, hB⟩ := hx
  obtain ⟨d', xs', rfl⟩ := List.exists_cons_of_ne_nil hxs0
  simp only [List.map_cons, List.cons.injEq] at hq
  obtain ⟨hd', hq'⟩ := hq
  have hdd : d' = d := eq_of_bv hd'.symm
  subst hdd
  have hdT : d' ∈ T := hQ.mem d' (by simp)
  have hda := hP.tcb d' hdT
  have hxd := hR.at_tcb hdT hkd
  have hd3 : (L.mem s (tStA d')).val = 3 := (hB d' (by simp)).1
  have hdb : L.mem s (tBlockA d') = e := (hB d' (by simp)).2
  -- the receiver's state
  obtain ⟨e', rep, dd, hstd⟩ := tsCode_three (hxd.st.symm.trans hd3)
  have he' : e' = e.bv := by
    have := hxd.blk e' (by rw [hstd]; rfl); rw [hdb] at this; exact this.symm
  subst he'
  obtain ⟨hrep, hrepR⟩ := hxd.recv _ _ _ hstd
  have htd : t ≠ d' := by
    intro h; subst h; exact hnb.1 (hxt.st.symm.trans hd3)
  have hde : d'.bv ≠ e.bv := kheap_ne hkd hk (fun _ h1 h2 => by subst h1; cases h2)
  have hte : t.bv ≠ e.bv := kheap_ne hkt hk (fun _ h1 h2 => by subst h1; cases h2)
  -- FL4
  unfold endpoint.send_ipc
  step as ⟨st0, hst0⟩
  rw [hst0, epState_eq, hst2]
  rw [if_neg (by rw [ep_state_vals.1]; decide), if_neg (by rw [ep_state_vals.2.1]; decide)]
  step as ⟨q0, hq0⟩
  have hhead : q0.head = d' := by rw [hq0, epQ_eq]; exact hQ.head
  rw [hhead]
  -- the dequeue
  refine WP.spec_bind (hX.deq hP s σ hR hSR he hk (d := d') (by simp [Fl4Spec.Endpoint.epQueue])) ?_
  rintro s1 ⟨e1, hR1, hS1, hA1⟩
  set σ1 := updK σ e.bv (.endpoint (epDeq (.recvEP (d'.bv :: q)) d'.bv))
  have hkt1 : σ1.kheap t.bv = some (.tcb xt) := by simp [σ1, hte, hkt]
  have hkd1 : σ1.kheap d'.bv = some (.tcb xd) := by simp [σ1, hde, hkd]
  -- the transfer
  refine WP.spec_bind (hX.xregs hP s1 a σ1 hR1 hS1 ht hdT htd hkt1 hkd1 hft hrb e badge g hcaps) ?_
  rintro s2 ⟨e2, hR2, hS2, hA2⟩
  set σ2 := updK σ1 d'.bv (.tcb (xferTcb xd xt badge.bv))
  have hkd2 : σ2.kheap d'.bv = some (.tcb (xferTcb xd xt badge.bv)) := by simp [σ2]
  have htd' : t.bv ≠ d'.bv := bv_inj htd
  have hkt2 : σ2.kheap t.bv = some (.tcb xt) := by simp [σ2, htd', hkt1]
  have hst2' : (xferTcb xd xt badge.bv).tcbState = .blockedOnReceive e.bv rep dd := by rw [xferTcb_state, hstd]
  -- `d'` is in no endpoint queue from `σ1` on
  have hk1e : σ1.kheap e.bv = some (.endpoint (epDeq (.recvEP (d'.bv :: q)) d'.bv)) := by simp [σ1]
  have hdb1 : L.mem s1 (tBlockA d') = e := by
    rw [hA1 _ (a_blk hda).1 ⟨d', hdT, (a_blk hda).2⟩, hdb]
  have hq1 := dequeued_not_queued hR1 he hdb1 hk1e (epDeq_not_mem _)
  have hq2 : ∀ e'' ∈ E, ∀ z, σ2.kheap e''.bv = some (.endpoint z) → d'.bv ∉ z.epQueue := by
    intro e'' he'' z hz
    have hne : d'.bv ≠ e''.bv := by intro h; rw [← h, hkd2] at hz; cases hz
    exact hq1 e'' he'' z (by simpa [σ2, Ne.symm hne] using hz)
  -- the reply word
  have hrw : L.mem s2 (tReplyA d') = L.mem s (tReplyA d') := by
    rw [hA2 _ (a_reply hda).1 ?_, hA1 _ (a_reply hda).1 ⟨d', hdT, (a_reply hda).2⟩]
    rintro ⟨r', hr'⟩
    rw [val_reply hda, regA_val hda (regIdx_lt r')] at hr'; have := regIdx_lt r'; omega
  step as ⟨i, hi⟩
  rw [hi, hrw]
  simp only [↓reduceIte]
  have hcond : ¬ ((g = true ∨ gr = true) ∧ rep ≠ none) := by
    rintro ⟨h1, h2⟩
    rcases hno with ⟨rfl, rfl⟩ | h
    · simp at h1
    · exact h2 (h _ _ _ hstd)
  refine WP.spec_bind (Pₘ := fun s3 => ∃ σ3 x3, EpStateRel T E R B (L.mem s3) σ3 ∧ SR s3 σ3 ∧
      Fl4Spec.NonDet.maybeM (Fl4Spec.replyUnlinkTcb (Z := Unit) d'.bv) rep σ2 = ({((), σ3)}, False) ∧
      σ3.kheap t.bv = some (.tcb xt) ∧ σ3.kheap d'.bv = some (.tcb x3) ∧ tsCode x3.tcbState ≠ 6 ∧
      (∀ e'' ∈ E, ∀ z, σ3.kheap e''.bv = some (.endpoint z) → d'.bv ∉ z.epQueue)) ?_ ?_
  · cases hrp : rep with
    | none =>
      rw [hrp] at hrep
      have h0 := optRef_none hrep
      simp only [h0, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
      exact ⟨σ2, _, hR2, hS2, rfl, hkt2, hkd2, by rw [hst2']; simp [tsCode], hq2⟩
    | some r =>
      rw [hrp] at hrep hrepR hst2'
      obtain ⟨hw0, hwr⟩ := optRef_some hrep
      have hwR := hrepR (by simp)
      have hne0 : (L.mem s (tReplyA d') != 0#u64) = true := by simp [hw0]
      simp only [hne0, ↓reduceIte]
      set w := L.mem s (tReplyA d') with hwdef
      subst hwr
      obtain ⟨xr, hkr, -⟩ := hR.reply w hwR
      have hwe : w.bv ≠ e.bv := kheap_ne hkr hk (fun _ h1 h2 => by subst h1; cases h2)
      have hwd : w.bv ≠ d'.bv := kheap_ne hkr hkd (fun _ h1 h2 => by subst h1; cases h2)
      have hwt : w.bv ≠ t.bv := kheap_ne hkr hkt (fun _ h1 h2 => by subst h1; cases h2)
      have hkr2 : σ2.kheap w.bv = some (.reply xr) := by simp [σ2, σ1, hwe, hwd, hkr]
      have hb' := hback e.bv w.bv dd xr (by rw [hstd, hrp]) hkr
      refine WP.spec_mono (hX.unlink hP s2 σ2 hR2 hS2 hdT hkd2 hst2' hwR hkr2 hb' hq2) ?_
      rintro s3 ⟨e3, hR3, hS3⟩
      refine ⟨_, { xferTcb xd xt badge.bv with tcbState := .inactive }, hR3, hS3, e3, ?_, ?_, ?_, ?_⟩
      · rw [stsAct_kheap]; simp [htd', hwt.symm, hkt2]
      · rw [stsAct_kheap]; simp
      · simp [tsCode]
      · intro e'' he'' z hz
        rw [stsAct_kheap] at hz
        have hne : d'.bv ≠ e''.bv := by intro h; rw [← h] at hz; simp at hz
        have hne' : w.bv ≠ e''.bv := by intro h; rw [← h] at hz; simp [hwd] at hz
        exact hq2 e'' he'' z (by simpa [Ne.symm hne, Ne.symm hne'] using hz)
  · rintro s3 ⟨σ3, x3, hR3, hS3, hU, hkt3, hkd3, hns3, hq3⟩
    have hqt3 := not_queued hR3 ht hkt3 hnb
    rcases hno with ⟨rfl, rfl⟩ | hnone
    · simp only [Bool.false_eq_true, ↓reduceIte, ite_self]
      refine WP.spec_bind (Pₘ := fun x => x.2 = a ∧
        EpStateRel T E R B (L.mem x.1) (stsAct (updK σ3 t.bv (.tcb { xt with tcbState := .inactive })) t.bv) ∧
        SR x.1 (stsAct (updK σ3 t.bv (.tcb { xt with tcbState := .inactive })) t.bv)) ?_ ?_
      · refine WP.spec_bind (hX.sts hP s3 σ3 hR3 hS3 ht hkt3 hqt3 hns .inactive (by simp [tsCode])
          sched.TS_INACTIVE (by unfold sched.TS_INACTIVE; rfl)) ?_
        rintro s5 ⟨h1, h2⟩
        simp only [WP.spec_ok]
        exact ⟨trivial, h1, h2⟩
      rintro ⟨s4, a4⟩ ⟨ha4, hR4, hS4⟩
      simp only at ha4
      subst ha4
      set σ4 := stsAct (updK σ3 t.bv (.tcb { xt with tcbState := .inactive })) t.bv
      have hkd4 : σ4.kheap d'.bv = some (.tcb x3) := by rw [stsAct_kheap]; simp [Ne.symm htd', hkd3]
      have hq4 : ∀ e'' ∈ E, ∀ z, σ4.kheap e''.bv = some (.endpoint z) → d'.bv ∉ z.epQueue := by
        intro e'' he'' z hz
        have hne : e''.bv ≠ t.bv := by intro h; rw [h] at hz; rw [stsAct_kheap] at hz; simp at hz
        refine hq3 e'' he'' z ?_
        rw [← hz, stsAct_kheap, updK_kheap, Function.update_of_ne hne]
      refine WP.spec_bind (hX.sts hP s4 σ4 hR4 hS4 hdT hkd4 hq4 (hX.ns_ep _ hns3) .running (by simp [tsCode])
        sched.TS_RUNNING (by unfold sched.TS_RUNNING; rfl)) ?_
      rintro s5 ⟨hR5, hS5⟩
      have hspec := sendIpc_callInactive_eq hk hkd hde htd' hstd blk badge.bv _ _ hcond e2 hU hkt3 hkd3 (t := t.bv)
      rw [hspec]
      refine WP.spec_mono (hTl.wakeTail s5 _ _ d' hR5 hS5 hdT) ?_
      rintro ⟨s7, a7⟩ ⟨ha7, hnf, σ', hm, hf, hv, hS'⟩
      exact ⟨ha7, hnf, σ', hm, hR5.frame hP hf hv, hS'⟩

    · have h0 : L.mem s (tReplyA d') = 0#u64 := optRef_none (by rw [hrep]; exact hnone _ _ _ hstd)
      simp only [h0, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      refine WP.spec_bind (Pₘ := fun x => x.2 = a ∧
        EpStateRel T E R B (L.mem x.1) (stsAct (updK σ3 t.bv (.tcb { xt with tcbState := .inactive })) t.bv) ∧
        SR x.1 (stsAct (updK σ3 t.bv (.tcb { xt with tcbState := .inactive })) t.bv)) ?_ ?_
      · refine WP.spec_bind (hX.sts hP s3 σ3 hR3 hS3 ht hkt3 hqt3 hns .inactive (by simp [tsCode])
          sched.TS_INACTIVE (by unfold sched.TS_INACTIVE; rfl)) ?_
        rintro s5 ⟨h1, h2⟩
        simp only [WP.spec_ok]
        exact ⟨trivial, h1, h2⟩
      rintro ⟨s4, a4⟩ ⟨ha4, hR4, hS4⟩
      simp only at ha4
      subst ha4
      set σ4 := stsAct (updK σ3 t.bv (.tcb { xt with tcbState := .inactive })) t.bv
      have hkd4 : σ4.kheap d'.bv = some (.tcb x3) := by rw [stsAct_kheap]; simp [Ne.symm htd', hkd3]
      have hq4 : ∀ e'' ∈ E, ∀ z, σ4.kheap e''.bv = some (.endpoint z) → d'.bv ∉ z.epQueue := by
        intro e'' he'' z hz
        have hne : e''.bv ≠ t.bv := by intro h; rw [h] at hz; rw [stsAct_kheap] at hz; simp at hz
        refine hq3 e'' he'' z ?_
        rw [← hz, stsAct_kheap, updK_kheap, Function.update_of_ne hne]
      refine WP.spec_bind (hX.sts hP s4 σ4 hR4 hS4 hdT hkd4 hq4 (hX.ns_ep _ hns3) .running (by simp [tsCode])
        sched.TS_RUNNING (by unfold sched.TS_RUNNING; rfl)) ?_
      rintro s5 ⟨hR5, hS5⟩
      have hspec := sendIpc_callInactive_eq hk hkd hde htd' hstd blk badge.bv _ _ hcond e2 hU hkt3 hkd3 (t := t.bv)
      rw [hspec]
      refine WP.spec_mono (hTl.wakeTail s5 _ _ d' hR5 hS5 hdT) ?_
      rintro ⟨s7, a7⟩ ⟨ha7, hnf, σ', hm, hf, hv, hS'⟩
      exact ⟨ha7, hnf, σ', hm, hR5.frame hP hf hv, hS'⟩

/-- **Call to a waiting receiver without a reply object or without a grant
right**: as `send_ipc_call`, but the caller becomes `Inactive`. -/
theorem send_ipc_call_inactive (hH : EpHyps st T E R B SR) (hBf : EpBufHyps st T E R B SR) (hTl : EpTailHyps st A T E R B SR)
    (hP : EPlaced T E R B) (s : S) (a : A) (σ : Fl4Spec.State Unit) (hR : EpStateRel T E R B (L.mem s) σ)
    (hSR : SR s σ) {t : U64} (ht : t ∈ T) {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt))
    (hnb : tsCode xt.tcbState ≠ 3 ∧ tsCode xt.tcbState ≠ 4) (hft : xt.tcbFault = none)
    {e d : U64} (he : e ∈ E) {q : List Fl4Spec.ObjRef} (hk : σ.kheap e.bv = some (.endpoint (.recvEP (d.bv :: q))))
    {xd : Fl4Spec.Tcb} (hkd : σ.kheap d.bv = some (.tcb xd)) (hrb : ipcBufOf true xd = none)
    (badge : U64) (g gr : Bool)
    (hcaps : g = false ∨ ipcBufOf false xt = none ∨
      Fl4Spec.unat (Fl4Spec.dataToMessageInfo (xt.tcbArch.tcbContext.userRegs Fl4Spec.msg_info_register)).miExtraCaps = 0)
    (hback : ∀ e' r dd xr, xd.tcbState = .blockedOnReceive e' (some r) dd → σ.kheap r = some (.reply xr) →
      xr.replyTcb = some d.bv)
    (hno : (g = false ∧ gr = false) ∨ ∀ e' rep dd, xd.tcbState = .blockedOnReceive e' rep dd → rep = none)
    (blk : Bool) :
    endpoint.send_ipc st ar s a blk true badge g gr false t e ⦃ r => r.2 = a ∧
      ¬ (Fl4Spec.sendIpc (Z := Unit) blk true badge.bv g gr false t.bv e.bv σ).2 ∧
      ∃ σ', ((), σ') ∈ (Fl4Spec.sendIpc (Z := Unit) blk true badge.bv g gr false t.bv e.bv σ).1 ∧
        EpStateRel T E R B (L.mem r.1) σ' ∧ SR r.1 σ' ⦄ :=
  send_ipc_call_inactive_gen (EpHyps.steps (ar := ar) hH hBf (fun _ => True) (fun _ _ => trivial)) hTl hP s a σ hR hSR ht hkt hnb hft trivial he hk hkd hrb badge g gr (Or.inr hcaps) hback hno blk

end

end

end Fl4Proofs.P3.Endp
