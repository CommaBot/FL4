/-
P3 (DESIGN.md §9), endpoints: the transfer theorems over the bundled step
lemmas (`EpSteps`): each `X_gen` is the proof of `X` (EpSend, EpCall,
EpCall2, EpCall3, EpRecvSend, EpSendBuf, EpRecvBuf) with its steps taken from
`hX`; instantiated with `CombHyps.steps` they give the combined theorems
(`EpCombIpc`).
-/
import Fl4Proofs.P3.EpStepsN
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Endp
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st] {T E R : Set U64}
  {B : Set (U64 × Fl4Spec.Word)} {SR : S → Fl4Spec.State Unit → Prop} {NS : Fl4Spec.ThreadState → Prop}

theorem send_ipc_recv_gen (hX : EpSteps st A ar T E R B SR NS) (hTl : EpTailHyps st A T E R B SR)
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
    (blk : Bool) :
    endpoint.send_ipc st ar s a blk false badge g gr false t e ⦃ r => r.2 = a ∧
      ¬ (Fl4Spec.sendIpc (Z := Unit) blk false badge.bv g gr false t.bv e.bv σ).2 ∧
      ∃ σ', ((), σ') ∈ (Fl4Spec.sendIpc (Z := Unit) blk false badge.bv g gr false t.bv e.bv σ).1 ∧
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
  simp only [Bool.false_eq_true, ↓reduceIte]
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
    have hxt3 := hR3.at_tcb ht hkt3
    step as ⟨i1, hi1⟩
    have hf0 : i1 = fl4_abi.consts.fault.NullFault := by
      rw [hi1, hxt3.fault0.2 hft]; unfold fl4_abi.consts.fault.NullFault; rfl
    simp only [hf0, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    apply ok_bind_spec
    refine WP.spec_bind (hX.sts hP s3 σ3 hR3 hS3 hdT hkd3 hq3 (hX.ns_ep _ hns3) .running (by simp [tsCode])
      sched.TS_RUNNING (by unfold sched.TS_RUNNING; rfl)) ?_
    rintro s5 ⟨hR5, hS5⟩
    have hspec := sendIpc_recv_eq hk hkd hde hstd blk badge.bv g gr e2 hU hkt3 hft hkd3 (t := t.bv)
    rw [hspec]
    refine WP.spec_mono (hTl.wakeTail s5 a _ d' hR5 hS5 hdT) ?_
    rintro ⟨s7, a7⟩ ⟨ha7, hnf, σ', hm, hf, hv, hS'⟩
    exact ⟨ha7, hnf, σ', hm, hR5.frame hP hf hv, hS'⟩

theorem send_ipc_call_gen (hX : EpSteps st A ar T E R B SR NS) (hTl : EpTailHyps st A T E R B SR)
    (hP : EPlaced T E R B) (s : S) (a : A) (σ : Fl4Spec.State Unit) (hR : EpStateRel T E R B (L.mem s) σ)
    (hSR : SR s σ) {t : U64} (ht : t ∈ T) {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt))
    (hnb : tsCode xt.tcbState ≠ 3 ∧ tsCode xt.tcbState ≠ 4) (hft : xt.tcbFault = none) (hns : NS xt.tcbState)
    {e d : U64} (he : e ∈ E) {q : List Fl4Spec.ObjRef} (hk : σ.kheap e.bv = some (.endpoint (.recvEP (d.bv :: q))))
    {xd : Fl4Spec.Tcb} (hkd : σ.kheap d.bv = some (.tcb xd)) (hrb : ipcBufOf true xd = none)
    (badge : U64) (g gr : Bool)
    (hcaps : g = false ∨ ipcBufOf false xt = none ∨
      Fl4Spec.unat (Fl4Spec.dataToMessageInfo (xt.tcbArch.tcbContext.userRegs Fl4Spec.msg_info_register)).miExtraCaps = 0)
    (hback : ∀ e' r dd xr, xd.tcbState = .blockedOnReceive e' (some r) dd → σ.kheap r = some (.reply xr) →
      xr.replyTcb = some d.bv)
    (hg : g = true ∨ gr = true)
    (hrp0 : ∀ e' rep dd, xd.tcbState = .blockedOnReceive e' rep dd → rep ≠ none)
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
  have hg' := hg
  cases hrp : rep with
  | none => exact absurd hrp (hrp0 _ _ _ hstd)
  | some r =>
  rw [hrp] at hrep hrepR hst2' hstd
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
  have hb' := hback e.bv w.bv dd xr hstd hkr
  refine WP.spec_bind (hX.unlink hP s2 σ2 hR2 hS2 hdT hkd2 hst2' hwR hkr2 hb' hq2) ?_
  rintro s3 ⟨e3, hR3, hS3⟩
  set x3 : Fl4Spec.Tcb := { xferTcb xd xt badge.bv with tcbState := .inactive }
  set σ3 := stsAct (updK (updK σ2 w.bv (.reply { xr with replyTcb := none })) d'.bv (.tcb x3)) d'.bv
  have hkt3 : σ3.kheap t.bv = some (.tcb xt) := by rw [stsAct_kheap]; simp [htd', hwt.symm, hkt2]
  have hkd3 : σ3.kheap d'.bv = some (.tcb x3) := by rw [stsAct_kheap]; simp
  have hkr3 : σ3.kheap w.bv = some (.reply { xr with replyTcb := none }) := by
    rw [stsAct_kheap]; simp [hwd]
  have hq3 : ∀ e'' ∈ E, ∀ z, σ3.kheap e''.bv = some (.endpoint z) → d'.bv ∉ z.epQueue := by
    intro e'' he'' z hz
    rw [stsAct_kheap] at hz
    have hne : d'.bv ≠ e''.bv := by intro h; rw [← h] at hz; simp at hz
    have hne' : w.bv ≠ e''.bv := by intro h; rw [← h] at hz; simp [hwd] at hz
    exact hq2 e'' he'' z (by simpa [Ne.symm hne, Ne.symm hne'] using hz)
  have hqt3 := not_queued hR3 ht hkt3 hnb
  have hpush := hX.push hP s3 a σ3 hR3 hS3 ht hkt3 hkd3 hqt3 hns hwR hkr3
  rcases hg with hg | hg
  · subst hg
    simp only [↓reduceIte]
    refine WP.spec_bind hpush ?_
    rintro ⟨s4, a4⟩ ⟨ha4, hP4, hR4, hS4⟩
    simp only at ha4
    subst ha4
    set σ4 := stsAct (updK (updK σ3 w.bv (.reply { ({ xr with replyTcb := none } : Fl4Spec.Reply) with
      replyTcb := some t.bv })) t.bv
      (.tcb { xt with tcbState := .blockedOnReply w.bv })) t.bv
    have h43 : ∀ p, p ≠ t.bv → p ≠ w.bv → σ4.kheap p = σ3.kheap p := by
      intro p h1 h2
      rw [stsAct_kheap, updK_kheap, Function.update_of_ne h1, updK_kheap, Function.update_of_ne h2]
    have hkd4 : σ4.kheap d'.bv = some (.tcb x3) := (h43 _ htd'.symm hwd.symm).trans hkd3
    have hq4 : ∀ e'' ∈ E, ∀ z, σ4.kheap e''.bv = some (.endpoint z) → d'.bv ∉ z.epQueue := by
      intro e'' he'' z hz
      have hne : e''.bv ≠ t.bv := by intro h; rw [h] at hz; rw [stsAct_kheap] at hz; simp at hz
      have hne' : e''.bv ≠ w.bv := by
        intro h; rw [h, stsAct_kheap] at hz; simp [hwt] at hz
      exact hq3 e'' he'' z ((h43 _ hne hne').symm.trans hz)
    refine WP.spec_bind (hX.sts hP s4 σ4 hR4 hS4 hdT hkd4 hq4 (hX.ns_ep _ (by simp [x3, tsCode])) .running (by simp [tsCode])
      sched.TS_RUNNING (by unfold sched.TS_RUNNING; rfl)) ?_
    rintro s5 ⟨hR5, hS5⟩
    have hspec := sendIpc_call_eq hk hkd hde (by rw [hstd]) blk badge.bv _ _ hg' e2 e3 hkt3 hkd3 hP4 hkd4
      (t := t.bv)
    rw [hspec]
    refine WP.spec_mono (hTl.wakeTail s5 _ _ d' hR5 hS5 hdT) ?_
    rintro ⟨s7, a7⟩ ⟨ha7, hnf, σ', hm, hf, hv, hS'⟩
    exact ⟨ha7, hnf, σ', hm, hR5.frame hP hf hv, hS'⟩
  · cases g with
    | true =>
      simp only [↓reduceIte]
      refine WP.spec_bind hpush ?_
      rintro ⟨s4, a4⟩ ⟨ha4, hP4, hR4, hS4⟩
      simp only at ha4
      subst ha4
      set σ4 := stsAct (updK (updK σ3 w.bv (.reply { ({ xr with replyTcb := none } : Fl4Spec.Reply) with
      replyTcb := some t.bv })) t.bv
        (.tcb { xt with tcbState := .blockedOnReply w.bv })) t.bv
      have h43 : ∀ p, p ≠ t.bv → p ≠ w.bv → σ4.kheap p = σ3.kheap p := by
        intro p h1 h2
        rw [stsAct_kheap, updK_kheap, Function.update_of_ne h1, updK_kheap, Function.update_of_ne h2]
      have hkd4 : σ4.kheap d'.bv = some (.tcb x3) := (h43 _ htd'.symm hwd.symm).trans hkd3
      have hq4 : ∀ e'' ∈ E, ∀ z, σ4.kheap e''.bv = some (.endpoint z) → d'.bv ∉ z.epQueue := by
        intro e'' he'' z hz
        have hne : e''.bv ≠ t.bv := by intro h; rw [h] at hz; rw [stsAct_kheap] at hz; simp at hz
        have hne' : e''.bv ≠ w.bv := by
          intro h; rw [h, stsAct_kheap] at hz; simp [hwt] at hz
        exact hq3 e'' he'' z ((h43 _ hne hne').symm.trans hz)
      refine WP.spec_bind (hX.sts hP s4 σ4 hR4 hS4 hdT hkd4 hq4 (hX.ns_ep _ (by simp [x3, tsCode])) .running (by simp [tsCode])
        sched.TS_RUNNING (by unfold sched.TS_RUNNING; rfl)) ?_
      rintro s5 ⟨hR5, hS5⟩
      have hspec := sendIpc_call_eq hk hkd hde (by rw [hstd]) blk badge.bv _ _ hg' e2 e3 hkt3 hkd3 hP4 hkd4
        (t := t.bv)
      rw [hspec]
      refine WP.spec_mono (hTl.wakeTail s5 _ _ d' hR5 hS5 hdT) ?_
      rintro ⟨s7, a7⟩ ⟨ha7, hnf, σ', hm, hf, hv, hS'⟩
      exact ⟨ha7, hnf, σ', hm, hR5.frame hP hf hv, hS'⟩

    | false =>
      subst hg
      simp only [Bool.false_eq_true, ↓reduceIte]
      refine WP.spec_bind hpush ?_
      rintro ⟨s4, a4⟩ ⟨ha4, hP4, hR4, hS4⟩
      simp only at ha4
      subst ha4
      set σ4 := stsAct (updK (updK σ3 w.bv (.reply { ({ xr with replyTcb := none } : Fl4Spec.Reply) with
      replyTcb := some t.bv })) t.bv
        (.tcb { xt with tcbState := .blockedOnReply w.bv })) t.bv
      have h43 : ∀ p, p ≠ t.bv → p ≠ w.bv → σ4.kheap p = σ3.kheap p := by
        intro p h1 h2
        rw [stsAct_kheap, updK_kheap, Function.update_of_ne h1, updK_kheap, Function.update_of_ne h2]
      have hkd4 : σ4.kheap d'.bv = some (.tcb x3) := (h43 _ htd'.symm hwd.symm).trans hkd3
      have hq4 : ∀ e'' ∈ E, ∀ z, σ4.kheap e''.bv = some (.endpoint z) → d'.bv ∉ z.epQueue := by
        intro e'' he'' z hz
        have hne : e''.bv ≠ t.bv := by intro h; rw [h] at hz; rw [stsAct_kheap] at hz; simp at hz
        have hne' : e''.bv ≠ w.bv := by
          intro h; rw [h, stsAct_kheap] at hz; simp [hwt] at hz
        exact hq3 e'' he'' z ((h43 _ hne hne').symm.trans hz)
      refine WP.spec_bind (hX.sts hP s4 σ4 hR4 hS4 hdT hkd4 hq4 (hX.ns_ep _ (by simp [x3, tsCode])) .running (by simp [tsCode])
        sched.TS_RUNNING (by unfold sched.TS_RUNNING; rfl)) ?_
      rintro s5 ⟨hR5, hS5⟩
      have hspec := sendIpc_call_eq hk hkd hde (by rw [hstd]) blk badge.bv _ _ hg' e2 e3 hkt3 hkd3 hP4 hkd4
        (t := t.bv)
      rw [hspec]
      refine WP.spec_mono (hTl.wakeTail s5 _ _ d' hR5 hS5 hdT) ?_
      rintro ⟨s7, a7⟩ ⟨ha7, hnf, σ', hm, hf, hv, hS'⟩
      exact ⟨ha7, hnf, σ', hm, hR5.frame hP hf hv, hS'⟩

theorem send_ipc_call_inactive_gen (hX : EpSteps st A ar T E R B SR NS) (hTl : EpTailHyps st A T E R B SR)
    (hP : EPlaced T E R B) (s : S) (a : A) (σ : Fl4Spec.State Unit) (hR : EpStateRel T E R B (L.mem s) σ)
    (hSR : SR s σ) {t : U64} (ht : t ∈ T) {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt))
    (hnb : tsCode xt.tcbState ≠ 3 ∧ tsCode xt.tcbState ≠ 4) (hft : xt.tcbFault = none) (hns : NS xt.tcbState)
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


theorem receive_ipc_sendCallPush_gen (hX : EpSteps st A ar T E R B SR NS)
    (hTl : EpTailHyps st A T E R B SR) (hSc : EpScHyps st T E R B SR) (hP : EPlaced T E R B) (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hR : EpStateRel T E R B (L.mem s) σ) (hSR : SR s σ)
    {t : U64} (ht : t ∈ T) {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt))
    (hnb : tsCode xt.tcbState ≠ 3 ∧ tsCode xt.tcbState ≠ 4) (hbn : xt.tcbBoundNotification = none)
    (hrb : ipcBufOf true xt = none)
    {e sd : U64} (he : e ∈ E) {q : List Fl4Spec.ObjRef} (hk : σ.kheap e.bv = some (.endpoint (.sendEP (sd.bv :: q))))
    {xs : Fl4Spec.Tcb} (hks : σ.kheap sd.bv = some (.tcb xs)) (hfs : xs.tcbFault = none)
    (hcall : ∀ e' dd, xs.tcbState = .blockedOnSend e' dd → dd.senderIsCall = true)
    (hg : ∀ e' dd, xs.tcbState = .blockedOnSend e' dd → dd.senderCanGrant = true ∨ dd.senderCanGrantReply = true)
    (hscn : xs.tcbSchedContext = none)
    (hcaps : ∀ e' dd, xs.tcbState = .blockedOnSend e' dd → dd.senderCanGrant = false ∨ ipcBufOf false xs = none ∨
      Fl4Spec.unat (Fl4Spec.dataToMessageInfo (xs.tcbArch.tcbContext.userRegs Fl4Spec.msg_info_register)).miExtraCaps = 0)
    (cb : U64) (c1 c2 c3 c4 : Bool) {rv : U64} (b' : Bool) (r' : Fl4Spec.CapRights) (hrvR : rv ∈ R) (hrv0 : L.mem s (rTcbA rv) = 0#u64) (b : Fl4Spec.Badge) (rights : Fl4Spec.CapRights) (blk : Bool) :
    endpoint.receive_ipc st ar s a t (.Endpoint e cb c1 c2 c3 c4) blk (.Reply rv b') ⦃ r => r.2 = a ∧
      ¬ (Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) blk (.replyCap rv.bv r') σ).2 ∧
      ∃ σ', ((), σ') ∈ (Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) blk (.replyCap rv.bv r') σ).1 ∧
        EpStateRel T E R B (L.mem r.1) σ' ∧ SR r.1 σ' ⦄ := by
  have hx := hR.at_ep he hk
  have hxt := hR.at_tcb ht hkt
  have hta := hP.tcb t ht
  have hbound : L.mem s (tBoundA t) = 0#u64 := optRef_none (hxt.bound.symm.trans hbn)
  have hrc : ReplyArg R (L.mem s) (.Reply rv b') (.replyCap rv.bv r') rv := Or.inr ⟨b', r', rfl, rfl, hrvR, hrv0⟩
  obtain ⟨hst1, xs0, hxs0, hq, hQ, hB⟩ := hx
  obtain ⟨sd', xs', rfl⟩ := List.exists_cons_of_ne_nil hxs0
  simp only [List.map_cons, List.cons.injEq] at hq
  obtain ⟨hd', hq'⟩ := hq
  have hdd : sd' = sd := eq_of_bv hd'.symm
  subst hdd
  have hsT : sd' ∈ T := hQ.mem sd' (by simp)
  have hsa := hP.tcb sd' hsT
  have hxs := hR.at_tcb hsT hks
  have hs4 : (L.mem s (tStA sd')).val = 4 := (hB sd' (by simp)).1
  have hsb : L.mem s (tBlockA sd') = e := (hB sd' (by simp)).2
  obtain ⟨e', dd, hstd⟩ := tsCode_four (hxs.st.symm.trans hs4)
  have he' : e' = e.bv := by
    have := hxs.blk e' (by rw [hstd]; rfl); rw [hsb] at this; exact this.symm
  subst he'
  obtain ⟨hbadge, hflags⟩ := hxs.send _ _ hstd
  have hts : t ≠ sd' := by
    intro h; subst h; exact hnb.2 (hxt.st.symm.trans hs4)
  have hse : sd'.bv ≠ e.bv := kheap_ne hks hk (fun _ h1 h2 => by subst h1; cases h2)
  have hte : t.bv ≠ e.bv := kheap_ne hkt hk (fun _ h1 h2 => by subst h1; cases h2)
  apply receive_ipc_pre s a t e cb c1 c2 c3 c4 blk _ _ rv hrc hbound
  step as ⟨st0, hst0⟩
  rw [hst0, epState_eq, hst1]
  rw [if_neg (by rw [ep_state_vals.1]; decide), if_neg (by rw [ep_state_vals.2.2]; decide)]
  unfold endpoint.receive_from_sender
  step as ⟨q0, hq0⟩
  have hhead : q0.head = sd' := by rw [hq0, epQ_eq]; exact hQ.head
  rw [hhead]
  refine WP.spec_bind (hX.deq hP s σ hR hSR he hk (d := sd') (by simp [Fl4Spec.Endpoint.epQueue])) ?_
  rintro s1 ⟨e1, hR1, hS1, hA1⟩
  set σ1 := updK σ e.bv (.endpoint (epDeq (.sendEP (sd'.bv :: q)) sd'.bv))
  have hkt1 : σ1.kheap t.bv = some (.tcb xt) := by simp [σ1, hte, hkt]
  have hks1 : σ1.kheap sd'.bv = some (.tcb xs) := by simp [σ1, hse, hks]
  have hbw : L.mem s1 (tBadgeA sd') = L.mem s (tBadgeA sd') := hA1 _ (a_badge hsa).1 ⟨sd', hsT, (a_badge hsa).2⟩
  have hfw : L.mem s1 (tFlagsA sd') = L.mem s (tFlagsA sd') := hA1 _ (a_flags hsa).1 ⟨sd', hsT, (a_flags hsa).2⟩
  step as ⟨bdg, hbdg⟩
  step as ⟨fl, hfl⟩
  step as ⟨i, hi, hi'⟩
  step as ⟨i1, hi1, hi1'⟩
  step as ⟨i2, hi2, hi2'⟩
  have hgi : (i != 0#u64) = dd.senderCanGrant := by
    rw [← flags_grant dd, ← hflags, ← hfw, ← hfl]
    congr 1
    exact UScalar.eq_of_val_eq hi
  have hc : (i2 != 0#u64) = true := by
    have hfc := flags_call dd
    rw [hcall _ _ hstd] at hfc
    have e : i2 = flagsOf dd &&& endpoint.FLAG_CALL := by
      rw [← hflags, ← hfw, ← hfl]; exact UScalar.eq_of_val_eq hi2
    rw [e]; exact hfc
  have hgr : (i1 != 0#u64) = dd.senderCanGrantReply := by
    rw [← flags_grantReply dd, ← hflags, ← hfw, ← hfl]
    congr 1
    exact UScalar.eq_of_val_eq hi1
  have hbb : bdg.bv = dd.senderBadge := by rw [hbdg, hbw]; exact hbadge
  have hcaps' := hcaps _ _ hstd
  rw [← hgi] at hcaps'
  refine WP.spec_bind (hX.xregs hP s1 a σ1 hR1 hS1 hsT ht (Ne.symm hts) hks1 hkt1 hfs hrb e bdg
    (i != 0#u64) hcaps') ?_
  rintro s2 ⟨e2, hR2, hS2, hA2⟩
  set σ2 := updK σ1 t.bv (.tcb (xferTcb xt xs bdg.bv))
  have e2' : Fl4Spec.doIpcTransfer (Z := Unit) sd'.bv (some e.bv) dd.senderBadge dd.senderCanGrant t.bv σ1 =
      ({((), σ2)}, False) := by rw [← hbb, ← hgi]; exact e2
  have hst' : sd'.bv ≠ t.bv := bv_inj (Ne.symm hts)
  have hks2 : σ2.kheap sd'.bv = some (.tcb xs) := by simp [σ2, hst', hks1]
  have hk2e : σ2.kheap e.bv = some (.endpoint (epDeq (.sendEP (sd'.bv :: q)) sd'.bv)) := by
    simp [σ2, σ1, hte.symm]
  refine WP.spec_bind (hTl.sporadicAssert s2 σ2 sd' hR2 hS2 hsT) ?_
  rintro s3 ⟨σ3, hA, hf3, hv3, hS3⟩
  have hR3 := hR2.frame hP hf3 hv3
  obtain ⟨xs3, hks3, hs3st, -, -, hs3f, -⟩ := hv3.2.2.1 _ _ hks2
  have hk3e := hv3.1 _ _ hk2e
  have hxs3 := hR3.at_tcb hsT hks3
  step as ⟨ft, hft⟩
  have hft0 : ft = fl4_abi.consts.fault.NullFault := by
    rw [hft, hxs3.fault0.2 (hs3f.trans hfs)]; unfold fl4_abi.consts.fault.NullFault; rfl
  simp only [hc, hft0, ↓reduceIte]
  -- the sender is in no queue
  have hb3 : L.mem s3 (tBlockA sd') = e := by
    rw [hf3 _ (a_blk hsa).1 (Or.inr (Or.inr (Or.inl ⟨sd', hsT, Or.inl (a_blk hsa).2⟩)))]
    rw [hA2 _ (a_blk hsa).1 ?_, hA1 _ (a_blk hsa).1 ⟨sd', hsT, (a_blk hsa).2⟩, hsb]
    rintro ⟨r', hr'⟩
    have := tcb_disj hP ht hsT hts.symm
    rw [val_blk hsa, regA_val hta (regIdx_lt r')] at hr'; have := regIdx_lt r'; omega
  have hq3 := dequeued_not_queued hR3 he hb3 hk3e (epDeq_not_mem _)
  -- the reply object and the sender's SC
  obtain ⟨xr, hkr, hxr⟩ := hR.reply rv hrvR
  rw [hrv0, optRef_zero] at hxr
  have hre : rv.bv ≠ e.bv := kheap_ne hkr hk (fun _ h1 h2 => by subst h1; cases h2)
  have hrt : rv.bv ≠ t.bv := kheap_ne hkr hkt (fun _ h1 h2 => by subst h1; cases h2)
  have hrs : rv.bv ≠ sd'.bv := kheap_ne hkr hks (fun _ h1 h2 => by subst h1; cases h2)
  have hkr2 : σ2.kheap rv.bv = some (.reply xr) := by simp [σ2, σ1, hre, hrt, hkr]
  obtain ⟨xr3, hkr3, -⟩ := hv3.2.1 _ _ hkr2
  have hkt2 : σ2.kheap t.bv = some (.tcb (xferTcb xt xs bdg.bv)) := by simp [σ2]
  obtain ⟨xt3, hkt3, -⟩ := hv3.2.2.1 _ _ hkt2
  obtain ⟨y, hy, hysc⟩ := hSc.sporadicSc σ2 σ3 sd' xs hA hks2
  rw [hks3] at hy; cases hy
  have hsc3 : xs3.tcbSchedContext = none := hysc.trans hscn
  have hscw : L.mem s3 (scA sd') = 0#u64 := (hSc.scRel s3 σ3 sd' xs3 hS3 hks3 hsT).2 hsc3
  have hspec := receiveIpc_sendCallPush_eq (rr := r') b rights blk hkr hxr hkt hbn hk hks hse hstd (hcall _ _ hstd)
    (hg _ _ hstd) e2' hA hks3 (hs3f.trans hfs) hsc3 (t := t.bv) (r := rv.bv)
  have hrvne : (rv != 0#u64) = true := by simp [rep_ne0 hP hrvR]
  have hpush := hX.push hP s3 a σ3 hR3 hS3 hsT hks3 hkt3 hq3 (hX.ns_ep _ (by rw [hs3st, hstd]; simp [tsCode])) hrvR hkr3
  have hg' := hg _ _ hstd
  cases hgg : dd.senderCanGrant with
  | true =>
    rw [hgg] at hgi
    simp only [hgi, hrvne, ↓reduceIte]
    step as ⟨i3, hi3⟩
    rw [hi3, hscw]
    simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    apply ok_bind_spec
    refine WP.spec_mono hpush ?_
    rintro ⟨s4, a4⟩ ⟨ha4, hp4, hR4, hS4⟩
    rw [hspec, hp4]
    exact ⟨ha4, by simp, _, by simp, hR4, hS4⟩

  | false =>
    rw [hgg] at hgi hg'
    simp only [Bool.false_eq_true, false_or] at hg'
    rw [hg'] at hgr
    simp only [hgi, hgr, hrvne, Bool.false_eq_true, ↓reduceIte]
    step as ⟨i3, hi3⟩
    rw [hi3, hscw]
    simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    apply ok_bind_spec
    refine WP.spec_mono hpush ?_
    rintro ⟨s4, a4⟩ ⟨ha4, hp4, hR4, hS4⟩
    rw [hspec, hp4]
    exact ⟨ha4, by simp, _, by simp, hR4, hS4⟩


theorem receive_ipc_sendCallInactive_gen (hX : EpSteps st A ar T E R B SR NS)
    (hTl : EpTailHyps st A T E R B SR) (hP : EPlaced T E R B) (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hR : EpStateRel T E R B (L.mem s) σ) (hSR : SR s σ)
    {t : U64} (ht : t ∈ T) {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt))
    (hnb : tsCode xt.tcbState ≠ 3 ∧ tsCode xt.tcbState ≠ 4) (hbn : xt.tcbBoundNotification = none)
    (hrb : ipcBufOf true xt = none)
    {e sd : U64} (he : e ∈ E) {q : List Fl4Spec.ObjRef} (hk : σ.kheap e.bv = some (.endpoint (.sendEP (sd.bv :: q))))
    {xs : Fl4Spec.Tcb} (hks : σ.kheap sd.bv = some (.tcb xs)) (hfs : xs.tcbFault = none)
    (hcall : ∀ e' dd, xs.tcbState = .blockedOnSend e' dd → dd.senderIsCall = true)
    (hcaps : ∀ e' dd, xs.tcbState = .blockedOnSend e' dd → dd.senderCanGrant = false ∨ ipcBufOf false xs = none ∨
      Fl4Spec.unat (Fl4Spec.dataToMessageInfo (xs.tcbArch.tcbContext.userRegs Fl4Spec.msg_info_register)).miExtraCaps = 0)
    (cb : U64) (c1 c2 c3 c4 : Bool) {rc : capability.Cap} {rc' : Fl4Spec.Cap} {rv : U64}
    (hrc : ReplyArg R (L.mem s) rc rc' rv)
    (hno : (∀ e' dd, xs.tcbState = .blockedOnSend e' dd → dd.senderCanGrant = false ∧ dd.senderCanGrantReply = false) ∨
      rv = 0#u64) (b : Fl4Spec.Badge) (rights : Fl4Spec.CapRights) (blk : Bool) :
    endpoint.receive_ipc st ar s a t (.Endpoint e cb c1 c2 c3 c4) blk rc ⦃ r => r.2 = a ∧
      ¬ (Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) blk rc' σ).2 ∧
      ∃ σ', ((), σ') ∈ (Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) blk rc' σ).1 ∧
        EpStateRel T E R B (L.mem r.1) σ' ∧ SR r.1 σ' ⦄ := by
  have hx := hR.at_ep he hk
  have hxt := hR.at_tcb ht hkt
  have hta := hP.tcb t ht
  have hbound : L.mem s (tBoundA t) = 0#u64 := optRef_none (hxt.bound.symm.trans hbn)
  have hsr := replyArg_spec hP hR hrc
  obtain ⟨hst1, xs0, hxs0, hq, hQ, hB⟩ := hx
  obtain ⟨sd', xs', rfl⟩ := List.exists_cons_of_ne_nil hxs0
  simp only [List.map_cons, List.cons.injEq] at hq
  obtain ⟨hd', hq'⟩ := hq
  have hdd : sd' = sd := eq_of_bv hd'.symm
  subst hdd
  have hsT : sd' ∈ T := hQ.mem sd' (by simp)
  have hsa := hP.tcb sd' hsT
  have hxs := hR.at_tcb hsT hks
  have hs4 : (L.mem s (tStA sd')).val = 4 := (hB sd' (by simp)).1
  have hsb : L.mem s (tBlockA sd') = e := (hB sd' (by simp)).2
  obtain ⟨e', dd, hstd⟩ := tsCode_four (hxs.st.symm.trans hs4)
  have he' : e' = e.bv := by
    have := hxs.blk e' (by rw [hstd]; rfl); rw [hsb] at this; exact this.symm
  subst he'
  obtain ⟨hbadge, hflags⟩ := hxs.send _ _ hstd
  have hts : t ≠ sd' := by
    intro h; subst h; exact hnb.2 (hxt.st.symm.trans hs4)
  have hse : sd'.bv ≠ e.bv := kheap_ne hks hk (fun _ h1 h2 => by subst h1; cases h2)
  have hte : t.bv ≠ e.bv := kheap_ne hkt hk (fun _ h1 h2 => by subst h1; cases h2)
  apply receive_ipc_pre s a t e cb c1 c2 c3 c4 blk rc rc' rv hrc hbound
  step as ⟨st0, hst0⟩
  rw [hst0, epState_eq, hst1]
  rw [if_neg (by rw [ep_state_vals.1]; decide), if_neg (by rw [ep_state_vals.2.2]; decide)]
  unfold endpoint.receive_from_sender
  step as ⟨q0, hq0⟩
  have hhead : q0.head = sd' := by rw [hq0, epQ_eq]; exact hQ.head
  rw [hhead]
  refine WP.spec_bind (hX.deq hP s σ hR hSR he hk (d := sd') (by simp [Fl4Spec.Endpoint.epQueue])) ?_
  rintro s1 ⟨e1, hR1, hS1, hA1⟩
  set σ1 := updK σ e.bv (.endpoint (epDeq (.sendEP (sd'.bv :: q)) sd'.bv))
  have hkt1 : σ1.kheap t.bv = some (.tcb xt) := by simp [σ1, hte, hkt]
  have hks1 : σ1.kheap sd'.bv = some (.tcb xs) := by simp [σ1, hse, hks]
  have hbw : L.mem s1 (tBadgeA sd') = L.mem s (tBadgeA sd') := hA1 _ (a_badge hsa).1 ⟨sd', hsT, (a_badge hsa).2⟩
  have hfw : L.mem s1 (tFlagsA sd') = L.mem s (tFlagsA sd') := hA1 _ (a_flags hsa).1 ⟨sd', hsT, (a_flags hsa).2⟩
  step as ⟨bdg, hbdg⟩
  step as ⟨fl, hfl⟩
  step as ⟨i, hi, hi'⟩
  step as ⟨i1, hi1, hi1'⟩
  step as ⟨i2, hi2, hi2'⟩
  have hgi : (i != 0#u64) = dd.senderCanGrant := by
    rw [← flags_grant dd, ← hflags, ← hfw, ← hfl]
    congr 1
    exact UScalar.eq_of_val_eq hi
  have hc : (i2 != 0#u64) = true := by
    have hfc := flags_call dd
    rw [hcall _ _ hstd] at hfc
    have e : i2 = flagsOf dd &&& endpoint.FLAG_CALL := by
      rw [← hflags, ← hfw, ← hfl]; exact UScalar.eq_of_val_eq hi2
    rw [e]; exact hfc
  have hgr : (i1 != 0#u64) = dd.senderCanGrantReply := by
    rw [← flags_grantReply dd, ← hflags, ← hfw, ← hfl]
    congr 1
    exact UScalar.eq_of_val_eq hi1
  have hbb : bdg.bv = dd.senderBadge := by rw [hbdg, hbw]; exact hbadge
  have hcaps' := hcaps _ _ hstd
  rw [← hgi] at hcaps'
  refine WP.spec_bind (hX.xregs hP s1 a σ1 hR1 hS1 hsT ht (Ne.symm hts) hks1 hkt1 hfs hrb e bdg
    (i != 0#u64) hcaps') ?_
  rintro s2 ⟨e2, hR2, hS2, hA2⟩
  set σ2 := updK σ1 t.bv (.tcb (xferTcb xt xs bdg.bv))
  have e2' : Fl4Spec.doIpcTransfer (Z := Unit) sd'.bv (some e.bv) dd.senderBadge dd.senderCanGrant t.bv σ1 =
      ({((), σ2)}, False) := by rw [← hbb, ← hgi]; exact e2
  have hst' : sd'.bv ≠ t.bv := bv_inj (Ne.symm hts)
  have hks2 : σ2.kheap sd'.bv = some (.tcb xs) := by simp [σ2, hst', hks1]
  have hk2e : σ2.kheap e.bv = some (.endpoint (epDeq (.sendEP (sd'.bv :: q)) sd'.bv)) := by
    simp [σ2, σ1, hte.symm]
  refine WP.spec_bind (hTl.sporadicAssert s2 σ2 sd' hR2 hS2 hsT) ?_
  rintro s3 ⟨σ3, hA, hf3, hv3, hS3⟩
  have hR3 := hR2.frame hP hf3 hv3
  obtain ⟨xs3, hks3, hs3st, -, -, hs3f, -⟩ := hv3.2.2.1 _ _ hks2
  have hk3e := hv3.1 _ _ hk2e
  have hxs3 := hR3.at_tcb hsT hks3
  step as ⟨ft, hft⟩
  have hft0 : ft = fl4_abi.consts.fault.NullFault := by
    rw [hft, hxs3.fault0.2 (hs3f.trans hfs)]; unfold fl4_abi.consts.fault.NullFault; rfl
  simp only [hc, hft0, ↓reduceIte]
  -- the sender is in no queue
  have hb3 : L.mem s3 (tBlockA sd') = e := by
    rw [hf3 _ (a_blk hsa).1 (Or.inr (Or.inr (Or.inl ⟨sd', hsT, Or.inl (a_blk hsa).2⟩)))]
    rw [hA2 _ (a_blk hsa).1 ?_, hA1 _ (a_blk hsa).1 ⟨sd', hsT, (a_blk hsa).2⟩, hsb]
    rintro ⟨r', hr'⟩
    have := tcb_disj hP ht hsT hts.symm
    rw [val_blk hsa, regA_val hta (regIdx_lt r')] at hr'; have := regIdx_lt r'; omega
  have hq3 := dequeued_not_queued hR3 he hb3 hk3e (epDeq_not_mem _)
  have hcond : ¬ ((dd.senderCanGrant = true ∨ dd.senderCanGrantReply = true) ∧ optRef rv ≠ none) := by
    rintro ⟨h1, h2⟩
    rcases hno with h | h
    · obtain ⟨g1, g2⟩ := h _ _ hstd; rw [g1, g2] at h1; simp at h1
    · rw [h, optRef_zero] at h2; exact h2 rfl
  have hspec := receiveIpc_sendCallInactive_eq b rights blk hsr hkt hbn hk hks hse hstd (hcall _ _ hstd) hcond
    e2' hA hks3 (hs3f.trans hfs) (t := t.bv)
  rcases hno with h | h
  · obtain ⟨g1, g2⟩ := h _ _ hstd
    rw [g1] at hgi
    rw [g2] at hgr
    simp only [hgi, hgr, Bool.false_eq_true, ↓reduceIte]
    refine WP.spec_bind (hX.sts hP s3 σ3 hR3 hS3 hsT hks3 hq3 (hX.ns_ep _ (by rw [hs3st, hstd]; simp [tsCode])) .inactive (by simp [tsCode])
      sched.TS_INACTIVE (by unfold sched.TS_INACTIVE; rfl)) ?_
    rintro s4 ⟨h1, h2⟩
    simp only [WP.spec_ok]
    rw [hspec, setThreadState_eq _ hks3]
    exact ⟨trivial, by simp, _, by simp, h1, h2⟩
  · simp only [h, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, ite_self]
    refine WP.spec_bind (hX.sts hP s3 σ3 hR3 hS3 hsT hks3 hq3 (hX.ns_ep _ (by rw [hs3st, hstd]; simp [tsCode])) .inactive (by simp [tsCode])
      sched.TS_INACTIVE (by unfold sched.TS_INACTIVE; rfl)) ?_
    rintro s4 ⟨h1, h2⟩
    simp only [WP.spec_ok]
    rw [hspec, setThreadState_eq _ hks3]
    exact ⟨trivial, by simp, _, by simp, h1, h2⟩

theorem receive_ipc_send_gen (hX : EpSteps st A ar T E R B SR NS)
    (hTl : EpTailHyps st A T E R B SR) (hP : EPlaced T E R B) (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hR : EpStateRel T E R B (L.mem s) σ) (hSR : SR s σ)
    {t : U64} (ht : t ∈ T) {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt))
    (hnb : tsCode xt.tcbState ≠ 3 ∧ tsCode xt.tcbState ≠ 4) (hbn : xt.tcbBoundNotification = none)
    (hrb : ipcBufOf true xt = none)
    {e sd : U64} (he : e ∈ E) {q : List Fl4Spec.ObjRef} (hk : σ.kheap e.bv = some (.endpoint (.sendEP (sd.bv :: q))))
    {xs : Fl4Spec.Tcb} (hks : σ.kheap sd.bv = some (.tcb xs)) (hfs : xs.tcbFault = none)
    (hcall : ∀ e' dd, xs.tcbState = .blockedOnSend e' dd → dd.senderIsCall = false)
    (hcaps : ∀ e' dd, xs.tcbState = .blockedOnSend e' dd → dd.senderCanGrant = false ∨ ipcBufOf false xs = none ∨
      Fl4Spec.unat (Fl4Spec.dataToMessageInfo (xs.tcbArch.tcbContext.userRegs Fl4Spec.msg_info_register)).miExtraCaps = 0)
    (cb : U64) (c1 c2 c3 c4 : Bool) {rc : capability.Cap} {rc' : Fl4Spec.Cap} {rv : U64}
    (hrc : ReplyArg R (L.mem s) rc rc' rv) (b : Fl4Spec.Badge) (rights : Fl4Spec.CapRights) (blk : Bool) :
    endpoint.receive_ipc st ar s a t (.Endpoint e cb c1 c2 c3 c4) blk rc ⦃ r => r.2 = a ∧
      ¬ (Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) blk rc' σ).2 ∧
      ∃ σ', ((), σ') ∈ (Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) blk rc' σ).1 ∧
        EpStateRel T E R B (L.mem r.1) σ' ∧ SR r.1 σ' ⦄ := by
  have hx := hR.at_ep he hk
  have hxt := hR.at_tcb ht hkt
  have hta := hP.tcb t ht
  have hbound : L.mem s (tBoundA t) = 0#u64 := optRef_none (hxt.bound.symm.trans hbn)
  have hsr := replyArg_spec hP hR hrc
  obtain ⟨hst1, xs0, hxs0, hq, hQ, hB⟩ := hx
  obtain ⟨sd', xs', rfl⟩ := List.exists_cons_of_ne_nil hxs0
  simp only [List.map_cons, List.cons.injEq] at hq
  obtain ⟨hd', hq'⟩ := hq
  have hdd : sd' = sd := eq_of_bv hd'.symm
  subst hdd
  have hsT : sd' ∈ T := hQ.mem sd' (by simp)
  have hsa := hP.tcb sd' hsT
  have hxs := hR.at_tcb hsT hks
  have hs4 : (L.mem s (tStA sd')).val = 4 := (hB sd' (by simp)).1
  have hsb : L.mem s (tBlockA sd') = e := (hB sd' (by simp)).2
  obtain ⟨e', dd, hstd⟩ := tsCode_four (hxs.st.symm.trans hs4)
  have he' : e' = e.bv := by
    have := hxs.blk e' (by rw [hstd]; rfl); rw [hsb] at this; exact this.symm
  subst he'
  obtain ⟨hbadge, hflags⟩ := hxs.send _ _ hstd
  have hts : t ≠ sd' := by
    intro h; subst h; exact hnb.2 (hxt.st.symm.trans hs4)
  have hse : sd'.bv ≠ e.bv := kheap_ne hks hk (fun _ h1 h2 => by subst h1; cases h2)
  have hte : t.bv ≠ e.bv := kheap_ne hkt hk (fun _ h1 h2 => by subst h1; cases h2)
  apply receive_ipc_pre s a t e cb c1 c2 c3 c4 blk rc rc' rv hrc hbound
  step as ⟨st0, hst0⟩
  rw [hst0, epState_eq, hst1]
  rw [if_neg (by rw [ep_state_vals.1]; decide), if_neg (by rw [ep_state_vals.2.2]; decide)]
  unfold endpoint.receive_from_sender
  step as ⟨q0, hq0⟩
  have hhead : q0.head = sd' := by rw [hq0, epQ_eq]; exact hQ.head
  rw [hhead]
  refine WP.spec_bind (hX.deq hP s σ hR hSR he hk (d := sd') (by simp [Fl4Spec.Endpoint.epQueue])) ?_
  rintro s1 ⟨e1, hR1, hS1, hA1⟩
  set σ1 := updK σ e.bv (.endpoint (epDeq (.sendEP (sd'.bv :: q)) sd'.bv))
  have hkt1 : σ1.kheap t.bv = some (.tcb xt) := by simp [σ1, hte, hkt]
  have hks1 : σ1.kheap sd'.bv = some (.tcb xs) := by simp [σ1, hse, hks]
  have hbw : L.mem s1 (tBadgeA sd') = L.mem s (tBadgeA sd') := hA1 _ (a_badge hsa).1 ⟨sd', hsT, (a_badge hsa).2⟩
  have hfw : L.mem s1 (tFlagsA sd') = L.mem s (tFlagsA sd') := hA1 _ (a_flags hsa).1 ⟨sd', hsT, (a_flags hsa).2⟩
  step as ⟨bdg, hbdg⟩
  step as ⟨fl, hfl⟩
  step as ⟨i, hi, hi'⟩
  step as ⟨i1, hi1, hi1'⟩
  step as ⟨i2, hi2, hi2'⟩
  have hg : (i != 0#u64) = dd.senderCanGrant := by
    rw [← flags_grant dd, ← hflags, ← hfw, ← hfl]
    congr 1
    exact UScalar.eq_of_val_eq hi
  have hc : (i2 != 0#u64) = false := by
    rw [← hcall _ _ hstd, ← flags_call dd, ← hflags, ← hfw, ← hfl]
    congr 1
    exact UScalar.eq_of_val_eq hi2
  have hbb : bdg.bv = dd.senderBadge := by rw [hbdg, hbw]; exact hbadge
  have hcaps' := hcaps _ _ hstd
  rw [← hg] at hcaps'
  refine WP.spec_bind (hX.xregs hP s1 a σ1 hR1 hS1 hsT ht (Ne.symm hts) hks1 hkt1 hfs hrb e bdg
    (i != 0#u64) hcaps') ?_
  rintro s2 ⟨e2, hR2, hS2, hA2⟩
  set σ2 := updK σ1 t.bv (.tcb (xferTcb xt xs bdg.bv))
  have e2' : Fl4Spec.doIpcTransfer (Z := Unit) sd'.bv (some e.bv) dd.senderBadge dd.senderCanGrant t.bv σ1 =
      ({((), σ2)}, False) := by rw [← hbb, ← hg]; exact e2
  have hst' : sd'.bv ≠ t.bv := bv_inj (Ne.symm hts)
  have hks2 : σ2.kheap sd'.bv = some (.tcb xs) := by simp [σ2, hst', hks1]
  have hk2e : σ2.kheap e.bv = some (.endpoint (epDeq (.sendEP (sd'.bv :: q)) sd'.bv)) := by
    simp [σ2, σ1, hte.symm]
  refine WP.spec_bind (hTl.sporadicAssert s2 σ2 sd' hR2 hS2 hsT) ?_
  rintro s3 ⟨σ3, hA, hf3, hv3, hS3⟩
  have hR3 := hR2.frame hP hf3 hv3
  obtain ⟨xs3, hks3, hs3st, -, -, hs3f, -⟩ := hv3.2.2.1 _ _ hks2
  have hk3e := hv3.1 _ _ hk2e
  have hxs3 := hR3.at_tcb hsT hks3
  step as ⟨ft, hft⟩
  have hft0 : ft = fl4_abi.consts.fault.NullFault := by
    rw [hft, hxs3.fault0.2 (hs3f.trans hfs)]; unfold fl4_abi.consts.fault.NullFault; rfl
  simp only [hc, hft0, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  -- the sender is in no queue
  have hb3 : L.mem s3 (tBlockA sd') = e := by
    rw [hf3 _ (a_blk hsa).1 (Or.inr (Or.inr (Or.inl ⟨sd', hsT, Or.inl (a_blk hsa).2⟩)))]
    rw [hA2 _ (a_blk hsa).1 ?_, hA1 _ (a_blk hsa).1 ⟨sd', hsT, (a_blk hsa).2⟩, hsb]
    rintro ⟨r', hr'⟩
    have := tcb_disj hP ht hsT hts.symm
    rw [val_blk hsa, regA_val hta (regIdx_lt r')] at hr'; have := regIdx_lt r'; omega
  have hq3 := dequeued_not_queued hR3 he hb3 hk3e (epDeq_not_mem _)
  refine WP.spec_bind (hX.sts hP s3 σ3 hR3 hS3 hsT hks3 hq3 (hX.ns_ep _ (by rw [hs3st, hstd]; simp [tsCode])) .running (by simp [tsCode])
    sched.TS_RUNNING (by unfold sched.TS_RUNNING; rfl)) ?_
  rintro s4 ⟨hR4, hS4⟩
  have hspec := receiveIpc_send_eq b rights blk hsr hkt hbn hk hks hse hstd (hcall _ _ hstd) e2' hA hks3
    (hs3f.trans hfs)
  rw [hspec]
  refine WP.spec_mono (hTl.switchTo s4 a _ sd' hR4 hS4 hsT) ?_
  rintro ⟨s5, a5⟩ ⟨ha5, hnf, σ', hm, hf, hv, hS'⟩
  exact ⟨ha5, hnf, σ', hm, hR4.frame hP hf hv, hS'⟩

theorem send_ipc_recv_buf_gen (hX : EpSteps st A ar T E R B SR NS) (hTl : EpTailHyps st A T E R B SR)
    (hP : EPlaced T E R B) (s : S) (a : A) (σ : Fl4Spec.State Unit) (hR : EpStateRel T E R B (L.mem s) σ)
    (hSR : SR s σ) {t : U64} (ht : t ∈ T) {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt))
    (hnb : tsCode xt.tcbState ≠ 3 ∧ tsCode xt.tcbState ≠ 4) (hft : xt.tcbFault = none)
    {e d : U64} (he : e ∈ E) {q : List Fl4Spec.ObjRef} (hk : σ.kheap e.bv = some (.endpoint (.recvEP (d.bv :: q))))
    {xd : Fl4Spec.Tcb} (hkd : σ.kheap d.bv = some (.tcb xd)) {rp : Fl4Spec.ObjRef} (hrb : ipcBufOf true xd = some rp)
    (badge : U64) (g gr : Bool)
    (hcaps : g = false ∨ ipcBufOf false xt = none ∨
      Fl4Spec.unat (Fl4Spec.dataToMessageInfo (xt.tcbArch.tcbContext.userRegs Fl4Spec.msg_info_register)).miExtraCaps = 0)
    (hback : ∀ e' r dd xr, xd.tcbState = .blockedOnReceive e' (some r) dd → σ.kheap r = some (.reply xr) →
      xr.replyTcb = some d.bv)
    (blk : Bool) :
    endpoint.send_ipc st ar s a blk false badge g gr false t e ⦃ r => r.2 = a ∧
      ¬ (Fl4Spec.sendIpc (Z := Unit) blk false badge.bv g gr false t.bv e.bv σ).2 ∧
      ∃ σ', ((), σ') ∈ (Fl4Spec.sendIpc (Z := Unit) blk false badge.bv g gr false t.bv e.bv σ).1 ∧
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
  refine WP.spec_bind (hX.xbuf hP s1 a σ1 hR1 hS1 ht hdT htd hkt1 hkd1 hft hrb e badge g
    hcaps) ?_
  rintro s2 ⟨σ2, e2, hR2, hS2, hA2, hk2o, x2, hkd2, hx2st⟩
  have htd' : t.bv ≠ d'.bv := bv_inj htd
  have hkt2 : σ2.kheap t.bv = some (.tcb xt) := (hk2o _ htd').trans hkt1
  have hst2' : x2.tcbState = .blockedOnReceive e.bv rep dd := by rw [hx2st, hstd]
  -- `d'` is in no endpoint queue from `σ1` on
  have hk1e : σ1.kheap e.bv = some (.endpoint (epDeq (.recvEP (d'.bv :: q)) d'.bv)) := by simp [σ1]
  have hdb1 : L.mem s1 (tBlockA d') = e := by
    rw [hA1 _ (a_blk hda).1 ⟨d', hdT, (a_blk hda).2⟩, hdb]
  have hq1 := dequeued_not_queued hR1 he hdb1 hk1e (epDeq_not_mem _)
  have hq2 : ∀ e'' ∈ E, ∀ z, σ2.kheap e''.bv = some (.endpoint z) → d'.bv ∉ z.epQueue := by
    intro e'' he'' z hz
    have hne : d'.bv ≠ e''.bv := by intro h; rw [← h, hkd2] at hz; cases hz
    exact hq1 e'' he'' z (by rw [← hk2o _ (Ne.symm hne)]; exact hz)
  -- the reply word
  have hrw : L.mem s2 (tReplyA d') = L.mem s (tReplyA d') := by
    rw [hA2 _ (a_reply hda).1 ⟨?_, ?_⟩, hA1 _ (a_reply hda).1 ⟨d', hdT, (a_reply hda).2⟩]
    · rintro ⟨r', hr'⟩
      rw [val_reply hda, regA_val hda (regIdx_lt r')] at hr'; have := regIdx_lt r'; omega
    · rintro ⟨wp, hw, he⟩
      have := hP.bt wp hw d' hdT
      have := congrArg UScalar.val he
      rw [val_reply hda] at this; omega
  step as ⟨i, hi⟩
  rw [hi, hrw]
  simp only [Bool.false_eq_true, ↓reduceIte]
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
      have hkr2 : σ2.kheap w.bv = some (.reply xr) := (hk2o _ hwd).trans (by simp [σ1, hwe, hkr])
      have hb' := hback e.bv w.bv dd xr (by rw [hstd, hrp]) hkr
      refine WP.spec_mono (hX.unlink hP s2 σ2 hR2 hS2 hdT hkd2 hst2' hwR hkr2 hb' hq2) ?_
      rintro s3 ⟨e3, hR3, hS3⟩
      refine ⟨_, { x2 with tcbState := .inactive }, hR3, hS3, e3, ?_, ?_, ?_, ?_⟩
      · rw [stsAct_kheap]; simp [htd', hwt.symm, hkt2]
      · rw [stsAct_kheap]; simp
      · simp [tsCode]
      · intro e'' he'' z hz
        rw [stsAct_kheap] at hz
        have hne : d'.bv ≠ e''.bv := by intro h; rw [← h] at hz; simp at hz
        have hne' : w.bv ≠ e''.bv := by intro h; rw [← h] at hz; simp [hwd] at hz
        exact hq2 e'' he'' z (by simpa [Ne.symm hne, Ne.symm hne'] using hz)
  · rintro s3 ⟨σ3, x3, hR3, hS3, hU, hkt3, hkd3, hns3, hq3⟩
    have hxt3 := hR3.at_tcb ht hkt3
    step as ⟨i1, hi1⟩
    have hf0 : i1 = fl4_abi.consts.fault.NullFault := by
      rw [hi1, hxt3.fault0.2 hft]; unfold fl4_abi.consts.fault.NullFault; rfl
    simp only [hf0, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    apply ok_bind_spec
    refine WP.spec_bind (hX.sts hP s3 σ3 hR3 hS3 hdT hkd3 hq3 (hX.ns_ep _ hns3) .running (by simp [tsCode])
      sched.TS_RUNNING (by unfold sched.TS_RUNNING; rfl)) ?_
    rintro s5 ⟨hR5, hS5⟩
    have hspec := sendIpc_recv_eq hk hkd hde hstd blk badge.bv g gr e2 hU hkt3 hft hkd3 (t := t.bv)
    rw [hspec]
    refine WP.spec_mono (hTl.wakeTail s5 a _ d' hR5 hS5 hdT) ?_
    rintro ⟨s7, a7⟩ ⟨ha7, hnf, σ', hm, hf, hv, hS'⟩
    exact ⟨ha7, hnf, σ', hm, hR5.frame hP hf hv, hS'⟩

theorem receive_ipc_send_buf_gen (hX : EpSteps st A ar T E R B SR NS)
    (hTl : EpTailHyps st A T E R B SR) (hP : EPlaced T E R B) (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hR : EpStateRel T E R B (L.mem s) σ) (hSR : SR s σ)
    {t : U64} (ht : t ∈ T) {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt))
    (hnb : tsCode xt.tcbState ≠ 3 ∧ tsCode xt.tcbState ≠ 4) (hbn : xt.tcbBoundNotification = none)
    {rp : Fl4Spec.ObjRef} (hrb : ipcBufOf true xt = some rp)
    {e sd : U64} (he : e ∈ E) {q : List Fl4Spec.ObjRef} (hk : σ.kheap e.bv = some (.endpoint (.sendEP (sd.bv :: q))))
    {xs : Fl4Spec.Tcb} (hks : σ.kheap sd.bv = some (.tcb xs)) (hfs : xs.tcbFault = none)
    (hcall : ∀ e' dd, xs.tcbState = .blockedOnSend e' dd → dd.senderIsCall = false)
    (hcaps : ∀ e' dd, xs.tcbState = .blockedOnSend e' dd → dd.senderCanGrant = false ∨ ipcBufOf false xs = none ∨
      Fl4Spec.unat (Fl4Spec.dataToMessageInfo (xs.tcbArch.tcbContext.userRegs Fl4Spec.msg_info_register)).miExtraCaps = 0)
    (cb : U64) (c1 c2 c3 c4 : Bool) {rc : capability.Cap} {rc' : Fl4Spec.Cap} {rv : U64}
    (hrc : ReplyArg R (L.mem s) rc rc' rv) (b : Fl4Spec.Badge) (rights : Fl4Spec.CapRights) (blk : Bool) :
    endpoint.receive_ipc st ar s a t (.Endpoint e cb c1 c2 c3 c4) blk rc ⦃ r => r.2 = a ∧
      ¬ (Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) blk rc' σ).2 ∧
      ∃ σ', ((), σ') ∈ (Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) blk rc' σ).1 ∧
        EpStateRel T E R B (L.mem r.1) σ' ∧ SR r.1 σ' ⦄ := by
  have hx := hR.at_ep he hk
  have hxt := hR.at_tcb ht hkt
  have hta := hP.tcb t ht
  have hbound : L.mem s (tBoundA t) = 0#u64 := optRef_none (hxt.bound.symm.trans hbn)
  have hsr := replyArg_spec hP hR hrc
  obtain ⟨hst1, xs0, hxs0, hq, hQ, hB⟩ := hx
  obtain ⟨sd', xs', rfl⟩ := List.exists_cons_of_ne_nil hxs0
  simp only [List.map_cons, List.cons.injEq] at hq
  obtain ⟨hd', hq'⟩ := hq
  have hdd : sd' = sd := eq_of_bv hd'.symm
  subst hdd
  have hsT : sd' ∈ T := hQ.mem sd' (by simp)
  have hsa := hP.tcb sd' hsT
  have hxs := hR.at_tcb hsT hks
  have hs4 : (L.mem s (tStA sd')).val = 4 := (hB sd' (by simp)).1
  have hsb : L.mem s (tBlockA sd') = e := (hB sd' (by simp)).2
  obtain ⟨e', dd, hstd⟩ := tsCode_four (hxs.st.symm.trans hs4)
  have he' : e' = e.bv := by
    have := hxs.blk e' (by rw [hstd]; rfl); rw [hsb] at this; exact this.symm
  subst he'
  obtain ⟨hbadge, hflags⟩ := hxs.send _ _ hstd
  have hts : t ≠ sd' := by
    intro h; subst h; exact hnb.2 (hxt.st.symm.trans hs4)
  have hse : sd'.bv ≠ e.bv := kheap_ne hks hk (fun _ h1 h2 => by subst h1; cases h2)
  have hte : t.bv ≠ e.bv := kheap_ne hkt hk (fun _ h1 h2 => by subst h1; cases h2)
  apply receive_ipc_pre s a t e cb c1 c2 c3 c4 blk rc rc' rv hrc hbound
  step as ⟨st0, hst0⟩
  rw [hst0, epState_eq, hst1]
  rw [if_neg (by rw [ep_state_vals.1]; decide), if_neg (by rw [ep_state_vals.2.2]; decide)]
  unfold endpoint.receive_from_sender
  step as ⟨q0, hq0⟩
  have hhead : q0.head = sd' := by rw [hq0, epQ_eq]; exact hQ.head
  rw [hhead]
  refine WP.spec_bind (hX.deq hP s σ hR hSR he hk (d := sd') (by simp [Fl4Spec.Endpoint.epQueue])) ?_
  rintro s1 ⟨e1, hR1, hS1, hA1⟩
  set σ1 := updK σ e.bv (.endpoint (epDeq (.sendEP (sd'.bv :: q)) sd'.bv))
  have hkt1 : σ1.kheap t.bv = some (.tcb xt) := by simp [σ1, hte, hkt]
  have hks1 : σ1.kheap sd'.bv = some (.tcb xs) := by simp [σ1, hse, hks]
  have hbw : L.mem s1 (tBadgeA sd') = L.mem s (tBadgeA sd') := hA1 _ (a_badge hsa).1 ⟨sd', hsT, (a_badge hsa).2⟩
  have hfw : L.mem s1 (tFlagsA sd') = L.mem s (tFlagsA sd') := hA1 _ (a_flags hsa).1 ⟨sd', hsT, (a_flags hsa).2⟩
  step as ⟨bdg, hbdg⟩
  step as ⟨fl, hfl⟩
  step as ⟨i, hi, hi'⟩
  step as ⟨i1, hi1, hi1'⟩
  step as ⟨i2, hi2, hi2'⟩
  have hg : (i != 0#u64) = dd.senderCanGrant := by
    rw [← flags_grant dd, ← hflags, ← hfw, ← hfl]
    congr 1
    exact UScalar.eq_of_val_eq hi
  have hc : (i2 != 0#u64) = false := by
    rw [← hcall _ _ hstd, ← flags_call dd, ← hflags, ← hfw, ← hfl]
    congr 1
    exact UScalar.eq_of_val_eq hi2
  have hbb : bdg.bv = dd.senderBadge := by rw [hbdg, hbw]; exact hbadge
  have hcaps' := hcaps _ _ hstd
  rw [← hg] at hcaps'
  refine WP.spec_bind (hX.xbuf hP s1 a σ1 hR1 hS1 hsT ht (Ne.symm hts) hks1 hkt1 hfs hrb e bdg
    (i != 0#u64) hcaps') ?_
  rintro s2 ⟨σ2, e2, hR2, hS2, hA2, hk2o, x2, hkt2, -⟩
  have e2' : Fl4Spec.doIpcTransfer (Z := Unit) sd'.bv (some e.bv) dd.senderBadge dd.senderCanGrant t.bv σ1 =
      ({((), σ2)}, False) := by rw [← hbb, ← hg]; exact e2
  have hst' : sd'.bv ≠ t.bv := bv_inj (Ne.symm hts)
  have hks2 : σ2.kheap sd'.bv = some (.tcb xs) := (hk2o _ hst').trans hks1
  have hk2e : σ2.kheap e.bv = some (.endpoint (epDeq (.sendEP (sd'.bv :: q)) sd'.bv)) :=
    (hk2o _ hte.symm).trans (by simp [σ1])
  refine WP.spec_bind (hTl.sporadicAssert s2 σ2 sd' hR2 hS2 hsT) ?_
  rintro s3 ⟨σ3, hA, hf3, hv3, hS3⟩
  have hR3 := hR2.frame hP hf3 hv3
  obtain ⟨xs3, hks3, hs3st, -, -, hs3f, -⟩ := hv3.2.2.1 _ _ hks2
  have hk3e := hv3.1 _ _ hk2e
  have hxs3 := hR3.at_tcb hsT hks3
  step as ⟨ft, hft⟩
  have hft0 : ft = fl4_abi.consts.fault.NullFault := by
    rw [hft, hxs3.fault0.2 (hs3f.trans hfs)]; unfold fl4_abi.consts.fault.NullFault; rfl
  simp only [hc, hft0, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  -- the sender is in no queue
  have hb3 : L.mem s3 (tBlockA sd') = e := by
    rw [hf3 _ (a_blk hsa).1 (Or.inr (Or.inr (Or.inl ⟨sd', hsT, Or.inl (a_blk hsa).2⟩)))]
    rw [hA2 _ (a_blk hsa).1 ⟨?_, ?_⟩, hA1 _ (a_blk hsa).1 ⟨sd', hsT, (a_blk hsa).2⟩, hsb]
    · rintro ⟨r', hr'⟩
      have := tcb_disj hP ht hsT hts.symm
      rw [val_blk hsa, regA_val hta (regIdx_lt r')] at hr'; have := regIdx_lt r'; omega
    · rintro ⟨wp, hw, he'⟩
      have := hP.bt wp hw sd' hsT
      have := congrArg UScalar.val he'
      rw [val_blk hsa] at this; omega
  have hq3 := dequeued_not_queued hR3 he hb3 hk3e (epDeq_not_mem _)
  refine WP.spec_bind (hX.sts hP s3 σ3 hR3 hS3 hsT hks3 hq3 (hX.ns_ep _ (by rw [hs3st, hstd]; simp [tsCode])) .running (by simp [tsCode])
    sched.TS_RUNNING (by unfold sched.TS_RUNNING; rfl)) ?_
  rintro s4 ⟨hR4, hS4⟩
  have hspec := receiveIpc_send_eq b rights blk hsr hkt hbn hk hks hse hstd (hcall _ _ hstd) e2' hA hks3
    (hs3f.trans hfs)
  rw [hspec]
  refine WP.spec_mono (hTl.switchTo s4 a _ sd' hR4 hS4 hsT) ?_
  rintro ⟨s5, a5⟩ ⟨ha5, hnf, σ', hm, hf, hv, hS'⟩
  exact ⟨ha5, hnf, σ', hm, hR4.frame hP hf hv, hS'⟩

end

end

end Fl4Proofs.P3.Endp
