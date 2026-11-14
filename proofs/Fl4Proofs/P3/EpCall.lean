/-
P3 (DESIGN.md §9), endpoints: **`reply_push` without donation refines l4v
`reply_push`** (`reply_push_rel`): the reply object is linked to the caller
(`reply_tcb`), the caller becomes `BlockedOnReply r` (state and reply words,
`schedule_tcb`); with `can_donate = false` neither side donates the
caller's scheduling context (SC donation is out of scope).
-/
import Fl4Proofs.P3.EpRecvSend
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Endp
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section Spec
open Fl4Spec

/-- The spec's `send_ipc` (call, no donation) to a waiting receiver `d` with
a reply object `r`, given the outcomes of its steps. -/
theorem sendIpc_call_eq {σ : State Unit} {t e d : ObjRef} {q : List ObjRef}
    (hk : σ.kheap e = some (.endpoint (.recvEP (d :: q)))) {xd : Tcb} (hkd : σ.kheap d = some (.tcb xd))
    (hde : d ≠ e) {e' r : ObjRef} {dd : ReceiverPayload}
    (hst : xd.tcbState = .blockedOnReceive e' (some r) dd) (blk : Bool) (badge : Badge) (g gr : Bool)
    (hg : g = true ∨ gr = true) {σ2 σ3 σ4 : State Unit}
    (hT : doIpcTransfer (Z := Unit) t (some e) badge g d (updK σ e (.endpoint (epDeq (.recvEP (d :: q)) d))) =
      ({((), σ2)}, False))
    (hU : NonDet.maybeM (replyUnlinkTcb (Z := Unit) d) (some r) σ2 = ({((), σ3)}, False))
    {xt3 x3 : Tcb} (hkt3 : σ3.kheap t = some (.tcb xt3)) (hkd3 : σ3.kheap d = some (.tcb x3))
    (hPush : replyPush (Z := Unit) t d r false σ3 = ({((), σ4)}, False)) {x4 : Tcb}
    (hkd4 : σ4.kheap d = some (.tcb x4)) :
    sendIpc (Z := Unit) blk true badge g gr false t e σ =
      specWakeTailE d (stsAct (updK σ4 d (.tcb { x4 with tcbState := .running })) d) := by
  have hkd1 : (updK σ e (.endpoint (epDeq (.recvEP (d :: q)) d))).kheap d = some (.tcb xd) := by
    simp [hde, hkd]
  unfold sendIpc
  rw [nd_bind_one (getEndpoint_eq hk)]
  cases blk <;> dsimp only <;>
  · rw [nd_bind_one (tcbEpDequeue_eq hk (by simp [Endpoint.epQueue])), nd_bind_one (getThreadState_eq hkd1), hst]
    dsimp only
    rw [nd_pure_bind', nd_bind_one hT, nd_bind_one hU, nd_bind_one (getTcbObjRef_eq _ hkd3),
      nd_bind_one (threadGet_eq _ hkt3)]
    have hg' : (g = true ∨ gr = true) ∧ (some r : Option ObjRef) ≠ none := ⟨hg, by simp⟩
    simp only [true_or, ↓reduceIte, hg', the]
    rw [if_pos ⟨trivial, by simp⟩]
    rw [nd_bind_one hPush, nd_bind_one (setThreadState_eq _ hkd4)]
    rfl

end Spec

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st] {T E R : Set U64}
  {B : Set (U64 × Fl4Spec.Word)} {SR : S → Fl4Spec.State Unit → Prop}

/-- The two writes of `set_blocked_on_reply`. -/
theorem block_reply_writes (hP : EPlaced T E R B) (s : S) {t : U64} (ht : t ∈ T) (r : U64) :
    let s2 := L.wr (L.wr s (tStA t) sched.TS_BLOCKED_ON_REPLY) (tReplyA t) r
    Agree (L.mem s) (L.mem s2) (fun b => b.val ≠ t.val + 3328 ∧ b.val ≠ t.val + 3360) ∧
      L.mem s2 (tStA t) = sched.TS_BLOCKED_ON_REPLY ∧ L.mem s2 (tReplyA t) = r ∧
      WritesIn st s s2 (EWrite T E R B) := by
  intro s2
  have hta := hP.tcb t ht
  have a1 := (a_st hta).1; have a3 := (a_reply hta).1
  have v1 := val_st hta; have v3 := val_reply hta
  have g1 := agree_wr2 (L := L) (s := s) (v := sched.TS_BLOCKED_ON_REPLY) (w := r) a1 a3
  refine ⟨g1.mono fun b hb => ?_, ?_, ?_, ?_⟩
  · rw [v1, v3]; omega
  · show L.mem (L.wr (L.wr s _ _) _ _) _ = _
    rw [L.mem_wr_ne a3 a1 (by omega), L.mem_wr_same a1]
  · exact L.mem_wr_same a3
  · refine ((wr_ewrite (E := E) (R := R) (B := B) ht (twf_of 3328 v1 (by unfold TWOffN; omega)) a1 s _).trans
      (wr_ewrite (E := E) (R := R) (B := B) ht (twf_of 3360 v3 (by unfold TWOffN; omega)) a3 _ _)).mono
      fun b hb => ?_
    rcases hb with hb | hb <;> exact hb

/-- **`reply_push caller callee r false`**. -/
theorem reply_push_rel (hH : EpHyps st T E R B SR) (hP : EPlaced T E R B) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) (hR : EpStateRel T E R B (L.mem s) σ) (hSR : SR s σ) {t d : U64} (ht : t ∈ T)
    {xt xd : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt)) (hkd : σ.kheap d.bv = some (.tcb xd))
    (hq : ∀ e ∈ E, ∀ z, σ.kheap e.bv = some (.endpoint z) → t.bv ∉ z.epQueue)
    {r : U64} (hr : r ∈ R) {xr : Fl4Spec.Reply} (hkr : σ.kheap r.bv = some (.reply xr)) :
    ipc.reply_push st ar s a t d r false ⦃ res => res.2 = a ∧
      Fl4Spec.replyPush (Z := Unit) t.bv d.bv r.bv false σ =
        ({((), stsAct (updK (updK σ r.bv (.reply { xr with replyTcb := some t.bv })) t.bv
          (.tcb { xt with tcbState := .blockedOnReply r.bv })) t.bv)}, False) ∧
      EpStateRel T E R B (L.mem res.1) (stsAct (updK (updK σ r.bv (.reply { xr with replyTcb := some t.bv })) t.bv
          (.tcb { xt with tcbState := .blockedOnReply r.bv })) t.bv) ∧
      SR res.1 (stsAct (updK (updK σ r.bv (.reply { xr with replyTcb := some t.bv })) t.bv
          (.tcb { xt with tcbState := .blockedOnReply r.bv })) t.bv) ⦄ := by
  have hta := hP.tcb t ht
  obtain ⟨e1, hR1, hS1, hA1⟩ := reply_link_rel hH hP s σ hR hSR hr hkr hta
  set σ1 := updK σ r.bv (.reply { xr with replyTcb := some t.bv })
  have hrt : r.bv ≠ t.bv := kheap_ne hkr hkt (fun _ h1 h2 => by subst h1; cases h2)
  have hkt1 : σ1.kheap t.bv = some (.tcb xt) := by simp [σ1, Ne.symm hrt, hkt]
  have hxt1 := hR1.at_tcb ht hkt1
  have hq1 : ∀ e ∈ E, ∀ z, σ1.kheap e.bv = some (.endpoint z) → t.bv ∉ z.epQueue := by
    intro e he z hz
    have hre : r.bv ≠ e.bv := by intro h; rw [← h] at hz; simp [σ1] at hz
    exact hq e he z (by simpa [σ1, Ne.symm hre] using hz)
  -- the spec
  have hspec : Fl4Spec.replyPush (Z := Unit) t.bv d.bv r.bv false σ =
      ({((), stsAct (updK σ1 t.bv (.tcb { xt with tcbState := .blockedOnReply r.bv })) t.bv)}, False) := by
    unfold Fl4Spec.replyPush
    rw [nd_bind_one (getTcbObjRef_eq _ hkt), nd_bind_one (getTcbObjRef_eq _ hkd), nd_bind_one e1,
      nd_bind_one (setThreadState_eq _ hkt1)]
    rw [nd_when_false (by simp)]
    rfl
  -- FL4
  set x1 : Fl4Spec.Tcb := { xt with tcbState := .blockedOnReply r.bv }
  set s1 := L.wr s (rTcbA r) t
  set s2 := L.wr (L.wr s1 (tStA t) sched.TS_BLOCKED_ON_REPLY) (tReplyA t) r
  obtain ⟨hA2, r1, r2, hW2⟩ := block_reply_writes (L := L) hP s1 ht r
  have v1 := val_st hta; have v3 := val_reply hta
  have hR2 : EpStateRel T E R B (L.mem s2) (updK σ1 t.bv (.tcb x1)) := by
    refine hR1.upd_tcb hP ht x1 (hA2.mono fun b hb => ?_) (Or.inl hq1) ?_
    · have n1 : b.val ≠ (tStA t).val := fun h => hb.2 (TF.of_val (a_st hta).2 h)
      have n3 : b.val ≠ (tReplyA t).val := fun h => hb.2 (TF.of_val (a_reply hta).2 h)
      omega
    refine hxt1.restate hta (hA2.mono fun b hb => ?_) rfl rfl rfl rfl ?_ ?_ ?_ ?_ ?_
    · have := hb.2; omega
    · rw [r1]; unfold sched.TS_BLOCKED_ON_REPLY; rfl
    · intro e' h; simp [x1, Fl4Spec.epBlocked] at h
    · intro e' d'' h; simp [x1] at h
    · intro e' rr d'' h; simp [x1] at h
    · intro rr h
      simp only [x1, Fl4Spec.ThreadState.blockedOnReply.injEq] at h
      subst h; rw [r2]
  have hS2 : EpStep σ1 (updK σ1 t.bv (.tcb x1)) := EpStep.tcb hkt1 _ xt.tcbArch
  have hSR2 := hH.stable _ _ _ _ hS1 hW2 hS2
  unfold ipc.reply_push
  step as ⟨i, hi⟩
  step as ⟨s1', hs1'⟩
  subst hs1'
  unfold sched.set_blocked_on_reply
  step as ⟨s2a, hs2a⟩
  step as ⟨s2b, hs2b⟩
  subst hs2a hs2b
  refine WP.spec_bind (hH.scheduleTcb _ _ t hR2 hSR2 ht) ?_
  rintro s3 ⟨hf3, hS3⟩
  have hR3 := hR2.frame hP hf3 (KView.stsAct' _ t.bv)
  unfold obj.Sc.is_null
  apply ok_bind_spec
  split
  · simp only [WP.spec_ok]; exact ⟨by simp, hspec, hR3, hS3⟩
  · step as ⟨i1, hi1⟩
    split
    · simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]; exact ⟨by simp, hspec, hR3, hS3⟩
    · simp only [WP.spec_ok]; exact ⟨by simp, hspec, hR3, hS3⟩

/-- **Call to a waiting receiver with a reply object** (no donation, sender
without a fault, grant or grant-reply right; receiver without IPC buffer, no
extra caps): the reply object moves from the receiver to the caller, which
becomes `BlockedOnReply`. -/
theorem send_ipc_call (hH : EpHyps st T E R B SR) (hBf : EpBufHyps st T E R B SR) (hTl : EpTailHyps st A T E R B SR)
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
  refine WP.spec_bind (ep_dequeue_rel hH hP s σ hR hSR he hk (d := d') (by simp [Fl4Spec.Endpoint.epQueue])) ?_
  rintro s1 ⟨e1, hR1, hS1, hA1⟩
  set σ1 := updK σ e.bv (.endpoint (epDeq (.recvEP (d'.bv :: q)) d'.bv))
  have hkt1 : σ1.kheap t.bv = some (.tcb xt) := by simp [σ1, hte, hkt]
  have hkd1 : σ1.kheap d'.bv = some (.tcb xd) := by simp [σ1, hde, hkd]
  -- the transfer
  refine WP.spec_bind (do_ipc_transfer_regs hH hBf hP s1 a σ1 hR1 hS1 ht hdT htd hkt1 hkd1 hft hrb e badge g hcaps) ?_
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
  refine WP.spec_bind (reply_unlink_rel hH hP s2 σ2 hR2 hS2 hdT hkd2 hst2' hwR hkr2 hb' hq2) ?_
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
  have hpush := reply_push_rel (ar := ar) hH hP s3 a σ3 hR3 hS3 ht hkt3 hkd3 hqt3 hwR hkr3
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
    refine WP.spec_bind (set_thread_state_rel hH hP s4 σ4 hR4 hS4 hdT hkd4 hq4 .running (by simp [tsCode])
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
      refine WP.spec_bind (set_thread_state_rel hH hP s4 σ4 hR4 hS4 hdT hkd4 hq4 .running (by simp [tsCode])
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
      refine WP.spec_bind (set_thread_state_rel hH hP s4 σ4 hR4 hS4 hdT hkd4 hq4 .running (by simp [tsCode])
        sched.TS_RUNNING (by unfold sched.TS_RUNNING; rfl)) ?_
      rintro s5 ⟨hR5, hS5⟩
      have hspec := sendIpc_call_eq hk hkd hde (by rw [hstd]) blk badge.bv _ _ hg' e2 e3 hkt3 hkd3 hP4 hkd4
        (t := t.bv)
      rw [hspec]
      refine WP.spec_mono (hTl.wakeTail s5 _ _ d' hR5 hS5 hdT) ?_
      rintro ⟨s7, a7⟩ ⟨ha7, hnf, σ', hm, hf, hv, hS'⟩
      exact ⟨ha7, hnf, σ', hm, hR5.frame hP hf hv, hS'⟩

end

end

end Fl4Proofs.P3.Endp
