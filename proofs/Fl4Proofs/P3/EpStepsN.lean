/-
P3 (DESIGN.md §9), endpoints: **the step lemmas for the combined relation**
(`CombHyps.steps`): every step of `EpSteps` for `SRN N T SR`, i.e. with the
notification relation carried along. The threads whose state is set are not
`BlockedOnNotification` (so on no notification queue).
-/
import Fl4Proofs.P3.EpSteps
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Endp
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st] {N T E R : Set U64}
  {B : Set (U64 × Fl4Spec.Word)} {SR : S → Fl4Spec.State Unit → Prop}

theorem tsCode_ne6 {ts : Fl4Spec.ThreadState} (h : tsCode ts ≠ 6) : ∀ m, ts ≠ .blockedOnNotification m :=
  fun m e => h (by rw [e]; rfl)

/-- `set_thread_state` to a state below 3, with the notification relation. -/
theorem set_thread_state_n (hC : CombHyps st N T E R B SR) (hP' : CPlaced N T E R B) (hP : EPlaced T E R B) (s : S)
    (σ : Fl4Spec.State Unit) (hR : EpStateRel T E R B (L.mem s) σ) (hSR : SRN st N T SR s σ) {t : U64} (ht : t ∈ T)
    {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x))
    (hq : ∀ e ∈ E, ∀ z, σ.kheap e.bv = some (.endpoint z) → t.bv ∉ z.epQueue) (hns : tsCode x.tcbState ≠ 6)
    (ts : Fl4Spec.ThreadState) (hts : tsCode ts < 3) (code : U64) (hcode : code.val = tsCode ts) :
    sched.set_thread_state st s t code ⦃ s' =>
      EpStateRel T E R B (L.mem s') (stsAct (updK σ t.bv (.tcb { x with tcbState := ts })) t.bv) ∧
      SRN st N T SR s' (stsAct (updK σ t.bv (.tcb { x with tcbState := ts })) t.bv) ⦄ := by
  have hqn := not_member hSR.2 ht hk (tsCode_ne6 hns)
  have hta := hP.tcb t ht
  have ha := a_st hta
  have hag := agree_wr (L := L) (s := s) (v := code) ha.1
  have g : ∀ b, Aligned b → (b.val < t.val + 3328 ∨ t.val + 3368 ≤ b.val) →
      L.mem (L.wr s (tStA t) code) b = L.mem s b := fun b hb hv => hag b hb (by rw [val_st hta]; omega)
  have hx1 := hSR.2.at_tcb ht hk
  have hN1 : NtfnStateRel N T (L.mem (L.wr s (tStA t) code)) (updK σ t.bv (.tcb { x with tcbState := ts })) := by
    refine ntfn_upd_fields hP' hSR.2 ht _ g hqn ⟨?_, ?_, ?_, ?_⟩
    · rw [rd_wr_eq ha.1]; exact hcode
    · intro n h; simp only at h; rw [h] at hts; simp [tsCode] at hts
    · show (L.mem _ (badgeRegA t)).bv = badgeOf { x with tcbState := ts }
      rw [g _ (by rw [badgeRegA_eq_regA]; exact (a_reg hta _).1) (by
        rw [badgeRegA_eq, tw_val hta (by simp)]; left; simp)]
      exact hx1.badge
    · show (L.mem _ (prioA t)).val = _
      rw [g _ (a_prio hta).1 (by rw [val_prio hta]; omega)]
      exact hx1.prio
  unfold sched.set_thread_state
  step
  subst s1_post
  obtain ⟨hR1, hW1, hS1⟩ := write_state_rel hP s σ hR ht hk hq ts hts code hcode
  refine WP.spec_mono (hC.scheduleTcb _ _ t hR1 (hC.stable _ _ _ _ hSR.1 (hW1.mono fun _ h => Or.inr h)
    (Or.inr hS1)) ht) ?_
  rintro s2 ⟨hf, hfN, hS⟩
  exact ⟨hR1.frame hP hf (KView.stsAct' _ _), hS, hN1.frame hP'.n hfN (Notif.KView.stsAct _ _)⟩

/-- **`reply_unlink`**, with the notification relation. -/
theorem reply_unlink_n (hC : CombHyps st N T E R B SR) (hP' : CPlaced N T E R B) (hP : EPlaced T E R B) (s : S)
    (σ : Fl4Spec.State Unit) (hR : EpStateRel T E R B (L.mem s) σ) (hSR : SRN st N T SR s σ) {t : U64} (ht : t ∈ T)
    {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x)) {e' : Fl4Spec.ObjRef} {dd : Fl4Spec.ReceiverPayload}
    {r : U64} (hst : x.tcbState = .blockedOnReceive e' (some r.bv) dd) (hr : r ∈ R) {xr : Fl4Spec.Reply}
    (hkr : σ.kheap r.bv = some (.reply xr)) (hback : xr.replyTcb = some t.bv)
    (hq : ∀ e ∈ E, ∀ z, σ.kheap e.bv = some (.endpoint z) → t.bv ∉ z.epQueue) :
    ipc.reply_unlink st s r t ⦃ s' =>
      Fl4Spec.replyUnlinkTcb (Z := Unit) t.bv r.bv σ =
        ({((), stsAct (updK (updK σ r.bv (.reply { xr with replyTcb := none })) t.bv
          (.tcb { x with tcbState := .inactive })) t.bv)}, False) ∧
      EpStateRel T E R B (L.mem s') (stsAct (updK (updK σ r.bv (.reply { xr with replyTcb := none })) t.bv
          (.tcb { x with tcbState := .inactive })) t.bv) ∧
      SRN st N T SR s' (stsAct (updK (updK σ r.bv (.reply { xr with replyTcb := none })) t.bv
          (.tcb { x with tcbState := .inactive })) t.bv) ⦄ := by
  obtain ⟨e1, hR1, hS1, hA1⟩ := reply_write_rel hC.epHyps hP s σ hR hSR.1 hr hkr 0#u64
  have hN1 := ntfn_reply_write hP' hSR.2 hr hA1 hkr { xr with replyTcb := optRef 0#u64 }
  rw [optRef_zero] at e1 hR1 hS1 hN1
  have hrt : r.bv ≠ t.bv := kheap_ne hkr hk (fun _ h1 h2 => by subst h1; cases h2)
  have hk1 : (updK σ r.bv (.reply { xr with replyTcb := none })).kheap t.bv = some (.tcb x) := by
    simp [Ne.symm hrt, hk]
  have hq1 : ∀ e ∈ E, ∀ z, (updK σ r.bv (.reply { xr with replyTcb := none })).kheap e.bv = some (.endpoint z) →
      t.bv ∉ z.epQueue := by
    intro e he z hz
    have hre : r.bv ≠ e.bv := by
      intro h; rw [← h] at hz; simp at hz
    exact hq e he z (by simpa [Ne.symm hre] using hz)
  unfold ipc.reply_unlink
  step as ⟨s1, hs1⟩
  subst hs1
  refine WP.spec_mono (set_thread_state_n hC hP' hP _ _ hR1 ⟨hS1, hN1⟩ ht hk1 hq1 (by rw [hst]; simp [tsCode])
    .inactive (by simp [tsCode]) sched.TS_INACTIVE (by unfold sched.TS_INACTIVE; rfl)) ?_
  rintro s2 ⟨hR2, hS2⟩
  refine ⟨?_, hR2, hS2⟩
  unfold Fl4Spec.replyUnlinkTcb
  rw [nd_bind_one (getReply_eq hkr), nd_bind_one (assert_true hback σ), nd_bind_one (getThreadState_eq hk),
    nd_bind_one (assert_true (Or.inr ⟨e', dd, hst⟩) σ), nd_bind_one e1, setThreadState_eq _ hk1]

/-- **`reply_push caller callee r false`**, with the notification relation. -/
theorem reply_push_n (hC : CombHyps st N T E R B SR) (hP' : CPlaced N T E R B) (hP : EPlaced T E R B) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) (hR : EpStateRel T E R B (L.mem s) σ) (hSR : SRN st N T SR s σ) {t d : U64} (ht : t ∈ T)
    {xt xd : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt)) (hkd : σ.kheap d.bv = some (.tcb xd))
    (hq : ∀ e ∈ E, ∀ z, σ.kheap e.bv = some (.endpoint z) → t.bv ∉ z.epQueue) (hns : tsCode xt.tcbState ≠ 6)
    {r : U64} (hr : r ∈ R) {xr : Fl4Spec.Reply} (hkr : σ.kheap r.bv = some (.reply xr)) :
    ipc.reply_push st ar s a t d r false ⦃ res => res.2 = a ∧
      Fl4Spec.replyPush (Z := Unit) t.bv d.bv r.bv false σ =
        ({((), stsAct (updK (updK σ r.bv (.reply { xr with replyTcb := some t.bv })) t.bv
          (.tcb { xt with tcbState := .blockedOnReply r.bv })) t.bv)}, False) ∧
      EpStateRel T E R B (L.mem res.1) (stsAct (updK (updK σ r.bv (.reply { xr with replyTcb := some t.bv })) t.bv
          (.tcb { xt with tcbState := .blockedOnReply r.bv })) t.bv) ∧
      SRN st N T SR res.1 (stsAct (updK (updK σ r.bv (.reply { xr with replyTcb := some t.bv })) t.bv
          (.tcb { xt with tcbState := .blockedOnReply r.bv })) t.bv) ⦄ := by
  have hH := hC.epHyps
  have hta := hP.tcb t ht
  obtain ⟨e1, hR1, hS1, hA1⟩ := reply_link_rel hH hP s σ hR hSR.1 hr hkr hta
  set σ1 := updK σ r.bv (.reply { xr with replyTcb := some t.bv })
  have hN1 : NtfnStateRel N T (L.mem (L.wr s (rTcbA r) t)) σ1 := ntfn_reply_write hP' hSR.2 hr hA1 hkr _
  have hrt : r.bv ≠ t.bv := kheap_ne hkr hkt (fun _ h1 h2 => by subst h1; cases h2)
  have hkt1 : σ1.kheap t.bv = some (.tcb xt) := by simp [σ1, Ne.symm hrt, hkt]
  have hxt1 := hR1.at_tcb ht hkt1
  have hq1 : ∀ e ∈ E, ∀ z, σ1.kheap e.bv = some (.endpoint z) → t.bv ∉ z.epQueue := by
    intro e he z hz
    have hre : r.bv ≠ e.bv := by intro h; rw [← h] at hz; simp [σ1] at hz
    exact hq e he z (by simpa [σ1, Ne.symm hre] using hz)
  have hqn := not_member hN1 ht hkt1 (tsCode_ne6 hns)
  have hspec : Fl4Spec.replyPush (Z := Unit) t.bv d.bv r.bv false σ =
      ({((), stsAct (updK σ1 t.bv (.tcb { xt with tcbState := .blockedOnReply r.bv })) t.bv)}, False) := by
    unfold Fl4Spec.replyPush
    rw [nd_bind_one (getTcbObjRef_eq _ hkt), nd_bind_one (getTcbObjRef_eq _ hkd), nd_bind_one e1,
      nd_bind_one (setThreadState_eq _ hkt1)]
    rw [nd_when_false (by simp)]
    rfl
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
  have hN2 : NtfnStateRel N T (L.mem s2) (updK σ1 t.bv (.tcb x1)) := by
    have hx1 := hN1.at_tcb ht hkt1
    have g : ∀ b, Aligned b → (b.val < t.val + 3328 ∨ t.val + 3368 ≤ b.val) → L.mem s2 b = L.mem s1 b :=
      fun b hb hv => hA2 b hb (by omega)
    refine ntfn_upd_fields hP' hN1 ht x1 g hqn ⟨?_, ?_, ?_, ?_⟩
    · rw [r1]; unfold sched.TS_BLOCKED_ON_REPLY; rfl
    · intro n h; simp [x1] at h
    · show (L.mem s2 (badgeRegA t)).bv = badgeOf xt
      rw [g _ (by rw [badgeRegA_eq_regA]; exact (a_reg hta _).1) (by
        rw [badgeRegA_eq, tw_val hta (by simp)]; left; simp)]
      exact hx1.badge
    · show (L.mem s2 (prioA t)).val = xt.tcbPriority.toNat
      rw [g _ (a_prio hta).1 (by rw [val_prio hta]; omega)]
      exact hx1.prio
  have hS2 : EpStep σ1 (updK σ1 t.bv (.tcb x1)) := EpStep.tcb hkt1 _ xt.tcbArch
  have hSR2 := hC.stable _ _ _ _ hS1 (hW2.mono fun _ h => Or.inr h) (Or.inr hS2)
  unfold ipc.reply_push
  step as ⟨i, hi⟩
  step as ⟨s1', hs1'⟩
  subst hs1'
  unfold sched.set_blocked_on_reply
  step as ⟨s2a, hs2a⟩
  step as ⟨s2b, hs2b⟩
  subst hs2a hs2b
  refine WP.spec_bind (hC.scheduleTcb _ _ t hR2 hSR2 ht) ?_
  rintro s3 ⟨hf3, hfN3, hS3⟩
  have hR3 := hR2.frame hP hf3 (KView.stsAct' _ t.bv)
  have hN3 := hN2.frame hP'.n hfN3 (Notif.KView.stsAct _ t.bv)
  unfold obj.Sc.is_null
  apply ok_bind_spec
  split
  · simp only [WP.spec_ok]; exact ⟨by simp, hspec, hR3, hS3, hN3⟩
  · step as ⟨i1, hi1⟩
    split
    · simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]; exact ⟨by simp, hspec, hR3, hS3, hN3⟩
    · simp only [WP.spec_ok]; exact ⟨by simp, hspec, hR3, hS3, hN3⟩

/-- **The step lemmas for the combined relation.** -/
theorem CombHyps.steps (hC : CombHyps st N T E R B SR) (hBf : EpBufHyps st T E R B SR)
    (hBm : EpBufMapHyps st T E R B SR) (hP' : CPlaced N T E R B) :
    EpSteps st A ar T E R B (SRN st N T SR) (fun ts => tsCode ts ≠ 6) where
  ns_ep _ h := h
  deq hP s σ hR hSR e he x hk d hd := by
    obtain ⟨xs, hQ, hxs, hB⟩ := (hR.at_ep he hk).queue
    have hdx : d ∈ xs := by
      rw [hxs, List.mem_map] at hd
      obtain ⟨y, hy, ey⟩ := hd
      rw [← eq_of_bv ey]; exact hy
    refine WP.spec_mono (WP.spec_and (ep_dequeue_rel hC.epHyps hP s σ hR hSR.1 he hk hd)
      (ep_dequeue_full hP s he d xs hQ hdx)) ?_
    rintro s' ⟨⟨h1, h2, h3, h4⟩, -, -, hQA, -, -, -⟩
    have hkv : Notif.KView σ (updK σ e.bv (.endpoint (epDeq x d.bv))) := by
      refine ⟨fun p y h => ?_, fun p y h => ⟨y, ?_, rfl, rfl, rfl⟩⟩
      · have : p ≠ e.bv := by intro h'; rw [h', hk] at h; cases h
        simp [this, h]
      · have : p ≠ e.bv := by intro h'; rw [h', hk] at h; cases h
        simp [this, h]
    have hW : ∀ w ∈ xs, w ∈ T ∧ (L.mem s (tStA w)).val ≠ 6 := fun w hw =>
      ⟨hQ.mem w hw, by rcases (hB w hw).2 with h | h <;> rw [h] <;> simp⟩
    exact ⟨h1, h2, ⟨h3, ntfn_frame_ep hP' hSR.2 he hW hQA hkv⟩, h4⟩
  xregs hP s a σ hR hSR snd rcv hs hr hne xs xr hks hkr hf hrb ep badge grant hcaps :=
    WP.spec_mono (do_ipc_transfer_regs (ar := ar) hC.epHyps hBf hP s a σ hR hSR.1 hs hr hne hks hkr hf hrb ep badge
      grant hcaps) fun _ ⟨h1, h2, h3, h4⟩ =>
      ⟨h1, h2, ⟨h3, ntfn_lift_rcv hP' hSR.2 h2 hr (h4.mono fun _ h => h.1) (fun p hp => by simp [hp]) hkr
        (by simp only [updK_kheap, Function.update_self]; exact rfl) (xferTcb_state _ _ _)⟩, h4⟩
  xbuf hP s a σ hR hSR snd rcv hs hr hne xs xr hks hkr hf rp hrb ep badge grant hcaps :=
    WP.spec_mono (do_ipc_transfer_buf (ar := ar) hC.epHyps hBf hBm hP s a σ hR hSR.1 hs hr hne hks hkr hf hrb ep
      badge grant hcaps) fun _ ⟨σ', h1, h2, h3, h4, h5, x', h6, h7⟩ =>
      ⟨σ', h1, h2, ⟨h3, ntfn_lift_rcv hP' hSR.2 h2 hr h4 h5 hkr h6 h7⟩, h4, h5, x', h6, h7⟩
  link hP s σ hR hSR r hr xr hkr t ht := by
    obtain ⟨e1, hR1, hS1, hA1⟩ := reply_link_rel hC.epHyps hP s σ hR hSR.1 hr hkr ht
    exact ⟨e1, hR1, ⟨hS1, ntfn_reply_write hP' hSR.2 hr hA1 hkr _⟩, hA1⟩
  unlink hP s σ hR hSR t ht x hk e' dd r hst hr xr hkr hback hq :=
    reply_unlink_n hC hP' hP s σ hR hSR ht hk hst hr hkr hback hq
  sts hP s σ hR hSR t ht x hk hq hns ts hts code hcode :=
    set_thread_state_n hC hP' hP s σ hR hSR ht hk hq hns ts hts code hcode
  push hP s a σ hR hSR t d ht xt xd hkt hkd hq hns r hr xr hkr :=
    reply_push_n (ar := ar) hC hP' hP s a σ hR hSR ht hkt hkd hq hns hr hkr

end

end

end Fl4Proofs.P3.Endp
