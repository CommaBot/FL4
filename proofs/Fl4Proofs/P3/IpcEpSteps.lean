/-
P3 (DESIGN.md §9), IPC: **the endpoint step lemmas on the merged relation**
(EpStepsN.lean with `IpcSchedHyps` for `CombHyps`): every step of
`EpStepsBuf` for `SRN N T (SRS T SR)` (`IpcSchedHyps.steps`). The endpoint
writes and `schedule_tcb` go through `IpcSchedHyps.epHyps` and
`IpcSchedHyps.schedC`.
-/
import Fl4Proofs.P3.IpcEpBase
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Endp
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Ipc

noncomputable section

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st] {N T E R : Set U64}
  {B : Set (U64 × Fl4Spec.Word)} {SR : S → Fl4Spec.State Unit → Prop}

/-- `set_thread_state` to a state below 3, with the notification relation. -/
theorem set_thread_state_i (hH : IpcSchedHyps st ar N T E R B SR) (hP0 : IPlaced N T E R B) (hP : EPlaced T E R B) (s : S)
    (σ : Fl4Spec.State Unit) (hR : EpStateRel T E R B (L.mem s) σ) (hSR : SRN st N T (SRS st T SR) s σ) {t : U64} (ht : t ∈ T)
    {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x))
    (hq : ∀ e ∈ E, ∀ z, σ.kheap e.bv = some (.endpoint z) → t.bv ∉ z.epQueue) (hns : tsCode x.tcbState ≠ 6)
    (ts : Fl4Spec.ThreadState) (hts : tsCode ts < 3) (code : U64) (hcode : code.val = tsCode ts) :
    sched.set_thread_state st s t code ⦃ s' =>
      EpStateRel T E R B (L.mem s') (stsAct (updK σ t.bv (.tcb { x with tcbState := ts })) t.bv) ∧
      SRN st N T (SRS st T SR) s' (stsAct (updK σ t.bv (.tcb { x with tcbState := ts })) t.bv) ⦄ := by
  have hqn := not_member hSR.2 ht hk (tsCode_ne6 hns)
  have hta := hP.tcb t ht
  have ha := a_st hta
  have hag := agree_wr (L := L) (s := s) (v := code) ha.1
  have g : ∀ b, Aligned b → (b.val < t.val + 3328 ∨ t.val + 3368 ≤ b.val) →
      L.mem (L.wr s (tStA t) code) b = L.mem s b := fun b hb hv => hag b hb (by rw [val_st hta]; omega)
  have hx1 := hSR.2.at_tcb ht hk
  have hN1 : NtfnStateRel N T (L.mem (L.wr s (tStA t) code)) (updK σ t.bv (.tcb { x with tcbState := ts })) := by
    refine ntfn_upd_fields hP0.toC hSR.2 ht _ g hqn ⟨?_, ?_, ?_, ?_⟩
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
  refine WP.spec_mono ((hH.schedC hP0 _ _ t hR1 ((hH.epHyps hP0).stable _ _ _ _ hSR.1 hW1 hS1) ht)) ?_
  rintro s2 ⟨hf, hfN, hS⟩
  exact ⟨hR1.frame hP hf (KView.stsAct' _ _), hS, hN1.frame hP0.n hfN (Notif.KView.stsAct _ _)⟩

/-- **`reply_unlink`**, with the notification relation. -/
theorem reply_unlink_i (hH : IpcSchedHyps st ar N T E R B SR) (hP0 : IPlaced N T E R B) (hP : EPlaced T E R B) (s : S)
    (σ : Fl4Spec.State Unit) (hR : EpStateRel T E R B (L.mem s) σ) (hSR : SRN st N T (SRS st T SR) s σ) {t : U64} (ht : t ∈ T)
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
      SRN st N T (SRS st T SR) s' (stsAct (updK (updK σ r.bv (.reply { xr with replyTcb := none })) t.bv
          (.tcb { x with tcbState := .inactive })) t.bv) ⦄ := by
  obtain ⟨e1, hR1, hS1, hA1⟩ := reply_write_rel (hH.epHyps hP0) hP s σ hR hSR.1 hr hkr 0#u64
  have hN1 := ntfn_reply_write hP0.toC hSR.2 hr hA1 hkr { xr with replyTcb := optRef 0#u64 }
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
  refine WP.spec_mono (set_thread_state_i hH hP0 hP _ _ hR1 ⟨hS1, hN1⟩ ht hk1 hq1 (by rw [hst]; simp [tsCode])
    .inactive (by simp [tsCode]) sched.TS_INACTIVE (by unfold sched.TS_INACTIVE; rfl)) ?_
  rintro s2 ⟨hR2, hS2⟩
  refine ⟨?_, hR2, hS2⟩
  unfold Fl4Spec.replyUnlinkTcb
  rw [nd_bind_one (getReply_eq hkr), nd_bind_one (assert_true hback σ), nd_bind_one (getThreadState_eq hk),
    nd_bind_one (assert_true (Or.inr ⟨e', dd, hst⟩) σ), nd_bind_one e1, setThreadState_eq _ hk1]

/-- The spec's state after `reply_push`'s link and block (no donation). -/
def pushSt (σ : Fl4Spec.State Unit) (t r : Fl4Spec.ObjRef) (xr : Fl4Spec.Reply) (xt : Fl4Spec.Tcb) :
    Fl4Spec.State Unit :=
  stsAct (updK (updK σ r (.reply { xr with replyTcb := some t })) t (.tcb { xt with tcbState := .blockedOnReply r })) t

/-- **`reply_push caller callee r don`**, with the notification relation:
the link and block, then, for a donating push, the donation (`hD`, over
`pushSt`); the post `P` holds at `pushSt` without a donation (`hP'`). -/
theorem reply_push_iG {don : Bool} (hH : IpcSchedHyps st ar N T E R B SR) (hP0 : IPlaced N T E R B) (hP : EPlaced T E R B)
    (s : S) (a : A)
    (σ : Fl4Spec.State Unit) (hR : EpStateRel T E R B (L.mem s) σ) (hSR : SRN st N T (SRS st T SR) s σ) {t d : U64} (ht : t ∈ T)
    {xt xd : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt)) (hkd : σ.kheap d.bv = some (.tcb xd))
    (hq : ∀ e ∈ E, ∀ z, σ.kheap e.bv = some (.endpoint z) → t.bv ∉ z.epQueue) (hns : tsCode xt.tcbState ≠ 6)
    {r : U64} (hr : r ∈ R) {xr : Fl4Spec.Reply} (hkr : σ.kheap r.bv = some (.reply xr))
    (hdT : don = true → d ∈ T) {P : S → Fl4Spec.State Unit → Prop}
    (hP' : ∀ s', EpStateRel T E R B (L.mem s') (pushSt σ t.bv r.bv xr xt) →
      SRN st N T (SRS st T SR) s' (pushSt σ t.bv r.bv xr xt) → P s' (pushSt σ t.bv r.bv xr xt))
    (hD : don = true → ∀ s3, EpStateRel T E R B (L.mem s3) (pushSt σ t.bv r.bv xr xt) →
      SRN st N T (SRS st T SR) s3 (pushSt σ t.bv r.bv xr xt) → L.mem s (scA t) ≠ 0#u64 →
      L.mem s3 (scA d) = 0#u64 → xt.tcbSchedContext = some (L.mem s (scA t)).bv → xd.tcbSchedContext = none →
      (do
        let i2 ← obj.Sc.reply st (L.mem s (scA t)) s3
        let s3' ← if i2 != 0#u64 then obj.Reply.set_next st i2 s3 r false else ok s3
        let s4 ← obj.Reply.set_prev st r s3' i2
        let s5 ← obj.Sc.set_reply st (L.mem s (scA t)) s4 r
        let s6 ← obj.Reply.set_next st r s5 (L.mem s (scA t)) true
        schedcontext.donate st ar s6 a (L.mem s (scA t)) d) ⦃ res => res.2 = a ∧ ∃ σ',
          (do
            Fl4Spec.bindScReply (Z := Unit) (L.mem s (scA t)).bv r.bv
            Fl4Spec.schedContextDonate (Z := Unit) (L.mem s (scA t)).bv d.bv) (pushSt σ t.bv r.bv xr xt) =
            ({((), σ')}, False) ∧ P res.1 σ' ⦄) :
    ipc.reply_push st ar s a t d r don ⦃ res => res.2 = a ∧ ∃ σ',
      Fl4Spec.replyPush (Z := Unit) t.bv d.bv r.bv don σ = ({((), σ')}, False) ∧ P res.1 σ' ⦄ := by
  have hE := hH.epHyps hP0
  have hta := hP.tcb t ht
  obtain ⟨e1, hR1, hS1, hA1⟩ := reply_link_rel hE hP s σ hR hSR.1 hr hkr hta
  set σ1 := updK σ r.bv (.reply { xr with replyTcb := some t.bv })
  have hN1 : NtfnStateRel N T (L.mem (L.wr s (rTcbA r) t)) σ1 := ntfn_reply_write hP0.toC hSR.2 hr hA1 hkr _
  have hrt : r.bv ≠ t.bv := kheap_ne hkr hkt (fun _ h1 h2 => by subst h1; cases h2)
  have hkt1 : σ1.kheap t.bv = some (.tcb xt) := by simp [σ1, Ne.symm hrt, hkt]
  have hxt1 := hR1.at_tcb ht hkt1
  have hq1 : ∀ e ∈ E, ∀ z, σ1.kheap e.bv = some (.endpoint z) → t.bv ∉ z.epQueue := by
    intro e he z hz
    have hre : r.bv ≠ e.bv := by intro h; rw [← h] at hz; simp [σ1] at hz
    exact hq e he z (by simpa [σ1, Ne.symm hre] using hz)
  have hqn := not_member hN1 ht hkt1 (tsCode_ne6 hns)
  have hspec : Fl4Spec.replyPush (Z := Unit) t.bv d.bv r.bv don σ =
      Fl4Spec.NonDet.when (xt.tcbSchedContext ≠ none ∧ xd.tcbSchedContext = none ∧ don = true) (do
        Fl4Spec.bindScReply (Z := Unit) (Fl4Spec.the xt.tcbSchedContext) r.bv
        Fl4Spec.schedContextDonate (Z := Unit) (Fl4Spec.the xt.tcbSchedContext) d.bv) (pushSt σ t.bv r.bv xr xt) := by
    unfold Fl4Spec.replyPush
    rw [nd_bind_one (getTcbObjRef_eq _ hkt), nd_bind_one (getTcbObjRef_eq _ hkd), nd_bind_one e1,
      nd_bind_one (setThreadState_eq _ hkt1)]
    rfl
  -- the callee's SC in `pushSt`
  have hkdP : ∀ x, (pushSt σ t.bv r.bv xr xt).kheap d.bv = some (.tcb x) → x.tcbSchedContext = xd.tcbSchedContext := by
    intro x hx
    unfold pushSt at hx; rw [stsAct_kheap] at hx
    by_cases e : d.bv = t.bv
    · rw [e] at hx hkd; rw [hkt] at hkd; cases hkd; simp at hx; rw [← hx]
    · have hdr : d.bv ≠ r.bv := kheap_ne hkd hkr (fun _ h1 h2 => by subst h1; cases h2)
      simp [e, hdr, hkd] at hx; rw [hx]
  have hsct : xt.tcbSchedContext = optRef (L.mem s (scA t)) := by
    obtain ⟨x, hx, hxs⟩ := hSR.1.2 t ht; rw [hkt] at hx; cases hx; exact hxs
  -- without a donation
  have nod : ∀ s3, EpStateRel T E R B (L.mem s3) (pushSt σ t.bv r.bv xr xt) →
      SRN st N T (SRS st T SR) s3 (pushSt σ t.bv r.bv xr xt) →
      ¬ (xt.tcbSchedContext ≠ none ∧ xd.tcbSchedContext = none ∧ don = true) →
      ∃ σ', Fl4Spec.replyPush (Z := Unit) t.bv d.bv r.bv don σ = ({((), σ')}, False) ∧
        P s3 σ' := fun s3 h1 h2 hc =>
    ⟨_, by rw [hspec, nd_when_false hc]; rfl, hP' s3 h1 h2⟩
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
    refine ntfn_upd_fields hP0.toC hN1 ht x1 g hqn ⟨?_, ?_, ?_, ?_⟩
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
  have hSR2 := hE.stable _ _ _ _ hS1 hW2 hS2
  unfold ipc.reply_push
  step as ⟨i, hi⟩
  step as ⟨s1', hs1'⟩
  subst hs1'
  unfold sched.set_blocked_on_reply
  step as ⟨s2a, hs2a⟩
  step as ⟨s2b, hs2b⟩
  subst hs2a hs2b
  refine WP.spec_bind (hH.schedC hP0 _ _ t hR2 hSR2 ht) ?_
  rintro s3 ⟨hf3, hfN3, hS3⟩
  have hR3 := hR2.frame hP hf3 (KView.stsAct' _ t.bv)
  have hN3 := hN2.frame hP0.n hfN3 (Notif.KView.stsAct _ t.bv)
  have hS3' : SRN st N T (SRS st T SR) s3 (pushSt σ t.bv r.bv xr xt) := ⟨hS3, hN3⟩
  subst hi
  unfold obj.Sc.is_null
  apply ok_bind_spec
  split
  · rename_i h0
    simp only [WP.spec_ok]
    refine ⟨by simp, nod s3 hR3 hS3' fun hc => hc.1 ?_⟩
    rw [hsct, of_decide_eq_true h0, optRef_zero]
  · rename_i h0
    have h0' : L.mem s (scA t) ≠ 0#u64 := fun e => h0 (by simp [e])
    step as ⟨i1, hi1⟩
    subst hi1
    split
    · rename_i hd0
      cases don with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
        exact ⟨by simp, nod s3 hR3 hS3' fun hc => by cases hc.2.2⟩
      | true =>
        simp only [↓reduceIte]
        have hxd0 : xd.tcbSchedContext = none := by
          obtain ⟨x, hx, hxs⟩ := hS3.2 d (hdT rfl)
          rw [← hkdP x hx, hxs, hd0, optRef_zero]
        have hxt0 : xt.tcbSchedContext = some (L.mem s (scA t)).bv := by rw [hsct, Notif.optRef_ne h0']
        refine WP.spec_mono (hD rfl s3 hR3 hS3' h0' hd0 hxt0 hxd0) ?_
        rintro res ⟨ha, σ', hm, hPs⟩
        refine ⟨ha, σ', ?_, hPs⟩
        have hc : (some (L.mem s (scA t)).bv ≠ none ∧ xd.tcbSchedContext = none ∧ true = true) := by simp [hxd0]
        rw [hspec, hxt0]
        simp only [Fl4Spec.NonDet.when, hc, ↓reduceIte, Fl4Spec.the]
        exact hm
    · rename_i hd0
      simp only [WP.spec_ok]
      refine ⟨by simp, nod s3 hR3 hS3' fun hc => hd0 ?_⟩
      obtain ⟨-, h2, h3⟩ := hc
      obtain ⟨x, hx, hxs⟩ := hS3.2 d (hdT h3)
      rw [hkdP x hx, h2] at hxs
      by_contra hc
      rw [Notif.optRef_ne hc] at hxs; cases hxs

/-- **`reply_push caller callee r false`**, with the notification relation. -/
theorem reply_push_i (hH : IpcSchedHyps st ar N T E R B SR) (hP0 : IPlaced N T E R B) (hP : EPlaced T E R B) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) (hR : EpStateRel T E R B (L.mem s) σ) (hSR : SRN st N T (SRS st T SR) s σ) {t d : U64} (ht : t ∈ T)
    {xt xd : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt)) (hkd : σ.kheap d.bv = some (.tcb xd))
    (hq : ∀ e ∈ E, ∀ z, σ.kheap e.bv = some (.endpoint z) → t.bv ∉ z.epQueue) (hns : tsCode xt.tcbState ≠ 6)
    {r : U64} (hr : r ∈ R) {xr : Fl4Spec.Reply} (hkr : σ.kheap r.bv = some (.reply xr)) :
    ipc.reply_push st ar s a t d r false ⦃ res => res.2 = a ∧
      Fl4Spec.replyPush (Z := Unit) t.bv d.bv r.bv false σ =
        ({((), stsAct (updK (updK σ r.bv (.reply { xr with replyTcb := some t.bv })) t.bv
          (.tcb { xt with tcbState := .blockedOnReply r.bv })) t.bv)}, False) ∧
      EpStateRel T E R B (L.mem res.1) (stsAct (updK (updK σ r.bv (.reply { xr with replyTcb := some t.bv })) t.bv
          (.tcb { xt with tcbState := .blockedOnReply r.bv })) t.bv) ∧
      SRN st N T (SRS st T SR) res.1 (stsAct (updK (updK σ r.bv (.reply { xr with replyTcb := some t.bv })) t.bv
          (.tcb { xt with tcbState := .blockedOnReply r.bv })) t.bv) ⦄ := by
  refine WP.spec_mono (reply_push_iG (don := false) (P := fun s' σ' => σ' = pushSt σ t.bv r.bv xr xt ∧
      EpStateRel T E R B (L.mem s') σ' ∧ SRN st N T (SRS st T SR) s' σ') hH hP0 hP s a σ hR hSR ht hkt hkd hq hns hr
    hkr (fun h => by cases h) (fun s' h1 h2 => ⟨rfl, h1, h2⟩) (fun h => by cases h)) ?_
  rintro res ⟨ha, σ', hm, rfl, h1, h2⟩
  exact ⟨ha, hm, h1, h2⟩

/-- **The step lemmas for the combined relation.** -/
theorem _root_.Fl4Proofs.P3.Ipc.IpcSchedHyps.steps (hH : IpcSchedHyps st ar N T E R B SR) (hBf : EpBufHyps st T E R B SR)
    (hBm : EpBufMapHyps st T E R B SR) (hP0 : IPlaced N T E R B) :
    EpStepsBuf st A ar T E R B (SRN st N T (SRS st T SR)) (fun ts => tsCode ts ≠ 6) False where
  ns_ep _ h := h
  deq hP s σ hR hSR e he x hk d hd := by
    obtain ⟨xs, hQ, hxs, hB⟩ := (hR.at_ep he hk).queue
    have hdx : d ∈ xs := by
      rw [hxs, List.mem_map] at hd
      obtain ⟨y, hy, ey⟩ := hd
      rw [← eq_of_bv ey]; exact hy
    refine WP.spec_mono (WP.spec_and (ep_dequeue_rel (hH.epHyps hP0) hP s σ hR hSR.1 he hk hd)
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
    exact ⟨h1, h2, ⟨h3, ntfn_frame_ep hP0.toC hSR.2 he hW hQA hkv⟩, h4⟩
  xregs hP s a σ hR hSR snd rcv hs hr hne xs xr hks hkr hf hrb ep badge grant hcaps :=
    WP.spec_mono (do_ipc_transfer_regs (ar := ar) (hH.epHyps hP0) hBf.srs hP s a σ hR hSR.1 hs hr hne hks hkr hf hrb ep badge
      grant (hcaps.resolve_left id)) fun _ ⟨h1, h2, h3, h4⟩ =>
      ⟨h1, h2, ⟨h3, ntfn_lift_rcv hP0.toC hSR.2 h2 hr (h4.mono fun _ h => h.1) (fun p hp => by simp [hp]) hkr
        (by simp only [updK_kheap, Function.update_self]; exact rfl) (xferTcb_state _ _ _)⟩, h4⟩
  xbuf hP s a σ hR hSR snd rcv hs hr hne xs xr hks hkr hf rp hrb ep badge grant hcaps :=
    WP.spec_mono (do_ipc_transfer_buf (ar := ar) (hH.epHyps hP0) hBf.srs hBm.srs hP s a σ hR hSR.1 hs hr hne hks hkr hf hrb ep
      badge grant (hcaps.resolve_left id)) fun _ ⟨σ', h1, h2, h3, h4, h5, x', h6, h7⟩ =>
      ⟨σ', h1, h2, ⟨h3, ntfn_lift_rcv hP0.toC hSR.2 h2 hr h4 h5 hkr h6 h7⟩, h4.mono fun _ h => h.2, KeepNC.of_eq h5, x', h6, h7⟩
  link hP s σ hR hSR r hr xr hkr t ht := by
    obtain ⟨e1, hR1, hS1, hA1⟩ := reply_link_rel (hH.epHyps hP0) hP s σ hR hSR.1 hr hkr ht
    exact ⟨e1, hR1, ⟨hS1, ntfn_reply_write hP0.toC hSR.2 hr hA1 hkr _⟩, hA1⟩
  unlink hP s σ hR hSR t ht x hk e' dd r hst hr xr hkr hback hq :=
    reply_unlink_i hH hP0 hP s σ hR hSR ht hk hst hr hkr hback hq
  sts hP s σ hR hSR t ht x hk hq hns ts hts code hcode :=
    set_thread_state_i hH hP0 hP s σ hR hSR ht hk hq hns ts hts code hcode
  push hP s a σ hR hSR t d ht xt xd hkt hkd hq hns r hr xr hkr :=
    reply_push_i (ar := ar) hH hP0 hP s a σ hR hSR ht hkt hkd hq hns hr hkr

end

end

end Fl4Proofs.P3.Endp
