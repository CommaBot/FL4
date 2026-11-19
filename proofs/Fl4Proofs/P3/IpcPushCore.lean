/-
P3 (DESIGN.md §9), IPC: **`reply_push` on the endpoint relation from
`IpcCore`** (`reply_push_iC`): IpcEpSteps' `reply_push_iG`, which uses only
the endpoint steps and `schedule_tcb` of its hypotheses, so `IpcCore`
(IpcCancel's `ipcCore_top`, no named premise) gives it at every `IRel` state.
-/
import Fl4Proofs.P3.IpcEpSteps
import Fl4Proofs.P3.IpcCancel
open Aeneas Aeneas.Std Result

noncomputable section

namespace Fl4Proofs.P3.Endp
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Ipc

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st] {N T E R : Set U64}
  {B : Set (U64 × Fl4Spec.Word)} {SR : S → Fl4Spec.State Unit → Prop}

/-- **`reply_push caller callee r don`** (IpcEpSteps' `reply_push_iG` from `IpcCore`):
the link and block, then, for a donating push, the donation (`hD`, over
`pushSt`); the post `P` holds at `pushSt` without a donation (`hP'`). -/
theorem reply_push_iC {don : Bool} (hH : IpcCore st N T E R B SR) (hP0 : IPlaced N T E R B) (hP : EPlaced T E R B)
    (s : S) (a : A)
    (σ : Fl4Spec.State Unit) (hR : EpStateRel T E R B (L.mem s) σ) (hSR : SRN st N T (SRS st T SR) s σ) {t d : U64} (ht : t ∈ T)
    {xt xd : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt)) (hkd : σ.kheap d.bv = some (.tcb xd))
    (hq : ∀ e ∈ E, ∀ z, σ.kheap e.bv = some (.endpoint z) → t.bv ∉ z.epQueue) (hns : tsCode xt.tcbState ≠ 6)
    {r : U64} (hr : r ∈ R) {xr : Fl4Spec.Reply} (hkr : σ.kheap r.bv = some (.reply xr))
    (hdT : don = true → d ∈ T) {P : S → Fl4Spec.State Unit → Prop}
    (hP' : ∀ s', EpStateRel T E R B (L.mem s') (pushSt σ t.bv r.bv xr xt) →
      SRN st N T (SRS st T SR) s' (pushSt σ t.bv r.bv xr xt) → P s' (pushSt σ t.bv r.bv xr xt))
    (hD : don = true → ∀ s3, sched.set_blocked_on_reply st (L.wr s (rTcbA r) t) t r = ok s3 →
      EpStateRel T E R B (L.mem s3) (pushSt σ t.bv r.bv xr xt) →
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
      nd_bind_one (Notif.setThreadState_eq _ hkt1)]
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
  step with Fl4Proofs.P1.obj.Tcb.sc.spec as ⟨i, hi⟩
  step with Fl4Proofs.P3.Endp.obj.Reply.set_tcb.spec as ⟨s1', hs1'⟩
  subst hs1'
  have hblkS : sched.set_blocked_on_reply st s1 t r ⦃ s3 => FootEq T E R B (L.mem s2) (L.mem s3) ∧
      Notif.FootEq N T (L.mem s2) (L.mem s3) ∧ SRS st T SR s3 (stsAct (updK σ1 t.bv (.tcb x1)) t.bv) ⦄ := by
    unfold sched.set_blocked_on_reply
    step with Fl4Proofs.P3.Notif.obj.Tcb.set_state.spec as ⟨s2a, hs2a⟩
    step with Fl4Proofs.P3.Endp.obj.Tcb.set_reply_obj.spec as ⟨s2b, hs2b⟩
    subst hs2a hs2b
    exact hH.schedC hP0 _ _ t hR2 hSR2 ht
  obtain ⟨s3, hsb, hf3, hfN3, hS3⟩ : ∃ s3, sched.set_blocked_on_reply st s1 t r = ok s3 ∧
      FootEq T E R B (L.mem s2) (L.mem s3) ∧ Notif.FootEq N T (L.mem s2) (L.mem s3) ∧
      SRS st T SR s3 (stsAct (updK σ1 t.bv (.tcb x1)) t.bv) := by
    revert hblkS; cases sched.set_blocked_on_reply st s1 t r <;> simp [WP.spec_vis, WP.spec_div, WP.spec_ok]
  refine WP.spec_bind (show sched.set_blocked_on_reply st s1 t r ⦃ fun x => x = s3 ⦄ by
    rw [hsb]; exact (WP.spec_ok _).2 rfl) ?_
  intro x hx
  rw [hx]
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
    step with Fl4Proofs.P1.obj.Tcb.sc.spec as ⟨i1, hi1⟩
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
        refine WP.spec_mono (hD rfl s3 hsb hR3 hS3' h0' hd0 hxt0 hxd0) ?_
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

end

end Fl4Proofs.P3.Endp

end
