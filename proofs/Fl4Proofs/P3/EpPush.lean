/-
P3 (DESIGN.md §9), endpoints: lemmas shared by the transfer theorems and the
bundled step lemmas (`EpStepsBase`): the thread state through a register
transfer, and `reply_push` (moved from EpSend / EpCall).
-/
import Fl4Proofs.P3.EpTail
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Endp
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

theorem copyRegsTcb_state (x : Fl4Spec.Tcb) (v : Fl4Spec.Register → Fl4Spec.Word) (rs : List Fl4Spec.Register) :
    (copyRegsTcb x v rs).tcbState = x.tcbState := by rw [copyRegsTcb_other]

theorem xferTcb_state (xr xs : Fl4Spec.Tcb) (b : Fl4Spec.Badge) : (xferTcb xr xs b).tcbState = xr.tcbState := by
  unfold xferTcb
  dsimp only
  rw [setReg_state, setReg_state, copyRegsTcb_state]

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

end

end

end Fl4Proofs.P3.Endp
