/-
# P2 (2): `timer::insert` as `TCB_SetTimer`'s local path runs it

`insert_local`: arming `tg` (a thread disarmed or armed in the current core's tree) from a state with
the P1 invariant (`BlkOK`) writes only `InsW`: the current core's `REPROGRAM`, `TIMER_ROOT` and
`TIMER_MIN`, `tg`'s timer fields, and the timer links of the other threads armed in the current core's
tree. It is the intersection of P1's `TW` footprint (`timer.insert.foot`: only TCB timer fields and the
cores' root and min words, never the null page) and the per-key `TLX` footprints
(`timer.remove.tlx`, `timer.insert.tlx`). Besides, nothing becomes due: an earliest timer later than
`now` stays later than `now` when the new deadline is (`NoDueT`).

No named premises.
-/
import Fl4Proofs.P2.FootTimerTree
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat}

theorem WritesIn.inter {s s' : S} {A B : U64 → Prop} (h1 : WritesIn st s s' A) (h2 : WritesIn st s s' B) :
    WritesIn st s s' (fun b => A b ∧ B b) :=
  ⟨h1.1, h1.2.1, fun b hb hn => by
    by_cases ha : A b
    · exact h2.2.2 b hb fun hb' => hn ⟨ha, hb'⟩
    · exact h1.2.2 b hb ha⟩

/-- The words `insert_local` writes. -/
def InsW (st : machine.Store S) [L : LawfulStore st] (T : Set U64) (s0 : S) (tg w : U64) : Prop :=
  (∃ o : U64, (o.val = 56 ∨ o.val = 104 ∨ o.val = 112) ∧ w = L.nodeAt s0 (L.cpu s0) o) ∨
    (∃ K : U64, 3528 ≤ K.val ∧ K.val < 3576 ∧ w = core.num.U64.wrapping_add tg K) ∨
    (∃ y ∈ T, y ≠ tg ∧ FootLtArmed st s0 (L.cpu s0) y ∧
      ∃ K : U64, 3544 ≤ K.val ∧ K.val < 3576 ∧ w = core.num.U64.wrapping_add y K)

/-- No timer of the current core is due at `now`. -/
def NoDueT (st : machine.Store S) [L : LawfulStore st] (s : S) (now : U64) : Prop :=
  L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN) = 0#u64 ∨
    now < L.mem s (tdA (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN)))

/-- A TCB word and a link word of `0` or a TCB differ unless they are the same field of the same TCB. -/
theorem tz_word_eq {y z K K' : U64} (hT : TcbPlaced T) (hy : y ∈ T) (hz : Tz T z) (hK : K.val < 4096)
    (hK' : K'.val < 4096) (e : core.num.U64.wrapping_add y K = core.num.U64.wrapping_add z K') :
    z = y ∧ K = K' := by
  by_cases hk : K.val = K'.val
  · have eK : K = K' := UScalar.eq_of_val_eq hk
    subst eK
    exact ⟨(tz_inj hT (Tz.of_mem hy) hz hK (congrArg UScalar.val e)).symm, rfl⟩
  · exact absurd (congrArg UScalar.val e) (tz_ne hT (Tz.of_mem hy) hz hK hK' hk)

theorem tz_y_ne0 {y : U64} (hT : TcbPlaced T) (hy : y ∈ T) : y ≠ 0#u64 := fun e =>
  (hT y hy).ne0 (by rw [e]; rfl)

/-- An armed thread of the current core's tree is a key of it. -/
theorem armed_key {s : S} {c y : U64} (hR : TimerRB st T Cs s) (hy : y ∈ T) (ha : FootLtArmed st s c y) :
    ∃ W, CoreTree st T s c W ∧ y ∈ W.keys := by
  obtain ⟨c', hc', W, ct, hyW⟩ := hR.armed y hy ha.1
  have e : c' = c := UScalar.eq_of_val_eq ((ct.core y hyW).symm.trans ha.2)
  subst e
  exact ⟨W, ct, hyW⟩

set_option maxHeartbeats 4000000 in
/-- **`timer::insert` of a thread disarmed or armed in the current core's tree**: the invariant, the
words `InsW`, and nothing becomes due. -/
theorem insert_local {s3 s4 : S} {tg d bd : U64} (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s3) (htg : tg ∈ T)
    (hown : L.mem s3 (tdA tg) = 0#u64 ∨ (L.mem s3 (thA tg)).val >>> 8 = (L.cpu s3).val)
    (e : timer.insert st s3 tg d bd = ok s4) :
    BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s4 ∧ WritesIn st s3 s4 (InsW st T s3 tg) ∧
      ∀ now : U64, (d = 0#u64 ∨ now < d) → NoDueT st s3 now → NoDueT st s4 now := by
  have hT : TcbPlaced T := TInv.tcbs h
  have hN : ∀ c ∈ Cs, NodePlaced st T s3 c := TInv.nodes h
  have hcC : L.cpu s3 ∈ Cs := h.1.choose_spec.choose_spec.cur
  have hR : TimerRB st T Cs s3 := TInv.rb h
  have hNc := hN _ hcC
  have hF := timer.insert.foot s3 tg d bd h htg
  rw [e, WP.spec_ok] at hF
  obtain ⟨h4, -, wTW, -⟩ := hF
  have hrem := WP.spec_and (timer.remove.rb s3 tg hT htg hR hN) (timer.remove.tlx s3 tg hT htg hR hN)
  have hins := timer.insert.tlx s3 tg d bd hT htg hrem fun s1 hs1 => by
    obtain ⟨⟨hR1, htd1, hN1, -⟩, hr⟩ := hs1
    have ec : L.cpu s1 = L.cpu s3 := by
      rcases hr with ⟨-, rfl⟩ | ⟨c0, hc0, W0, ct0', htW0, w, k0⟩
      · rfl
      · exact w.2.1
    obtain ⟨t0, ct0⟩ := hR1.tree _ (ec ▸ hcC)
    exact ⟨hN1 _ (ec ▸ hcC), t0, ct0, fun hm => ct0.armed tg hm htd1⟩
  rw [e, WP.spec_ok] at hins
  -- the remove part: `s3 → s1`, words of `t`'s tree (the current core's) or nothing
  have remW : ∀ s1, ((L.mem s3 (tdA tg) = 0#u64 ∧ s1 = s3) ∨
      ∃ c ∈ Cs, ∃ W, CoreTree st T s3 c W ∧ tg ∈ W.keys ∧ WritesIn st s3 s1 (TLX st s3 c W.keys tg) ∧
        TKeepO st T s3 s1 tg) →
      WritesIn st s3 s1 (fun w => ∃ Ks : List U64, (∀ z ∈ Ks, z ∈ T ∧ FootLtArmed st s3 (L.cpu s3) z) ∧
        TLX st s3 (L.cpu s3) Ks tg w) ∧ TKeepO st T s3 s1 tg ∧ L.cpu s1 = L.cpu s3 := by
    intro s1 hr
    rcases hr with ⟨-, rfl⟩ | ⟨c, hc, W, ct, htW, w, k⟩
    · exact ⟨WritesIn.refl _ _, fun _ _ _ => ⟨rfl, rfl⟩, rfl⟩
    · have ec : c = L.cpu s3 := by
        have hd : L.mem s3 (tdA tg) ≠ 0#u64 := ct.armed tg htW
        exact UScalar.eq_of_val_eq ((ct.core tg htW).symm.trans (hown.resolve_left hd))
      subst ec
      exact ⟨w.mono fun b hb => ⟨W.keys, fun z hz => ⟨ct.inT z hz, ct.armed z hz, ct.core z hz⟩, hb⟩, k, w.2.1⟩
  -- the footprint as a union of `TLX` sets
  obtain ⟨wX, kX, htdX⟩ : WritesIn st s3 s4 (fun w => ∃ Ks : List U64,
      (∀ z ∈ Ks, z ∈ T ∧ FootLtArmed st s3 (L.cpu s3) z) ∧ TLX st s3 (L.cpu s3) Ks tg w) ∧
      TKeepO st T s3 s4 tg ∧ (d ≠ 0#u64 → L.mem s4 (tdA tg) = d) ∧ (d = 0#u64 → L.mem s4 (tdA tg) = 0#u64) := by
    rcases hins with ⟨hd0, ⟨-, htd1, -, -⟩, hr⟩ | ⟨hd0, s1, ctx, ⟨⟨hR1, htd1, hN1, -⟩, hr⟩, cto, w14, k14, htd4, -⟩
    · obtain ⟨w, k, -⟩ := remW s4 hr
      exact ⟨w, k, fun h => absurd hd0 h, fun _ => htd1⟩
    · obtain ⟨w1, k1, ec⟩ := remW s1 hr
      refine ⟨(w1.trans (w14.mono fun b hb => ?_)).mono fun b hb => hb.elim id id, k1.trans k14,
        fun _ => htd4, fun h => absurd h hd0⟩
      refine ⟨(ctx.plug .leaf).keys, fun z hz => ?_, by have h' := TLX.ksb w1.1 hb; rw [ec] at h'; exact h'⟩
      have hzT := cto.inT z hz
      have hne : z ≠ tg := fun ez => by
        subst ez; exact cto.armed _ hz htd1
      obtain ⟨a1, a2⟩ := k1 z hzT hne
      refine ⟨hzT, by rw [← a1]; exact cto.armed z hz, by rw [← a2, ← ec]; exact cto.core z hz⟩
  refine ⟨h4, ?_, ?_⟩
  · refine (WritesIn.inter wTW wX).mono fun w ⟨hw1, Ks, hKs, hw2⟩ => ?_
    have hKz : ∀ z, (z = 0#u64 ∨ z ∈ Ks) → Tz T z := fun z hz => hz.imp_right fun h => (hKs z h).1
    rcases hw1 with (⟨y, hy, K, hK1, hK2, rfl⟩ | ⟨c, hc, o, ho, rfl⟩) | rfl
    · -- a timer field of `y`
      rcases hw2 with ⟨z, hz, ez⟩ | ⟨K', h1, h2, ez⟩ | ⟨o, ho, ez⟩
      · have fz : ∀ K' : U64, K'.val < 4096 → 3544 ≤ K'.val → K'.val < 3576 →
            core.num.U64.wrapping_add y K = core.num.U64.wrapping_add z K' → InsW st T s3 tg
              (core.num.U64.wrapping_add y K) := by
          intro K' hK' a1 a2 ee
          obtain ⟨ezy, eK⟩ := tz_word_eq hT hy (hKz z hz) (by omega) hK' ee
          subst ezy eK
          rcases hz with hz | hz
          · exact absurd hz (tz_y_ne0 hT hy)
          · by_cases hyt : z = tg
            · subst hyt; exact Or.inr (Or.inl ⟨K, hK1, hK2, rfl⟩)
            · exact Or.inr (Or.inr ⟨z, hy, hyt, (hKs z hz).2, K, a1, a2, rfl⟩)
        rcases ez with ez | ez | ez | ez
        · exact fz 3544#u64 (by simp) (by simp) (by simp) ez
        · exact fz 3552#u64 (by simp) (by simp) (by simp) ez
        · exact fz 3560#u64 (by simp) (by simp) (by simp) ez
        · exact fz 3568#u64 (by simp) (by simp) (by simp) ez
      · obtain ⟨ezy, eK⟩ := tz_word_eq hT hy (Tz.of_mem htg) (by omega) (by omega) ez
        subst ezy eK
        exact Or.inr (Or.inl ⟨K, hK1, hK2, rfl⟩)
      · exact absurd (congrArg UScalar.val ez).symm (node_ne_tz hT hNc ho (Tz.of_mem hy) (by omega))
    · -- a root or min word of core `c`
      rcases hw2 with ⟨z, hz, ez⟩ | ⟨K', h1, h2, ez⟩ | ⟨o', ho', ez⟩
      · have hNc' := hN c hc
        rcases ez with ez | ez | ez | ez <;>
          exact absurd (congrArg UScalar.val ez) (node_ne_tz hT hNc' (by omega) (hKz z hz) (by simp))
      · exact absurd (congrArg UScalar.val ez) (node_ne_tz hT (hN c hc) (by omega) (Tz.of_mem htg) (by omega))
      · by_cases ecc : c = L.cpu s3
        · subst ecc; exact Or.inl ⟨o, by omega, rfl⟩
        · exact absurd (congrArg UScalar.val ez) (node_ne_node (hN c hc) hNc (by omega) ho' (fun h => absurd h ecc))
    · exact Or.inl ⟨layout.node.REPROGRAM, Or.inl (by simp [layout.node.REPROGRAM]), rfl⟩
  · -- nothing becomes due
    intro now hd hnd
    have hR4 : TimerRB st T Cs s4 := TInv.rb h4
    have ec4 : L.cpu s4 = L.cpu s3 := wTW.2.1
    obtain ⟨W4, ct4⟩ := hR4.tree _ (ec4 ▸ hcC)
    unfold NoDueT
    rw [ct4.min]
    rcases TRB.RBT.minKey_mem W4 with h0 | hm
    · exact Or.inl h0
    right
    have hmT := ct4.inT _ hm
    have harm4 := ct4.armed _ hm
    by_cases hmt : W4.minKey = tg
    · rw [hmt] at harm4 ⊢
      by_cases hd0 : d = 0#u64
      · exact absurd (htdX.2 hd0) harm4
      · rw [htdX.1 hd0]; exact hd.resolve_left hd0
    · obtain ⟨a1, a2⟩ := kX _ hmT hmt
      have harm3 : FootLtArmed st s3 (L.cpu s3) W4.minKey :=
        ⟨by rw [← a1]; exact harm4, by rw [← a2, ← ec4]; exact ct4.core _ hm⟩
      obtain ⟨W3, ct3, hm3⟩ := armed_key hR hmT harm3
      have hle := CoreTree.min_le ct3 hm3
      have hne0 : L.mem s3 (L.nodeAt s3 (L.cpu s3) layout.node.TIMER_MIN) ≠ 0#u64 := by
        rw [ct3.min]
        intro h0
        unfold TRB.RBT.minKey at h0
        cases hk : W3.keys with
        | nil => rw [hk] at hm3; simp at hm3
        | cons x xs =>
          rw [hk] at h0
          simp only [List.headD_cons] at h0
          exact tz_y_ne0 hT (ct3.inT x (by rw [hk]; simp)) h0
      have h3 := hnd.resolve_left hne0
      rw [a1]
      exact lt_of_lt_of_le h3 hle
end

end Fl4Proofs.P2
