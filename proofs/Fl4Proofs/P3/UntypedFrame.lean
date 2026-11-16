/-
P3: **retype's word-level write frames** (for P1's `RetypeP1Step`): the
object loop of the types whose objects need no initialisation writes only
slot words (`create_loop_frame`); the reset writes only its region, the
untyped cap's slot and the preemption point's words (`reset_frame`).
-/
import Fl4Proofs.P3.UntypedTcbLoop
import Fl4Proofs.P3.UntypedResetRetype
import Fl4Proofs.P3.UntypedPml4
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

/-- The words of a typed heap's slots. -/
def SlotW (th : TypedHeap) (w : U64) : Prop := ∃ a, IsSlot th a ∧ a.val ≤ w.val ∧ w.val < a.val + 32

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **`create_new_objects`' write frame** (types 0, 2..7, 9..13: no
object initialisation): `create_loop_rel` with only slot words of `th'`
written. -/
theorem create_loop_frame {A' : Type} (arI : machine.Arch A') (ar : A') (th' : TypedHeap) (hP' : Placed th')
    {pp : U64} {rs : Nat} (hpp : th' pp = some (.cnode rs))
    {idx : List Bool} (hidx : idx.length = rs) {p sb fi : U64} {d : Bool}
    (hsb : sb.val < 64) (hpfit : p.val + 2 ^ sb.val ≤ 2 ^ 64)
    (σ1 : Fl4Spec.State Unit) {dest : U64} {r : Nat} (hdest : th' dest = some (.cnode r)) (hr : r ≤ 64)
    (nt us : U64) (dev : Bool) (t : Fl4Spec.ApiObjectType) (ht : objTypeOf nt.val = some t)
    (hn : nt.val = 0 ∨ (2 ≤ nt.val ∧ nt.val ≤ 13 ∧ nt.val ≠ 8)) (hus : us.val < 64) (hz : zOf nt.val us.val < 64)
    (hsc : nt.val = 5 → 7 ≤ us.val)
    (off win base : U64) (hwin : off.val + win.val ≤ 2 ^ r)
    (hfit : base.val + win.val * 2 ^ zOf nt.val us.val ≤ 2 ^ 64) (hhigh : 2 ^ 64 - 2 ^ 47 ≤ base.val)
    (hpA : p.val ≤ base.val) (hAp : base.val + win.val * 2 ^ zOf nt.val us.val ≤ p.val + 2 ^ sb.val)
    (hnewcv : ∀ i, i < win.val →
      CapValid th' (newCapOf nt.val ⟨BitVec.ofNat 64 (base.val + i * 2 ^ zOf nt.val us.val)⟩ us dev))
    (zlo zhi : Nat) (hzs : ∀ a, IsSlot th' a → a.val + 32 ≤ zlo ∨ zhi ≤ a.val)
    (G0 : MdbGhost) (m0 : U64 → U64)
    (hsrcd : ∀ j, j < win.val → cslotAddr (pp.bv, idx) ≠ slotAddr dest.bv (BitVec.ofNat 64 (off.val + j)))
    (s : S)
    (hinv : LoopInv (L := L) th' (pp.bv, idx) (.Untyped p sb fi d) σ1
      (Fl4Spec.createCap (Z := Unit) t us.val (pp.bv, idx) dev)
      ((windowSlots dest r off.val win.val).zip (regionPtrs (BitVec.ofNat 64 base.val) win.val (2 ^ zOf nt.val us.val)))
      base.val (2 ^ zOf nt.val us.val) win.val (fun j => slotAddr dest.bv (BitVec.ofNat 64 (off.val + j))) zlo zhi G0 m0
      (cjOf nt.val us dev base.val (2 ^ zOf nt.val us.val)) s 0) :
    objects.create_new_objects st arI s ar nt (cslotAddr (pp.bv, idx)) dest off win base us dev ⦃ res =>
      res.2 = ar ∧ LoopInv (L := L) th' (pp.bv, idx) (.Untyped p sb fi d) σ1
      (Fl4Spec.createCap (Z := Unit) t us.val (pp.bv, idx) dev)
      ((windowSlots dest r off.val win.val).zip (regionPtrs (BitVec.ofNat 64 base.val) win.val (2 ^ zOf nt.val us.val)))
      base.val (2 ^ zOf nt.val us.val) win.val (fun j => slotAddr dest.bv (BitVec.ofNat 64 (off.val + j))) zlo zhi G0 m0
      (cjOf nt.val us dev base.val (2 ^ zOf nt.val us.val)) res.1
        win.val ∧ WFrame (L := L) s res.1 (SlotW th') ⦄ := by
  have hn14 : nt.val < 14 := by omega
  unfold objects.create_new_objects
  rw [object_size_eq nt us hn14 hus]
  simp only [bind_ok]
  unfold objects.create_new_objects_loop
  have hk1 : 1 ≤ 2 ^ zOf nt.val us.val := Nat.one_le_two_pow
  have h63 : ((⟨BitVec.ofNat 64 (zOf nt.val us.val)⟩ : U64) &&& 63#u64).val = zOf nt.val us.val := by
    have : ((⟨BitVec.ofNat 64 (zOf nt.val us.val)⟩ : U64) &&& 63#u64).val =
        (⟨BitVec.ofNat 64 (zOf nt.val us.val)⟩ : U64).val % 64 := by
      simp only [UScalar.val_and]; exact Nat.and_two_pow_sub_one_eq_mod _ 6
    rw [this]
    show (BitVec.ofNat 64 (zOf nt.val us.val)).toNat % 64 = _
    simp; omega
  refine loop.spec_decr_nat (measure := fun x => win.val - x.2.2.val)
    (inv := fun x => x.2.1 = ar ∧ x.2.2.val ≤ win.val ∧ LoopInv (L := L) th' (pp.bv, idx) (.Untyped p sb fi d) σ1
      (Fl4Spec.createCap (Z := Unit) t us.val (pp.bv, idx) dev)
      ((windowSlots dest r off.val win.val).zip (regionPtrs (BitVec.ofNat 64 base.val) win.val (2 ^ zOf nt.val us.val)))
      base.val (2 ^ zOf nt.val us.val) win.val (fun j => slotAddr dest.bv (BitVec.ofNat 64 (off.val + j))) zlo zhi G0 m0
      (cjOf nt.val us dev base.val (2 ^ zOf nt.val us.val)) x.1
        x.2.2.val ∧ WFrame (L := L) s x.1 (SlotW th')) _ _ _ ?_ ?_
  · rintro ⟨s1, a1, i⟩ ⟨ha, hiw, hI, hW⟩
    simp only at ha hiw hI hW ⊢
    subst ha
    unfold objects.create_new_objects_loop.body
    by_cases hit : i < win
    · rw [if_pos hit]
      have hit' : i.val < win.val := hit
      simp only [lift, bind_ok]
      have hik : (i.val + 1) * 2 ^ zOf nt.val us.val ≤ win.val * 2 ^ zOf nt.val us.val :=
        Nat.mul_le_mul_right _ hit'
      rw [Nat.add_mul, Nat.one_mul] at hik
      obtain ⟨i2, hi2, hv2, -⟩ := spec_exists (UScalar.ShiftLeft_spec i
        ((⟨BitVec.ofNat 64 (zOf nt.val us.val)⟩ : U64) &&& 63#u64) _
        (by rw [h63]; simp [UScalarTy.U64_numBits_eq]; omega) rfl)
      rw [hi2]; simp only [bind_ok]
      have hi2v : i2.val = i.val * 2 ^ zOf nt.val us.val := by
        rw [hv2, h63, Nat.shiftLeft_eq]
        simp [U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits]; omega
      have hi3 : core.num.U64.wrapping_add base i2 =
          ⟨BitVec.ofNat 64 (base.val + i.val * 2 ^ zOf nt.val us.val)⟩ := by
        apply u64_ofNat_eq
        simp [core.num.U64.wrapping_add_val_eq, U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits, hi2v]; omega
      rw [hi3, create_object_eq arI s1 a1 nt _ us dev (by omega)]
      simp only [bind_ok, uncurry_apply_pair]
      have hi4 : (core.num.U64.wrapping_add off i).bv = BitVec.ofNat 64 (off.val + i.val) := by
        rw [bv_eq_ofNat]; congr 1
        have : off.val + i.val < 2 ^ 64 := by
          have := Nat.pow_le_pow_right (show 0 < 2 by decide) hr; omega
        simp [core.num.U64.wrapping_add_val_eq, U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits]; omega
      rw [show obj.Slot.index dest (core.num.U64.wrapping_add off i) =
        ok (slotAddr dest.bv (BitVec.ofNat 64 (off.val + i.val))) by
          rw [spec_eq_ok (slot_index_spec dest _), hi4]]
      simp only [bind_ok]
      have hL := loop_step (L := L) th' hP' hpp hidx hsb hpfit σ1 hdest hr nt us dev t ht (by omega) hus hz hsc off.val
        win.val base.val hwin hfit hhigh hpA hAp hnewcv zlo zhi hzs G0 m0 hsrcd s1 i.val hit' hI
      obtain ⟨σi, Gi, -, -, -, hMi, -, -, hcsi, -⟩ := id hI
      have hAs : AbsSlot th' (pp.bv, idx) := ⟨pp, rfl, Or.inl (by simpa [hidx] using hpp)⟩
      have hss : IsSlot th' (cslotAddr (pp.bv, idx)) := hAs.isSlot
      have hsm : cslotAddr (pp.bv, idx) ∈ Gi.chains.flatten := (hMi.members _).2 ⟨hss, _, hcsi, by simp⟩
      have hds : IsSlot th' (slotAddr dest.bv (BitVec.ofNat 64 (off.val + i.val))) :=
        ⟨dest, off.val + i.val, Or.inl ⟨r, hdest, by omega⟩, rfl⟩
      have hnx : nextOf (L.mem s1) (cslotAddr (pp.bv, idx)) = 0#u64 ∨
          IsSlot th' (nextOf (L.mem s1) (cslotAddr (pp.bv, idx))) := by
        rcases hMi.next_mem hsm with h | ⟨h1, -⟩
        · exact Or.inl h
        · exact Or.inr ((hMi.members _).1 h1).1
      refine WP.spec_bind (WP.spec_and hL (WP.spec_and (insert_new_frame hP' s1 _ _ _ hss hds hnx)
        (insert_new_ksb s1 _ _ _))) fun s3 ⟨hs3, hfr, hk⟩ => ?_
      have hW3 : WFrame (L := L) s s3 (SlotW th') := hW.trans ⟨hk, fun w hw hnp => hfr w hw (fun a ha hin => by
        refine hnp ⟨a, ?_, hin.1, hin.2⟩
        rcases ha with e | e | ⟨h0, e⟩
        · rw [e]; exact hss
        · rw [e]; exact hds
        · rw [e]; exact hnx.resolve_left h0)⟩
      step as ⟨i5, hi5⟩
      refine ⟨by omega, by rw [hi5]; exact hs3, hW3, by omega⟩
    · rw [if_neg hit, WP.spec_ok]
      have : i.val = win.val := by have : ¬ i.val < win.val := hit; omega
      rw [this] at hI
      exact ⟨rfl, hI, hW⟩
  · exact ⟨rfl, by simp, hinv, WFrame.refl s _⟩

end

/-! ## The reset -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- The words a reset may write: its region, the untyped cap's two cap
words, and the preemption point's words `PW`. -/
def ResetW (p sb x : U64) (PW : U64 → Prop) (w : U64) : Prop :=
  (p.val ≤ w.val ∧ w.val < p.val + 2 ^ sb.val) ∨ (x.val ≤ w.val ∧ w.val < x.val + 16) ∨ PW w

theorem zr_frame (s : S) (a n : U64) (ha : P1.Aligned a) (hn : n.val % 8 = 0) (hf : a.val + n.val ≤ 2 ^ 64) :
    WFrame (L := L) s (L.zr s a n) (fun w => a.val ≤ w.val ∧ w.val < a.val + n.val) :=
  ⟨L.ksb_zr _ _ _, fun w hw hnp => by rw [L.mem_zr s a n w ha hn hf hw, if_neg hnp]⟩

theorem set_cap_frame (s : S) (x : U64) (c : capability.Cap) (hx : x.val % 8 = 0) (hxf : x.val + 16 ≤ 2 ^ 64) :
    obj.Slot.set_cap st x s c ⦃ s' => WFrame (L := L) s s' (fun w => x.val ≤ w.val ∧ w.val < x.val + 16) ⦄ := by
  apply WP.spec_mono (set_cap_spec x s c)
  rintro s' rfl
  have h8 : (core.num.U64.wrapping_add x 8#u64).val = x.val + 8 := by
    rw [core.num.U64.wrapping_add_val_eq]; simp [U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits]; omega
  exact (WFrame.wr s hx ⟨le_refl _, by omega⟩ _).trans
    (WFrame.wr _ (by unfold P1.Aligned; rw [h8]; omega) ⟨by rw [h8]; omega, by rw [h8]; omega⟩ _)

/-- **The reset's write frame**: `reset_untyped` on the slot `x` of an
untyped cap `Untyped p sb fi dev` writes only `ResetW p sb x PW`, given a
preemption point that writes only `PW` and keeps a property `Q` that the
zeroing and the slot's write keep. -/
theorem reset_frame {A' : Type} (arI : machine.Arch A') (s : S) (a : A') (x : U64) {p sb fi : U64} {dev : Bool}
    (hcap : capAt (L.mem s) x = ok (.Untyped p sb fi dev)) (hpal : p.val % 2 ^ sb.val = 0) (hsb4 : 4 ≤ sb.val)
    (hfit : p.val + 2 ^ sb.val ≤ 2 ^ 64) (hfib : fi.val ≤ 2 ^ sb.val)
    (hx : x.val % 8 = 0) (hxf : x.val + 16 ≤ 2 ^ 64)
    {Q : S → Prop} (hQk : EKept (L := L) Q p sb x) (hQ : Q s) {PW : U64 → Prop}
    (hPPF : ∀ (s1 : S) (a1 : A'), Q s1 → sched.preemption_point st arI s1 a1 ⦃ r => WFrame (L := L) s1 r.2.1 PW ∧ Q r.2.1 ⦄) :
    untyped.reset_untyped st arI s a x ⦃ res => WFrame (L := L) s res.2.1 (ResetW p sb x PW) ∧ Q res.2.1 ⦄ := by
  have hsb : sb.val < 64 := capAt_untyped_inv hcap
  have hmod : ∀ d, d ∣ 2 ^ sb.val → p.val % d = 0 := by
    intro d hd; have := Nat.mod_mod_of_dvd p.val hd; rw [hpal, Nat.zero_mod] at this; exact this.symm
  have h16 : 16 ∣ 2 ^ sb.val := by
    have := Nat.pow_dvd_pow 2 hsb4; simpa using this
  have hp8 : p.val % 8 = 0 := hmod 8 (dvd_trans (by norm_num) h16)
  have hcapW : ∀ (s1 : S) c, Q s1 → WFrame (L := L) s s1 (ResetW p sb x PW) →
      obj.Slot.set_cap st x s1 c ⦃ s' => WFrame (L := L) s s' (ResetW p sb x PW) ∧ Q s' ⦄ := fun s1 c hq hw =>
    WP.spec_mono (WP.spec_and (set_cap_frame s1 x c hx hxf) (hQk.2 s1 c hq)) fun s' ⟨h1, h2⟩ =>
      ⟨hw.trans (h1.mono fun w h => Or.inr (Or.inl h)), h2⟩
  unfold untyped.reset_untyped
  rw [slot_cap_eq, hcap]
  simp only [bind_ok, untyped.as_untyped]
  by_cases hfi0 : fi = 0#u64
  · simp only [hfi0, ↓reduceIte]; exact (WP.spec_ok _).2 ⟨WFrame.refl _ _, hQ⟩
  simp only [hfi0, ↓reduceIte]
  have hfi0v : fi.val ≠ 0 := fun e => hfi0 (UScalar.eq_of_val_eq e)
  cases dev
  · simp only [Bool.false_eq_true, ↓reduceIte]
    by_cases hsm : sb < untyped.RESET_CHUNK_BITS
    · rw [if_pos hsm]
      have h63 : (sb &&& 63#u64).val = sb.val := by
        have : (sb &&& 63#u64).val = sb.val % 64 := by
          simp only [UScalar.val_and]; exact Nat.and_two_pow_sub_one_eq_mod _ 6
        rw [this]; omega
      obtain ⟨i1, hi1, hv1, -⟩ := spec_exists (UScalar.ShiftLeft_spec (1#u64 : U64) (sb &&& 63#u64) _
        (by rw [h63]; simp [UScalarTy.U64_numBits_eq]; omega) rfl)
      have hi1v : i1.val = 2 ^ sb.val := by
        rw [hv1, h63, Nat.shiftLeft_eq]
        simp [U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits]
        exact Nat.pow_lt_pow_right (by decide) hsb
      simp only [lift, bind_ok, hi1, L.clear_free_eq]
      have hz := zr_frame (L := L) s p i1 hp8 (by rw [hi1v]; omega) (by rw [hi1v]; omega)
      have hq1 : Q (L.zr s p i1) := hQk.1 _ _ _ hp8 (by rw [hi1v]; omega) (le_refl _) (by rw [hi1v]) hQ
      refine WP.spec_bind (hcapW _ _ hq1 (hz.mono fun w h => Or.inl (by rw [hi1v] at h; exact h)))
        fun s2 h2 => (WP.spec_ok _).2 h2
    · rw [if_neg hsm]
      have hsb16 : 16 ≤ sb.val := by rw [reset_chunk_bits_eq] at hsm; exact Nat.le_of_not_lt hsm
      have hC : untyped.RESET_CHUNK.val = 65536 := by rw [reset_chunk_eq]; rfl
      obtain ⟨i, hi, hiv, -⟩ := spec_exists (U64.sub_spec (x := fi) (y := 1#u64)
        (by have : (1#u64 : U64).val = 1 := rfl; rw [this]; omega))
      obtain ⟨i1, hi1, hi1v, -⟩ := spec_exists (U64.sub_spec (x := untyped.RESET_CHUNK) (y := 1#u64)
        (by have : (1#u64 : U64).val = 1 := rfl; rw [this, hC]; omega))
      rw [hi, hi1]
      simp only [bind_ok, lift]
      have hi1v' : i1.val = 65535 := by rw [hi1v, hC]; rfl
      have hov : (i &&& ~~~i1).val = (fi.val - 1) / 65536 * 65536 := by
        rw [and_not_mask i i1 hi1v', hiv]; rfl
      have hdv : 65536 ∣ 2 ^ sb.val := by
        have := Nat.pow_dvd_pow 2 hsb16; simpa using this
      obtain ⟨t, ht⟩ := hdv
      have hq : (fi.val - 1) / 65536 < t := by rw [Nat.div_lt_iff_lt_mul (by decide)]; omega
      have hp16 := hmod 65536 ⟨t, ht⟩
      unfold untyped.reset_untyped_loop
      refine loop.spec_decr_nat (measure := fun y => y.2.2.val)
        (inv := fun y => y.2.2.val % 65536 = 0 ∧ y.2.2.val + 65536 ≤ 2 ^ sb.val ∧
          WFrame (L := L) s y.1 (ResetW p sb x PW) ∧ Q y.1) _ _ _ ?_ ?_
      rotate_left
      · exact ⟨by rw [hov]; omega, by rw [hov, ht]; nlinarith, WFrame.refl _ _, hQ⟩
      rintro ⟨s1, a1, o⟩ ⟨ho1, ho2, hW1, hQ1⟩
      simp only at ho1 ho2 hW1 hQ1 ⊢
      unfold untyped.reset_untyped_loop.body
      have hiv' : (core.num.U64.wrapping_add p o).val = p.val + o.val := by
        rw [core.num.U64.wrapping_add_val_eq]; simp [U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits]; omega
      simp only [lift, bind_ok, L.clear_free_eq]
      have hz := zr_frame (L := L) s1 (core.num.U64.wrapping_add p o) untyped.RESET_CHUNK
        (by unfold P1.Aligned; rw [hiv']; omega) (by rw [hC]) (by rw [hiv', hC]; omega)
      have hq1 := hQk.1 s1 _ _ (by unfold P1.Aligned; rw [hiv']; omega) (by rw [hC])
        (by rw [hiv']; omega) (by rw [hiv', hC]; omega) hQ1
      have hW1z : WFrame (L := L) s (L.zr s1 (core.num.U64.wrapping_add p o) untyped.RESET_CHUNK) (ResetW p sb x PW) :=
        hW1.trans (hz.mono fun w h => Or.inl (by rw [hiv', hC] at h; omega))
      refine WP.spec_bind (hcapW _ _ hq1 hW1z) fun s2 ⟨hW2, hQ2⟩ => ?_
      by_cases ho0 : o = 0#u64
      · rw [if_pos ho0]; exact (WP.spec_ok _).2 ⟨hW2, hQ2⟩
      rw [if_neg ho0]
      have ho0' : o.val ≠ 0 := fun e => ho0 (UScalar.eq_of_val_eq e)
      refine WP.spec_bind (hPPF s2 a1 hQ2) ?_
      rintro ⟨r, s3, a2⟩ ⟨hW3, hQ3⟩
      simp only at hW3 hQ3
      have hW3' : WFrame (L := L) s s3 (ResetW p sb x PW) := hW2.trans (hW3.mono fun w h => Or.inr (Or.inr h))
      cases r with
      | Ok u =>
        simp only [bind_ok, core.result.Result.Insts.CoreOpsTry.branch, uncurry_apply_pair]
        have hsv : (core.num.U64.saturating_sub o untyped.RESET_CHUNK).val = o.val - 65536 := by
          show (BitVec.ofNat 64 (max 0 (o.val - untyped.RESET_CHUNK.val))).toNat = _
          rw [hC]; simp; omega
        refine (WP.spec_ok _).2 ⟨⟨by rw [hsv]; omega, by rw [hsv]; omega, hW3', hQ3⟩, ?_⟩
        show (core.num.U64.saturating_sub o untyped.RESET_CHUNK).val < o.val
        rw [hsv]; omega
      | Err e =>
        simp only [bind_ok, core.result.Result.Insts.CoreOpsTry.branch, uncurry_apply_pair,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from]
        simp only [bind_tc_ok, bind_ok]
        exact (WP.spec_ok _).2 ⟨hW3', hQ3⟩
  · simp only [↓reduceIte, bind_ok]
    refine WP.spec_bind (hcapW _ _ hQ (WFrame.refl _ _)) fun s2 h2 => (WP.spec_ok _).2 h2

end

/-! ## The TCB loop -/

/-- The words the TCB loop may write: slot words, the window, the debug-list
head word `DW`, and the old head's `debug_prev` word. -/
def TcbLoopW (th : TypedHeap) (A win : Nat) (DW h0 : U64) (w : U64) : Prop :=
  SlotW th w ∨ (A ≤ w.val ∧ w.val < A + win * 4096) ∨ w = DW ∨ (h0 ≠ 0#u64 ∧ w.val = h0.val + 3584)

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

set_option maxRecDepth 20000 in
/-- **`create_new_objects`' write frame for TCBs** (`create_loop_rel_tcb`
with the frame `TcbLoopW`). -/
theorem create_loop_frame_tcb {A' : Type} (arI : machine.Arch A') (ar : A') (th th' : TypedHeap) (hP' : Placed th')
    (hext : ∀ a, IsSlot th a → IsSlot th' a)
    {pp : U64} {rs : Nat} (hpp : th' pp = some (.cnode rs))
    {idx : List Bool} (hidx : idx.length = rs) (hppo : IsSlot th (cslotAddr (pp.bv, idx))) {p sb fi : U64} {d : Bool}
    (hsb : sb.val < 64) (hpfit : p.val + 2 ^ sb.val ≤ 2 ^ 64)
    (σ1 : Fl4Spec.State Unit) {dest : U64} {r : Nat} (hdest : th' dest = some (.cnode r))
    (hdesto : th dest = some (.cnode r)) (hr : r ≤ 64)
    (nt us : U64) (dev : Bool) (t : Fl4Spec.ApiObjectType) (ht : objTypeOf nt.val = some t)
    (hnt : nt.val = 1) (hus : us.val < 64)
    (off win base : U64) (hwin : off.val + win.val ≤ 2 ^ r)
    (hfit : base.val + win.val * 4096 ≤ 2 ^ 64) (hhigh : 2 ^ 64 - 2 ^ 47 ≤ base.val) (hal : base.val % 32 = 0)
    (hpA : p.val ≤ base.val) (hAp : base.val + win.val * 4096 ≤ p.val + 2 ^ sb.val)
    (hnew : ∀ i, i < win.val → th' ⟨BitVec.ofNat 64 (base.val + i * 4096)⟩ = some .tcb)
    (zhi : Nat) (hzhi : base.val + win.val * 4096 ≤ zhi)
    (hzs : ∀ a, IsSlot th' a → a.val + 32 ≤ base.val + win.val * 4096 ∨ zhi ≤ a.val)
    (hold : ∀ a, IsSlot th a → a.val + 32 ≤ base.val ∨ zhi ≤ a.val)
    (ksb0 DW : U64) (hDWal : P1.Aligned DW) (hDWout : ∀ a, IsSlot th' a → ¬ (a.val ≤ DW.val ∧ DW.val < a.val + 32))
    (hDWreg : ¬ (base.val ≤ DW.val ∧ DW.val < zhi))
    (hDW : ∀ s : S, L.ksb s = ksb0 → L.nodeAt s 0#u64 layout.node.DEBUG_TCBS = DW)
    (G0 : MdbGhost) (m0 : U64 → U64)
    (hsrcd : ∀ j, j < win.val → cslotAddr (pp.bv, idx) ≠ slotAddr dest.bv (BitVec.ofNat 64 (off.val + j)))
    (s : S)
    (hinv : LoopInv (L := L) th' (pp.bv, idx) (.Untyped p sb fi d) σ1
      (Fl4Spec.createCap (Z := Unit) t us.val (pp.bv, idx) dev)
      ((windowSlots dest r off.val win.val).zip (regionPtrs (BitVec.ofNat 64 base.val) win.val (2 ^ zOf nt.val us.val)))
      base.val (2 ^ zOf nt.val us.val) win.val (fun j => slotAddr dest.bv (BitVec.ofNat 64 (off.val + j)))
      (base.val + win.val * 4096) zhi G0 m0 (cjOf nt.val us dev base.val (2 ^ zOf nt.val us.val)) s 0)
    (hX : TcbX (L := L) th th' ksb0 DW base.val win.val zhi s 0) :
    objects.create_new_objects st arI s ar nt (cslotAddr (pp.bv, idx)) dest off win base us dev ⦃ res =>
      res.2 = ar ∧ LoopInv (L := L) th' (pp.bv, idx) (.Untyped p sb fi d) σ1
      (Fl4Spec.createCap (Z := Unit) t us.val (pp.bv, idx) dev)
      ((windowSlots dest r off.val win.val).zip (regionPtrs (BitVec.ofNat 64 base.val) win.val (2 ^ zOf nt.val us.val)))
      base.val (2 ^ zOf nt.val us.val) win.val (fun j => slotAddr dest.bv (BitVec.ofNat 64 (off.val + j)))
      (base.val + win.val * 4096) zhi G0 m0 (cjOf nt.val us dev base.val (2 ^ zOf nt.val us.val)) res.1 win.val ∧
      L.ksb res.1 = ksb0 ∧ WFrame (L := L) s res.1 (TcbLoopW th' base.val win.val DW (L.mem s DW)) ⦄ := by
  have hz12 : zOf nt.val us.val = 12 := by simp [zOf, hnt]
  have hk : 2 ^ zOf nt.val us.val = 4096 := by rw [hz12]; rfl
  have hn14 : nt.val < 14 := by omega
  unfold objects.create_new_objects
  rw [object_size_eq nt us hn14 hus]
  simp only [bind_ok]
  unfold objects.create_new_objects_loop
  have h63 : ((⟨BitVec.ofNat 64 (zOf nt.val us.val)⟩ : U64) &&& 63#u64).val = zOf nt.val us.val := by
    have : ((⟨BitVec.ofNat 64 (zOf nt.val us.val)⟩ : U64) &&& 63#u64).val =
        (⟨BitVec.ofNat 64 (zOf nt.val us.val)⟩ : U64).val % 64 := by
      simp only [UScalar.val_and]; exact Nat.and_two_pow_sub_one_eq_mod _ 6
    rw [this]
    show (BitVec.ofNat 64 (zOf nt.val us.val)).toNat % 64 = _
    simp; omega
  have hdsl : ∀ j, j < win.val → IsSlot th (slotAddr dest.bv (BitVec.ofNat 64 (off.val + j))) :=
    fun j hj => ⟨dest, off.val + j, Or.inl ⟨r, hdesto, by omega⟩, rfl⟩
  have hnewcv : ∀ i, i < win.val →
      CapValid th' (newCapOf nt.val ⟨BitVec.ofNat 64 (base.val + i * 2 ^ zOf nt.val us.val)⟩ us dev) := by
    intro i hi; rw [hk, hnt]; exact hnew i hi
  refine loop.spec_decr_nat (measure := fun x => win.val - x.2.2.val)
    (inv := fun x => x.2.1 = ar ∧ x.2.2.val ≤ win.val ∧ LoopInv (L := L) th' (pp.bv, idx) (.Untyped p sb fi d) σ1
      (Fl4Spec.createCap (Z := Unit) t us.val (pp.bv, idx) dev)
      ((windowSlots dest r off.val win.val).zip (regionPtrs (BitVec.ofNat 64 base.val) win.val (2 ^ zOf nt.val us.val)))
      base.val (2 ^ zOf nt.val us.val) win.val (fun j => slotAddr dest.bv (BitVec.ofNat 64 (off.val + j)))
      (base.val + win.val * 4096) zhi G0 m0 (cjOf nt.val us dev base.val (2 ^ zOf nt.val us.val)) x.1 x.2.2.val ∧
      TcbX (L := L) th th' ksb0 DW base.val win.val zhi x.1 x.2.2.val ∧
      WFrame (L := L) s x.1 (TcbLoopW th' base.val win.val DW (L.mem s DW)) ∧
      (L.mem x.1 DW = L.mem s DW ∨ (base.val ≤ (L.mem x.1 DW).val ∧ (L.mem x.1 DW).val + 4096 ≤ base.val + win.val * 4096))) _ _ _ ?_ ?_
  · rintro ⟨s1, a1, i⟩ ⟨ha, hiw, hI, hXi, hW1, hD1⟩
    simp only at ha hiw hI hXi hW1 hD1 ⊢
    subst ha
    unfold objects.create_new_objects_loop.body
    by_cases hit : i < win
    · rw [if_pos hit]
      have hit' : i.val < win.val := hit
      simp only [lift, bind_ok]
      have hik : (i.val + 1) * 4096 ≤ win.val * 4096 := Nat.mul_le_mul_right _ hit'
      rw [Nat.add_mul, Nat.one_mul] at hik
      obtain ⟨i2, hi2, hv2, -⟩ := spec_exists (UScalar.ShiftLeft_spec i
        ((⟨BitVec.ofNat 64 (zOf nt.val us.val)⟩ : U64) &&& 63#u64) _
        (by rw [h63]; simp [UScalarTy.U64_numBits_eq]; omega) rfl)
      rw [hi2]; simp only [bind_ok]
      have hi2v : i2.val = i.val * 4096 := by
        rw [hv2, h63, Nat.shiftLeft_eq, hk]
        simp [U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits]; omega
      have hi3 : core.num.U64.wrapping_add base i2 = ⟨BitVec.ofNat 64 (base.val + i.val * 4096)⟩ := by
        apply u64_ofNat_eq
        simp [core.num.U64.wrapping_add_val_eq, U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits, hi2v]; omega
      rw [hi3]
      obtain ⟨⟨c, s2, a2⟩, hcr, hc, ha2, hI2, hk2, hz2, hX22, hm2⟩ := spec_exists (create_step (L := L) arI a1 th th'
        hP' ksb0 DW base.val win.val zhi hDWal hDWout hDWreg hDW rfl hzhi hfit hal hnew
        (fun j hj => hext _ (hdsl j hj)) (hext _ hppo) nt us dev hnt s1 i.val hit' hI hXi)
      simp only at hc ha2 hI2 hk2 hz2 hX22 hm2
      -- the frame of the creation
      have hW2 : WFrame (L := L) s s2 (TcbLoopW th' base.val win.val DW (L.mem s DW)) := by
        set bi : U64 := ⟨BitVec.ofNat 64 (base.val + i.val * 4096)⟩ with hbi
        have hbiv : bi.val = base.val + i.val * 4096 := by
          show (BitVec.ofNat 64 (base.val + i.val * 4096)).toNat = _; simp; omega
        have htk : TcbOk bi := ⟨by rw [hbiv]; omega, by rw [hbiv]; omega⟩
        obtain ⟨hksb1, hz1, -, hX31⟩ := hXi
        have hcpu : tcbCpu (L := L) s1 bi = 0#u64 := by
          unfold tcbCpu
          have hv : (core.num.U64.wrapping_add bi 3520#u64).val = base.val + i.val * 4096 + 3520 := by
            obtain ⟨h1, h2⟩ := htk; rw [← hbiv]; addr_tac
          exact hz1 _ (by unfold P1.Aligned; omega) (by omega) (by omega)
        have hdw : dbgW (L := L) s1 bi = DW := by unfold dbgW; rw [hcpu]; exact hDW s1 hksb1
        have hnotInT : ∀ w : U64, InT bi w → base.val ≤ w.val ∧ w.val < base.val + (i.val + 1) * 4096 := by
          rintro w ⟨h1, h2, -⟩; rw [hbiv] at h1 h2; omega
        obtain ⟨r', hr', -, -, hf', -⟩ := spec_exists (create_tcb_frame (L := L) arI s1 a1 nt bi us dev hnt htk
          (by rw [hdw]; exact hDWal)
          (by rw [hdw]; intro h; rcases hX31 with h' | ⟨-, h', -⟩; exact absurd h' h; exact h')
          (by rw [hdw]; intro h; exact hDWreg (by have := hnotInT DW h; omega)))
        rw [hcr] at hr'; cases eq_of_ok_eq hr'
        refine hW1.trans (hf'.mono fun w hw => ?_)
        unfold TcbW at hw; rw [hdw] at hw
        rcases hw with h | ⟨hne, he⟩ | he
        · exact Or.inr (Or.inl (by have := hnotInT w h; omega))
        · rcases hD1 with e | ⟨h1, h2⟩
          · rw [e] at hne he; exact Or.inr (Or.inr (Or.inr ⟨hne, he⟩))
          · exact Or.inr (Or.inl (by omega))
        · exact Or.inr (Or.inr (Or.inl (UScalar.eq_of_val_eq he)))
      subst hc ha2
      rw [hcr]; simp only [bind_ok, uncurry_apply_pair]
      have hi4 : (core.num.U64.wrapping_add off i).bv = BitVec.ofNat 64 (off.val + i.val) := by
        rw [bv_eq_ofNat]; congr 1
        have : off.val + i.val < 2 ^ 64 := by
          have := Nat.pow_le_pow_right (show 0 < 2 by decide) hr; omega
        simp [core.num.U64.wrapping_add_val_eq, U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits]; omega
      rw [show obj.Slot.index dest (core.num.U64.wrapping_add off i) =
        ok (slotAddr dest.bv (BitVec.ofNat 64 (off.val + i.val))) by
          rw [spec_eq_ok (slot_index_spec dest _), hi4]]
      simp only [bind_ok]
      have hcap : capability.Cap.Thread ⟨BitVec.ofNat 64 (base.val + i.val * 4096)⟩ =
          newCapOf nt.val ⟨BitVec.ofNat 64 (base.val + i.val * 2 ^ zOf nt.val us.val)⟩ us dev := by
        rw [hk, hnt]; rfl
      rw [hcap]
      obtain ⟨σi, Gi, -, -, -, hM2, -, -, hsrc2, hnull2, -⟩ := id hI2
      have hsm : cslotAddr (pp.bv, idx) ∈ Gi.chains.flatten := (hM2.members _).2 ⟨hext _ hppo, _, hsrc2, by simp⟩
      have hdn : slotAddr dest.bv (BitVec.ofNat 64 (off.val + i.val)) ∉ Gi.chains.flatten := by
        intro h; obtain ⟨-, c0, h0, hn0⟩ := (hM2.members _).1 h
        rw [hnull2 i.val le_rfl hit'] at h0; exact hn0 (eq_of_ok_eq h0).symm
      have he : EncWf (newCapOf nt.val ⟨BitVec.ofNat 64 (base.val + i.val * 2 ^ zOf nt.val us.val)⟩ us dev) :=
        newCap_encWf (by omega) _ us dev hus (canonical_of_high (by
          show 2 ^ 64 - 2 ^ 47 ≤ (BitVec.ofNat 64 _).toNat; rw [hk]; simp; omega))
      obtain ⟨s3, hs3, hL3⟩ := spec_exists (loop_step th' hP' hpp hidx hsb hpfit σ1 hdest hr nt us dev t ht
        (by omega) hus (by omega) (fun h => by omega) off.val win.val base.val hwin (by rw [hk]; exact hfit) hhigh hpA
        (by rw [hk]; exact hAp) hnewcv (base.val + win.val * 4096) zhi hzs G0 m0 hsrcd s2 i.val hit' hI2)
      obtain ⟨s3', hs3', hX3⟩ := spec_exists (tcbx_insert (L := L) th th' hP' hext ksb0 DW base.val win.val zhi hDWal
        hDWout hold hzhi hnew hfit hal s2 Gi hM2 _ _ hsm hppo (hdsl i.val hit') hdn _ he i.val hit' hk2 hz2 hX22 hm2)
      rw [hs3] at hs3'; cases eq_of_ok_eq hs3'
      have hnx : nextOf (L.mem s2) (cslotAddr (pp.bv, idx)) = 0#u64 ∨
          IsSlot th' (nextOf (L.mem s2) (cslotAddr (pp.bv, idx))) := by
        rcases hM2.next_mem hsm with h | ⟨h1, -⟩
        · exact Or.inl h
        · exact Or.inr ((hM2.members _).1 h1).1
      obtain ⟨s3', hs3', hfr⟩ := spec_exists (insert_new_frame (L := L) hP' s2
        (newCapOf nt.val ⟨BitVec.ofNat 64 (base.val + i.val * 2 ^ zOf nt.val us.val)⟩ us dev) _ _ (hext _ hppo)
        (hext _ (hdsl i.val hit')) hnx)
      rw [hs3] at hs3'; cases eq_of_ok_eq hs3'
      obtain ⟨s3', hs3', hk3⟩ := spec_exists (insert_new_ksb (L := L) s2 (cslotAddr (pp.bv, idx))
        (slotAddr dest.bv (BitVec.ofNat 64 (off.val + i.val)))
        (newCapOf nt.val ⟨BitVec.ofNat 64 (base.val + i.val * 2 ^ zOf nt.val us.val)⟩ us dev))
      rw [hs3] at hs3'; cases eq_of_ok_eq hs3'
      have hslw : ∀ a, (a = cslotAddr (pp.bv, idx) ∨ a = slotAddr dest.bv (BitVec.ofNat 64 (off.val + i.val)) ∨
          (nextOf (L.mem s2) (cslotAddr (pp.bv, idx)) ≠ 0#u64 ∧ a = nextOf (L.mem s2) (cslotAddr (pp.bv, idx)))) →
          IsSlot th' a := by
        rintro a (e | e | ⟨h0, e⟩)
        · rw [e]; exact hext _ hppo
        · rw [e]; exact hext _ (hdsl i.val hit')
        · rw [e]; exact hnx.resolve_left h0
      have hW3 : WFrame (L := L) s s3 (TcbLoopW th' base.val win.val DW (L.mem s DW)) :=
        hW2.trans ⟨hk3, fun w hw hnp => hfr w hw (fun a ha hin => hnp (Or.inl ⟨a, hslw a ha, hin.1, hin.2⟩))⟩
      have hD3 : L.mem s3 DW = ⟨BitVec.ofNat 64 (base.val + i.val * 4096)⟩ := by
        rw [hfr DW hDWal (fun a ha hin => hDWout a (hslw a ha) hin)]; exact hm2
      rw [hs3]; simp only [bind_ok]
      step as ⟨i5, hi5⟩
      refine ⟨by omega, by rw [hi5]; exact hL3, by rw [hi5]; exact hX3, hW3, Or.inr ?_, by omega⟩
      have : (⟨BitVec.ofNat 64 (base.val + i.val * 4096)⟩ : U64).val = base.val + i.val * 4096 := by
        show (BitVec.ofNat 64 (base.val + i.val * 4096)).toNat = _; simp; omega
      rw [hD3, this]; omega
    · rw [if_neg hit, WP.spec_ok]
      have : i.val = win.val := by have : ¬ i.val < win.val := hit; omega
      rw [this] at hI
      exact ⟨rfl, hI, hXi.1, hW1⟩
  · exact ⟨rfl, by simp, hinv, hX, WFrame.refl s _, Or.inl rfl⟩

end

/-! ## The loop with a per-object frame (PML4s) -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **`create_new_objects`' write frame, each object writing only its own
window slot** (`create_loop_rel_gen`; PML4s, by `create_object_pml4`):
slot words and the window. -/
theorem create_loop_frame_gen {A' : Type} (arI : machine.Arch A') (ar : A') (th' : TypedHeap) (hP' : Placed th')
    {pp : U64} {rs : Nat} (hpp : th' pp = some (.cnode rs))
    {idx : List Bool} (hidx : idx.length = rs) {p sb fi : U64} {d : Bool}
    (hsb : sb.val < 64) (hpfit : p.val + 2 ^ sb.val ≤ 2 ^ 64)
    (σ1 : Fl4Spec.State Unit) {dest : U64} {r : Nat} (hdest : th' dest = some (.cnode r)) (hr : r ≤ 64)
    (nt us : U64) (dev : Bool) (t : Fl4Spec.ApiObjectType) (ht : objTypeOf nt.val = some t)
    (hn : nt.val ≤ 13) (hus : us.val < 64) (hz : zOf nt.val us.val < 64)
    (hsc : nt.val = 5 → 7 ≤ us.val)
    (off win base : U64) (hwin : off.val + win.val ≤ 2 ^ r)
    (hfit : base.val + win.val * 2 ^ zOf nt.val us.val ≤ 2 ^ 64) (hhigh : 2 ^ 64 - 2 ^ 47 ≤ base.val)
    (hpA : p.val ≤ base.val) (hAp : base.val + win.val * 2 ^ zOf nt.val us.val ≤ p.val + 2 ^ sb.val)
    (hnewcv : ∀ i, i < win.val →
      CapValid th' (newCapOf nt.val ⟨BitVec.ofNat 64 (base.val + i * 2 ^ zOf nt.val us.val)⟩ us dev))
    (zlo zhi : Nat) (hzs : ∀ a, IsSlot th' a → a.val + 32 ≤ zlo ∨ zhi ≤ a.val)
    (G0 : MdbGhost) (m0 : U64 → U64)
    (hsrcd : ∀ j, j < win.val → cslotAddr (pp.bv, idx) ≠ slotAddr dest.bv (BitVec.ofNat 64 (off.val + j)))
    (hslo : ∀ a, IsSlot th' a → a.val + 32 ≤ base.val ∨ base.val + win.val * 2 ^ zOf nt.val us.val ≤ a.val)
    (hzlo : base.val + win.val * 2 ^ zOf nt.val us.val ≤ zlo)
    (hco : ∀ (s1 : S) (a1 : A') (i : Nat), i < win.val →
      objects.create_object st arI s1 a1 nt ⟨BitVec.ofNat 64 (base.val + i * 2 ^ zOf nt.val us.val)⟩ us dev ⦃ res =>
        res.1 = newCapOf nt.val ⟨BitVec.ofNat 64 (base.val + i * 2 ^ zOf nt.val us.val)⟩ us dev ∧ res.2.2 = a1 ∧
        L.ksb res.2.1 = L.ksb s1 ∧ ∀ w : U64, P1.Aligned w → ¬ (base.val + i * 2 ^ zOf nt.val us.val ≤ w.val ∧
          w.val < base.val + i * 2 ^ zOf nt.val us.val + 2 ^ zOf nt.val us.val) → L.mem res.2.1 w = L.mem s1 w ⦄)
    (s : S)
    (hinv : LoopInv (L := L) th' (pp.bv, idx) (.Untyped p sb fi d) σ1
      (Fl4Spec.createCap (Z := Unit) t us.val (pp.bv, idx) dev)
      ((windowSlots dest r off.val win.val).zip (regionPtrs (BitVec.ofNat 64 base.val) win.val (2 ^ zOf nt.val us.val)))
      base.val (2 ^ zOf nt.val us.val) win.val (fun j => slotAddr dest.bv (BitVec.ofNat 64 (off.val + j))) zlo zhi G0 m0
      (cjOf nt.val us dev base.val (2 ^ zOf nt.val us.val)) s 0) :
    objects.create_new_objects st arI s ar nt (cslotAddr (pp.bv, idx)) dest off win base us dev ⦃ res =>
      res.2 = ar ∧ LoopInv (L := L) th' (pp.bv, idx) (.Untyped p sb fi d) σ1
      (Fl4Spec.createCap (Z := Unit) t us.val (pp.bv, idx) dev)
      ((windowSlots dest r off.val win.val).zip (regionPtrs (BitVec.ofNat 64 base.val) win.val (2 ^ zOf nt.val us.val)))
      base.val (2 ^ zOf nt.val us.val) win.val (fun j => slotAddr dest.bv (BitVec.ofNat 64 (off.val + j))) zlo zhi G0 m0
      (cjOf nt.val us dev base.val (2 ^ zOf nt.val us.val)) res.1
        win.val ∧ L.ksb res.1 = L.ksb s ∧ WFrame (L := L) s res.1 (fun w => SlotW th' w ∨
          (base.val ≤ w.val ∧ w.val < base.val + win.val * 2 ^ zOf nt.val us.val)) ⦄ := by
  have hn14 : nt.val < 14 := by omega
  unfold objects.create_new_objects
  rw [object_size_eq nt us hn14 hus]
  simp only [bind_ok]
  unfold objects.create_new_objects_loop
  have hk1 : 1 ≤ 2 ^ zOf nt.val us.val := Nat.one_le_two_pow
  have h63 : ((⟨BitVec.ofNat 64 (zOf nt.val us.val)⟩ : U64) &&& 63#u64).val = zOf nt.val us.val := by
    have : ((⟨BitVec.ofNat 64 (zOf nt.val us.val)⟩ : U64) &&& 63#u64).val =
        (⟨BitVec.ofNat 64 (zOf nt.val us.val)⟩ : U64).val % 64 := by
      simp only [UScalar.val_and]; exact Nat.and_two_pow_sub_one_eq_mod _ 6
    rw [this]
    show (BitVec.ofNat 64 (zOf nt.val us.val)).toNat % 64 = _
    simp; omega
  refine loop.spec_decr_nat (measure := fun x => win.val - x.2.2.val)
    (inv := fun x => x.2.1 = ar ∧ x.2.2.val ≤ win.val ∧ LoopInv (L := L) th' (pp.bv, idx) (.Untyped p sb fi d) σ1
      (Fl4Spec.createCap (Z := Unit) t us.val (pp.bv, idx) dev)
      ((windowSlots dest r off.val win.val).zip (regionPtrs (BitVec.ofNat 64 base.val) win.val (2 ^ zOf nt.val us.val)))
      base.val (2 ^ zOf nt.val us.val) win.val (fun j => slotAddr dest.bv (BitVec.ofNat 64 (off.val + j))) zlo zhi G0 m0
      (cjOf nt.val us dev base.val (2 ^ zOf nt.val us.val)) x.1
        x.2.2.val ∧ L.ksb x.1 = L.ksb s ∧ WFrame (L := L) s x.1 (fun w => SlotW th' w ∨
          (base.val ≤ w.val ∧ w.val < base.val + win.val * 2 ^ zOf nt.val us.val))) _ _ _ ?_ ?_
  · rintro ⟨s1, a1, i⟩ ⟨ha, hiw, hI, hks, hW1⟩
    simp only at ha hiw hI hks hW1 ⊢
    subst ha
    unfold objects.create_new_objects_loop.body
    by_cases hit : i < win
    · rw [if_pos hit]
      have hit' : i.val < win.val := hit
      simp only [lift, bind_ok]
      have hik : (i.val + 1) * 2 ^ zOf nt.val us.val ≤ win.val * 2 ^ zOf nt.val us.val :=
        Nat.mul_le_mul_right _ hit'
      rw [Nat.add_mul, Nat.one_mul] at hik
      obtain ⟨i2, hi2, hv2, -⟩ := spec_exists (UScalar.ShiftLeft_spec i
        ((⟨BitVec.ofNat 64 (zOf nt.val us.val)⟩ : U64) &&& 63#u64) _
        (by rw [h63]; simp [UScalarTy.U64_numBits_eq]; omega) rfl)
      rw [hi2]; simp only [bind_ok]
      have hi2v : i2.val = i.val * 2 ^ zOf nt.val us.val := by
        rw [hv2, h63, Nat.shiftLeft_eq]
        simp [U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits]; omega
      have hi3 : core.num.U64.wrapping_add base i2 =
          ⟨BitVec.ofNat 64 (base.val + i.val * 2 ^ zOf nt.val us.val)⟩ := by
        apply u64_ofNat_eq
        simp [core.num.U64.wrapping_add_val_eq, U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits, hi2v]; omega
      rw [hi3]
      obtain ⟨⟨c1, s1', a1'⟩, hco1, hc1, ha1, hks1, hfr1⟩ := spec_exists (hco s1 a1 i.val hit')
      simp only at hc1 ha1 hks1 hfr1
      subst hc1 ha1
      rw [hco1]
      simp only [bind_ok, uncurry_apply_pair]
      have hbi : base.val + i.val * 2 ^ zOf nt.val us.val + 2 ^ zOf nt.val us.val ≤
          base.val + win.val * 2 ^ zOf nt.val us.val := by omega
      have hS1 : SlotsSame th' (L.mem s1) (L.mem s1') := slotsSame_out hP' (lo := base.val + i.val * 2 ^ zOf nt.val us.val)
        (hi := base.val + i.val * 2 ^ zOf nt.val us.val + 2 ^ zOf nt.val us.val)
        (fun a ha => by rcases hslo a ha with h | h <;> [left; right] <;> omega)
        (fun w hw ho => hfr1 w hw (by omega))
      have hdsl : ∀ j, j < win.val → IsSlot th' (slotAddr dest.bv (BitVec.ofNat 64 (off.val + j))) :=
        fun j hj => ⟨dest, off.val + j, Or.inl ⟨r, hdest, by omega⟩, rfl⟩
      have hI := LoopInv.of_same (s' := s1') hdsl
        (AbsSlot.isSlot ⟨pp, rfl, Or.inl (by simpa [hidx] using hpp)⟩) (by omega) hI hS1
        (fun w hw h1 h2 => hfr1 w hw (by omega))
      have hi4 : (core.num.U64.wrapping_add off i).bv = BitVec.ofNat 64 (off.val + i.val) := by
        rw [bv_eq_ofNat]; congr 1
        have : off.val + i.val < 2 ^ 64 := by
          have := Nat.pow_le_pow_right (show 0 < 2 by decide) hr; omega
        simp [core.num.U64.wrapping_add_val_eq, U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits]; omega
      rw [show obj.Slot.index dest (core.num.U64.wrapping_add off i) =
        ok (slotAddr dest.bv (BitVec.ofNat 64 (off.val + i.val))) by
          rw [spec_eq_ok (slot_index_spec dest _), hi4]]
      simp only [bind_ok]
      have hW2 : WFrame (L := L) s s1' (fun w => SlotW th' w ∨
          (base.val ≤ w.val ∧ w.val < base.val + win.val * 2 ^ zOf nt.val us.val)) :=
        hW1.trans ⟨hks1, fun w hw hnp => hfr1 w hw (fun h => hnp (Or.inr ⟨by omega, by omega⟩))⟩
      obtain ⟨σi, Gi, -, -, -, hMi, -, -, hcsi, -⟩ := id hI
      have hss : IsSlot th' (cslotAddr (pp.bv, idx)) :=
        AbsSlot.isSlot ⟨pp, rfl, Or.inl (by simpa [hidx] using hpp)⟩
      have hsm : cslotAddr (pp.bv, idx) ∈ Gi.chains.flatten := (hMi.members _).2 ⟨hss, _, hcsi, by simp⟩
      have hnx : nextOf (L.mem s1') (cslotAddr (pp.bv, idx)) = 0#u64 ∨
          IsSlot th' (nextOf (L.mem s1') (cslotAddr (pp.bv, idx))) := by
        rcases hMi.next_mem hsm with h | ⟨h1, -⟩
        · exact Or.inl h
        · exact Or.inr ((hMi.members _).1 h1).1
      obtain ⟨s3f, hs3f, hfr⟩ := spec_exists (insert_new_frame (L := L) hP' s1'
        (newCapOf nt.val ⟨BitVec.ofNat 64 (base.val + i.val * 2 ^ zOf nt.val us.val)⟩ us dev) _ _ hss
        (hdsl i.val hit') hnx)
      obtain ⟨s3, hs3e, hs3⟩ := spec_exists (loop_step th' hP' hpp hidx hsb hpfit σ1 hdest hr nt us dev t ht hn hus hz
        hsc off.val win.val base.val hwin hfit hhigh hpA hAp hnewcv zlo zhi hzs G0 m0 hsrcd s1' i.val hit' hI)
      obtain ⟨s3', hs3', hk3⟩ := spec_exists (insert_new_cap_ksb (L := L) s1' (cslotAddr (pp.bv, idx))
        (slotAddr dest.bv (BitVec.ofNat 64 (off.val + i.val)))
        (newCapOf nt.val ⟨BitVec.ofNat 64 (base.val + i.val * 2 ^ zOf nt.val us.val)⟩ us dev))
      rw [hs3e] at hs3'; cases eq_of_ok_eq hs3'
      rw [hs3e] at hs3f
      have e3 := eq_of_ok_eq hs3f
      subst e3
      have hW3 : WFrame (L := L) s s3 (fun w => SlotW th' w ∨
          (base.val ≤ w.val ∧ w.val < base.val + win.val * 2 ^ zOf nt.val us.val)) :=
        hW2.trans ⟨hk3, fun w hw hnp => hfr w hw (fun a ha hin => by
          refine hnp (Or.inl ⟨a, ?_, hin.1, hin.2⟩)
          rcases ha with e | e | ⟨h0, e⟩
          · rw [e]; exact hss
          · rw [e]; exact hdsl i.val hit'
          · rw [e]; exact hnx.resolve_left h0)⟩
      rw [hs3e]; simp only [bind_ok]
      step as ⟨i5, hi5⟩
      refine ⟨by omega, by rw [hi5]; exact hs3, by rw [hk3, hks1, hks], hW3, by omega⟩
    · rw [if_neg hit, WP.spec_ok]
      have : i.val = win.val := by have : ¬ i.val < win.val := hit; omega
      rw [this] at hI
      exact ⟨rfl, hI, hks, hW1⟩
  · exact ⟨rfl, by simp, hinv, rfl, WFrame.refl s _⟩

end

end Fl4Proofs.P3
