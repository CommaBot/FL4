/-
P3 (DESIGN.md §9), IO ports: **the IO port bitmap** (1024 words at
kernel-state offset `IOPORT_BITMAP`, port `p` is bit `p % 64` of word
`p / 64`) against the spec's `x64_allocated_io_ports` (`IoRel`), and what
FL4's bitmap operations do to it:

* `set_mask low high set` sets (or clears) the bits of the ports
  `low ..= high` and writes nothing but bitmap words (`set_mask_spec`);
* `range_free low high` tests that those bits are all clear
  (`range_free_eq`).

The bitmap words are outside every object (`IoLayout`), so the slots are
kept.
-/
import Fl4Proofs.P3.IntFrame
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

/-- Offset of bitmap word `w` in the kernel-state block. -/
def ioOff (w : U64) : U64 := core.num.U64.wrapping_add 5344#u64 (core.num.U64.wrapping_mul w 8#u64)

/-- Address of bitmap word `w`. -/
def ioA (kb w : U64) : U64 := core.num.U64.wrapping_add kb (ioOff w)

/-- The bitmap word of port `p`. -/
def wI (p : Nat) : U64 := ⟨BitVec.ofNat 64 (p / 64)⟩

/-- Port `p`'s bit in the bitmap. -/
def bitOf (mem : U64 → U64) (kb : U64) (p : Nat) : Bool := (mem (ioA kb (wI p))).val.testBit (p % 64)

theorem wI_val {p : Nat} (hp : p < 65536) : (wI p).val = p / 64 := by
  show (BitVec.ofNat 64 (p / 64)).toNat = _
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)

/-- The bitmap words, outside every object. -/
structure IoLayout (th : TypedHeap) (kb : U64) : Prop where
  fit : kb.val + 13568 ≤ 2 ^ 64
  out : ∀ w : U64, w.val < 1024 → OutsideObjects th (ioA kb w)

/-- The bitmap against the spec's allocated IO ports. -/
def IoRel (mem : U64 → U64) (kb : U64) (σ : Fl4Spec.State Unit) : Prop :=
  ∀ p : Nat, p < 65536 → σ.archState.x64AllocatedIoPorts (BitVec.ofNat 16 p) = bitOf mem kb p

theorem ioport_bitmap_eq : layout.ks.IOPORT_BITMAP = ok 5344#u64 := by
  obtain ⟨v, hv, rfl⟩ := spec_exists P0.Consts.layout.ks.IOPORT_BITMAP.spec; exact hv

theorem word_off_eq (w : U64) : ioport.word_off w = ok (ioOff w) := by
  unfold ioport.word_off; simp only [lift, bind_ok, ioport_bitmap_eq]; rfl

theorem ioA_val {kb w : U64} (hf : kb.val + 13568 ≤ 2 ^ 64) (hw : w.val < 1024) :
    (ioA kb w).val = kb.val + 5344 + 8 * w.val := by
  unfold ioA ioOff
  simp only [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq]
  simp [U64.size, U64.numBits]
  omega

theorem ioA_eq_iff {kb w w' : U64} (hf : kb.val + 13568 ≤ 2 ^ 64) (hw : w.val < 1024) (hw' : w'.val < 1024) :
    ioA kb w = ioA kb w' ↔ w.val = w'.val := by
  constructor
  · intro h; have h1 := ioA_val hf hw; have h2 := ioA_val hf hw'; rw [h] at h1; omega
  · intro h; rw [UScalar.eq_of_val_eq h]

/-! ## One word -/

/-- Setting or clearing the bits of `p` in `v`. -/
def opW (set : Bool) (p v : U64) : U64 := if set then v ||| p else v &&& ~~~p

theorem testBit_val (x : U64) (i : Nat) : x.val.testBit i = x.bv.getLsbD i := rfl

theorem opW_bit (set : Bool) (p v : U64) {i : Nat} (hi : i < 64) :
    (opW set p v).val.testBit i = if p.val.testBit i then set else v.val.testBit i := by
  unfold opW
  cases set
  · simp only [Bool.false_eq_true, ↓reduceIte, testBit_val, UScalar.bv_and, UScalar.bv_not,
      BitVec.getLsbD_and, BitVec.getLsbD_not]
    simp only [show i < 64 from hi, decide_true, Bool.true_and]
    cases p.bv.getLsbD i <;> simp
  · simp only [↓reduceIte, UScalar.val_or, Nat.testBit_lor]
    cases p.val.testBit i <;> simp

theorem max_bit {i : Nat} (hi : i < 64) : (core.num.U64.MAX).val.testBit i = true := by
  have : (core.num.U64.MAX).val = 2 ^ 64 - 1 := by simp [core.num.U64.MAX, U64.rMax]
  rw [this, Nat.testBit_two_pow_sub_one]; simpa using hi

/-- `pattern start end`: the bits `start ..< end`. -/
theorem pattern_spec (st en : U64) (hs : st.val ≤ 63) (hse : st.val ≤ en.val) (he : en.val ≤ 64) :
    ∃ P, ioport.pattern st en = ok P ∧ ∀ i, i < 64 → P.val.testBit i = decide (st.val ≤ i ∧ i < en.val) := by
  unfold ioport.pattern
  have hn : (core.num.U64.wrapping_sub en st).val = en.val - st.val := by
    rw [core.num.U64.wrapping_sub_val_eq]; simp [U64.size, U64.numBits]; omega
  simp only [lift, bind_ok]
  by_cases h64 : core.num.U64.wrapping_sub en st >= 64#u64
  · rw [if_pos h64]
    refine ⟨_, rfl, fun i hi => ?_⟩
    rw [max_bit hi]
    have : en.val - st.val ≥ 64 := by rw [← hn]; scalar_tac
    simp; omega
  rw [if_neg h64]
  have hlt : en.val - st.val < 64 := by rw [← hn]; scalar_tac
  have h63 : (core.num.U64.wrapping_sub en st &&& 63#u64).val = en.val - st.val := by
    rw [UScalar.val_and, hn]
    have : (63#u64 : U64).val = 2 ^ 6 - 1 := rfl
    rw [this, Nat.and_two_pow_sub_one_eq_mod]; exact Nat.mod_eq_of_lt (by omega)
  obtain ⟨z, hz, hzv, -⟩ := spec_exists (U64.ShiftLeft_spec (x := 1#u64)
    (y := core.num.U64.wrapping_sub en st &&& 63#u64) (by rw [h63]; omega))
  rw [hz]; simp only [bind_ok]
  have hzv' : z.val = 2 ^ (en.val - st.val) := by
    rw [hzv, h63, Nat.shiftLeft_eq]
    have h1 : (1#u64 : U64).val = 1 := rfl
    rw [h1, Nat.one_mul]
    exact Nat.mod_eq_of_lt (by have := Nat.pow_lt_pow_right (by decide : 1 < 2) hlt; simpa [U64.size, U64.numBits] using this)
  have hst : (st &&& 63#u64).val = st.val := by
    rw [UScalar.val_and]
    have : (63#u64 : U64).val = 2 ^ 6 - 1 := rfl
    rw [this, Nat.and_two_pow_sub_one_eq_mod]; exact Nat.mod_eq_of_lt (by omega)
  obtain ⟨P, hP, hPv, -⟩ := spec_exists (U64.ShiftLeft_spec (x := core.num.U64.wrapping_sub z 1#u64)
    (y := st &&& 63#u64) (by rw [hst]; omega))
  refine ⟨P, hP, fun i hi => ?_⟩
  have hsub : (core.num.U64.wrapping_sub z 1#u64).val = 2 ^ (en.val - st.val) - 1 := by
    rw [core.num.U64.wrapping_sub_val_eq, hzv']
    have : 0 < 2 ^ (en.val - st.val) := Nat.pow_pos (by decide)
    have h2 : 2 ^ (en.val - st.val) < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) hlt
    simp [U64.size, U64.numBits]; omega
  rw [hPv, hsub, hst, Nat.shiftLeft_eq, show U64.size = 2 ^ 64 by simp [U64.size, U64.numBits], Nat.testBit_mod_two_pow,
    Nat.testBit_mul_two_pow,
    Nat.testBit_two_pow_sub_one]
  by_cases h1 : st.val ≤ i
  · simp [hi, h1]; omega
  · simp [hi, h1]

/-! ## Writes to the bitmap -/

section
variable {th : TypedHeap} {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

theorem apply_eq (s : S) (w p : U64) (set : Bool) :
    ioport.apply st s w p set =
      ok (L.wr s (ioA (L.ksb s) w) (opW set p (L.mem s (ioA (L.ksb s) w)))) := by
  unfold ioport.apply obj.ks_get obj.ks_set
  simp only [word_off_eq, L.ks_base_eq, L.read_eq, L.write_eq, lift, bind_ok]
  cases set <;> rfl

/-- `s'` is `s` with the bitmap words changed by `F` (word index, old
value). -/
def IoW (kb : U64) (s s' : S) (F : Nat → U64 → U64) : Prop :=
  L.ksb s' = L.ksb s ∧ L.cpu s' = L.cpu s ∧ (∀ b, P1.Aligned b → (∀ w : U64, w.val < 1024 → b ≠ ioA kb w) → L.mem s' b = L.mem s b) ∧
  ∀ w : U64, w.val < 1024 → L.mem s' (ioA kb w) = F w.val (L.mem s (ioA kb w))

theorem IoW.refl (kb : U64) (s : S) : IoW (L := L) kb s s (fun _ v => v) := ⟨rfl, rfl, fun _ _ _ => rfl, fun _ _ => rfl⟩

theorem IoW.trans {kb : U64} {s s1 s2 : S} {F F' : Nat → U64 → U64} (h1 : IoW (L := L) kb s s1 F)
    (h2 : IoW (L := L) kb s1 s2 F') (hf : kb.val + 13568 ≤ 2 ^ 64) :
    IoW (L := L) kb s s2 (fun w v => F' w (F w v)) := by
  refine ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, fun b hb hn => by rw [h2.2.2.1 b hb hn, h1.2.2.1 b hb hn],
    fun w hw => ?_⟩
  rw [h2.2.2.2 w hw, h1.2.2.2 w hw]

theorem IoW.congr {kb : U64} {s s' : S} {F F' : Nat → U64 → U64} (h : IoW (L := L) kb s s' F)
    (he : ∀ w, w < 1024 → ∀ v, F w v = F' w v) : IoW (L := L) kb s s' F' :=
  ⟨h.1, h.2.1, h.2.2.1, fun w hw => by rw [h.2.2.2 w hw, he _ hw]⟩

/-- Writing one bitmap word. -/
theorem IoW.wr {kb : U64} (hL : IoLayout th kb) (s : S) (hk : L.ksb s = kb) {w : U64} (hw : w.val < 1024)
    (f : U64 → U64) :
    IoW (L := L) kb s (L.wr s (ioA kb w) (f (L.mem s (ioA kb w)))) (fun w' v => if w' = w.val then f v else v) := by
  have ha := (hL.out w hw).1
  refine ⟨by rw [L.ksb_wr], by rw [L.cpu_wr], fun b hb hn => ?_, fun w' hw' => ?_⟩
  · rw [L.mem_wr _ _ _ _ ha hb, if_neg (fun e => hn w hw e.symm)]
  · rw [L.mem_wr _ _ _ _ ha (hL.out w' hw').1]
    beta_reduce
    by_cases e : w'.val = w.val
    · rw [if_pos (by rw [UScalar.eq_of_val_eq e]), if_pos e, UScalar.eq_of_val_eq e]
    · rw [if_neg (fun h => e ((ioA_eq_iff hL.fit hw hw').1 h).symm), if_neg e]

theorem apply_ioW {kb : U64} (hL : IoLayout th kb) (s : S) (hk : L.ksb s = kb) {w : U64} (hw : w.val < 1024)
    (p : U64) (set : Bool) :
    ioport.apply st s w p set ⦃ s' => IoW (L := L) kb s s' (fun w' v => if w' = w.val then opW set p v else v) ⦄ := by
  rw [apply_eq, hk, WP.spec_ok]
  exact IoW.wr hL s hk hw (opW set p)

/-- **The loop of `set_mask`**: the whole words `w ..< hw`. -/
theorem set_mask_loop_spec {kb : U64} (hL : IoLayout th kb) (s : S) (hk : L.ksb s = kb) (set : Bool)
    (hw w : U64) (hhw : hw.val < 1024) (hle : w.val ≤ hw.val) :
    ioport.set_mask_loop st s set hw w ⦃ s' =>
      IoW (L := L) kb s s' (fun w' v => if w.val ≤ w' ∧ w' < hw.val then opW set core.num.U64.MAX v else v) ⦄ := by
  unfold ioport.set_mask_loop
  apply loop.spec_decr_nat (measure := fun x : S × U64 => hw.val - x.2.val)
    (inv := fun x : S × U64 => w.val ≤ x.2.val ∧ x.2.val ≤ hw.val ∧
      IoW (L := L) kb s x.1 (fun w' v => if w.val ≤ w' ∧ w' < x.2.val then opW set core.num.U64.MAX v else v))
  · rintro ⟨s1, w1⟩ ⟨h1, h2, hI⟩
    unfold ioport.set_mask_loop.body
    simp only
    by_cases hlt : w1 < hw
    · rw [if_pos hlt]
      have hw1 : w1.val < 1024 := by scalar_tac
      refine WP.spec_bind (apply_ioW hL s1 (hI.1.trans hk) hw1 core.num.U64.MAX set) ?_
      intro s2 h2'
      obtain ⟨w2, hw2, hw2v⟩ := spec_exists (U64.add_spec (x := w1) (y := 1#u64) (by scalar_tac))
      rw [hw2]; simp only [bind_ok, WP.spec_ok]
      refine ⟨⟨by scalar_tac, by scalar_tac, ?_⟩, by scalar_tac⟩
      refine (hI.trans h2' hL.fit).congr (fun w' _ v => ?_)
      by_cases e : w' = w1.val
      · subst e; simp only [↓reduceIte, lt_irrefl, and_false]
        rw [if_pos ⟨h1, by scalar_tac⟩]
      · rw [if_neg e]
        by_cases e2 : w.val ≤ w' ∧ w' < w1.val
        · rw [if_pos e2, if_pos ⟨e2.1, by scalar_tac⟩]
        · rw [if_neg e2, if_neg (fun h => e2 ⟨h.1, by scalar_tac⟩)]
    · rw [if_neg hlt, WP.spec_ok]
      have : w1.val = hw.val := by scalar_tac
      rw [this] at hI; exact hI
  · exact ⟨le_refl _, hle, (IoW.refl kb s).congr (fun w' _ v => by
      rw [if_neg (fun h => by simp only at h; omega)])⟩

end

section
variable {th : TypedHeap} {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

theorem shr6_spec (x : U64) : ∃ z, (x >>> 6#i32 : Result U64) = ok z ∧ z.val = x.val / 64 := by
  obtain ⟨z, hz, hzv, -⟩ := spec_exists (U64.ShiftRight_IScalar_spec (x := x) (y := 6#i32) (by decide) (by decide))
  refine ⟨z, hz, ?_⟩
  rw [hzv, Nat.shiftRight_eq_div_pow]; rfl

theorem and63_val (x : U64) : (x &&& 63#u64).val = x.val % 64 := by
  rw [UScalar.val_and]
  have : (63#u64 : U64).val = 2 ^ 6 - 1 := rfl
  rw [this, Nat.and_two_pow_sub_one_eq_mod]

theorem add1_val (x : U64) (h : x.val < 64) : (core.num.U64.wrapping_add x 1#u64).val = x.val + 1 := by
  rw [core.num.U64.wrapping_add_val_eq]; simp [U64.size, U64.numBits]; omega

/-- The bits after `set_mask low high set`. -/
def MaskPost (kb : U64) (low high : U64) (set : Bool) (s s' : S) : Prop :=
  L.ksb s' = L.ksb s ∧ L.cpu s' = L.cpu s ∧ (∀ b, P1.Aligned b → (∀ w : U64, w.val < 1024 → b ≠ ioA kb w) → L.mem s' b = L.mem s b) ∧
  ∀ w : U64, w.val < 1024 → ∀ i, i < 64 →
    (L.mem s' (ioA kb w)).val.testBit i =
      if low.val ≤ 64 * w.val + i ∧ 64 * w.val + i ≤ high.val then set else (L.mem s (ioA kb w)).val.testBit i

/-- **`set_mask low high set`** sets (or clears) the bits of `low ..= high`. -/
theorem set_mask_spec {kb : U64} (hL : IoLayout th kb) (s : S) (hk : L.ksb s = kb) (low high : U64)
    (hlh : low.val ≤ high.val) (hh : high.val < 65536) (set : Bool) :
    ioport.set_mask st s low high set ⦃ s' => MaskPost (L := L) kb low high set s s' ⦄ := by
  unfold ioport.set_mask
  obtain ⟨lw, hlw, hlwv⟩ := shr6_spec low
  obtain ⟨hw, hhw, hhwv⟩ := shr6_spec high
  rw [hlw, hhw]; simp only [lift, bind_ok, and63_val]
  have hli := and63_val low
  have hhi := and63_val high
  by_cases heq : lw = hw
  · rw [if_pos heq]
    have hlwhw : lw.val = hw.val := by rw [heq]
    have hsum := add1_val (high &&& 63#u64) (by rw [hhi]; omega)
    obtain ⟨P, hP, hPb⟩ := pattern_spec (low &&& 63#u64) (core.num.U64.wrapping_add (high &&& 63#u64) 1#u64)
      (by rw [hli]; omega) (by rw [hli, hsum, hhi]; omega) (by rw [hsum, hhi]; omega)
    rw [hP]; simp only [bind_ok]
    have hlw1 : lw.val < 1024 := by omega
    refine WP.spec_mono (apply_ioW hL s hk hlw1 P set) ?_
    intro s' hW
    refine ⟨hW.1, hW.2.1, hW.2.2.1, fun w hwl i hi => ?_⟩
    rw [hW.2.2.2 w hwl]
    beta_reduce
    by_cases e : w.val = lw.val
    · rw [if_pos e, opW_bit set P _ hi, hPb i hi]
      by_cases hc : (low &&& 63#u64).val ≤ i ∧ i < (core.num.U64.wrapping_add (high &&& 63#u64) 1#u64).val
      · have hcond : low.val ≤ 64 * w.val + i ∧ 64 * w.val + i ≤ high.val := by omega
        rw [decide_eq_true hc, if_pos hcond]; simp
      · have hcond : ¬ (low.val ≤ 64 * w.val + i ∧ 64 * w.val + i ≤ high.val) := by omega
        rw [decide_eq_false hc]; simp only [Bool.false_eq_true, ↓reduceIte]; rw [if_neg hcond]
    · have hcond : ¬ (low.val ≤ 64 * w.val + i ∧ 64 * w.val + i ≤ high.val) := by omega
      rw [if_neg e, if_neg hcond]
  · rw [if_neg heq]
    have hlt : lw.val < hw.val := by
      have : lw.val ≤ hw.val := by rw [hlwv, hhwv]; omega
      have : lw.val ≠ hw.val := fun h => heq (UScalar.eq_of_val_eq h)
      omega
    obtain ⟨P1, hP1, hP1b⟩ := pattern_spec (low &&& 63#u64) 64#u64 (by rw [hli]; omega) (by rw [hli]; simp; omega)
      (by simp)
    rw [hP1]; simp only [bind_ok]
    have hlw1 : lw.val < 1024 := by omega
    have hhw1 : hw.val < 1024 := by omega
    refine WP.spec_bind (apply_ioW hL s hk hlw1 P1 set) ?_
    intro s1 hW1
    obtain ⟨w0, hw0, hw0v⟩ := spec_exists (U64.add_spec (x := lw) (y := 1#u64) (by scalar_tac))
    rw [hw0]; simp only [bind_ok]
    refine WP.spec_bind (set_mask_loop_spec hL s1 (hW1.1.trans hk) set hw w0 hhw1 (by scalar_tac)) ?_
    intro s2 hW2
    have hsum := add1_val (high &&& 63#u64) (by rw [hhi]; omega)
    obtain ⟨P2, hP2, hP2b⟩ := pattern_spec 0#u64 (core.num.U64.wrapping_add (high &&& 63#u64) 1#u64)
      (by simp) (by simp) (by rw [hsum, hhi]; omega)
    rw [hP2]; simp only [bind_ok]
    refine WP.spec_mono (apply_ioW hL s2 (hW2.1.trans (hW1.1.trans hk)) hhw1 P2 set) ?_
    intro s' hW3
    have hW := (hW1.trans hW2 hL.fit).trans hW3 hL.fit
    refine ⟨hW.1, hW.2.1, hW.2.2.1, fun w hwl i hi => ?_⟩
    rw [hW.2.2.2 w hwl]
    beta_reduce
    have h0 : (0#u64 : U64).val = 0 := rfl
    have h64 : (64#u64 : U64).val = 64 := rfl
    have h1 : (1#u64 : U64).val = 1 := rfl
    by_cases e3 : w.val = hw.val
    · rw [if_pos e3, opW_bit set P2 _ hi, hP2b i hi]
      have e1 : ¬ w.val = lw.val := by omega
      have e2 : ¬ (w0.val ≤ w.val ∧ w.val < hw.val) := by omega
      rw [if_neg e2, if_neg e1]
      by_cases hc : (0#u64 : U64).val ≤ i ∧ i < (core.num.U64.wrapping_add (high &&& 63#u64) 1#u64).val
      · have hcond : low.val ≤ 64 * w.val + i ∧ 64 * w.val + i ≤ high.val := by omega
        rw [decide_eq_true hc, if_pos hcond]; simp
      · have hcond : ¬ (low.val ≤ 64 * w.val + i ∧ 64 * w.val + i ≤ high.val) := by omega
        rw [decide_eq_false hc]; simp only [Bool.false_eq_true, ↓reduceIte]; rw [if_neg hcond]
    rw [if_neg e3]
    by_cases e2 : w0.val ≤ w.val ∧ w.val < hw.val
    · have hcond : low.val ≤ 64 * w.val + i ∧ 64 * w.val + i ≤ high.val := by omega
      rw [if_pos e2, opW_bit set _ _ hi, max_bit hi, if_pos rfl, if_pos hcond]
    rw [if_neg e2]
    by_cases e1 : w.val = lw.val
    · rw [if_pos e1, opW_bit set P1 _ hi, hP1b i hi]
      by_cases hc : (low &&& 63#u64).val ≤ i ∧ i < (64#u64 : U64).val
      · have hcond : low.val ≤ 64 * w.val + i ∧ 64 * w.val + i ≤ high.val := by omega
        rw [decide_eq_true hc, if_pos hcond]; simp
      · have hcond : ¬ (low.val ≤ 64 * w.val + i ∧ 64 * w.val + i ≤ high.val) := by omega
        rw [decide_eq_false hc]; simp only [Bool.false_eq_true, ↓reduceIte]; rw [if_neg hcond]
    · have hcond : ¬ (low.val ≤ 64 * w.val + i ∧ 64 * w.val + i ≤ high.val) := by omega
      rw [if_neg e1, if_neg hcond]

end

/-! ## `range_free` -/

theorem bitOf_eq {mem : U64 → U64} {kb : U64} {w : U64} (hw : w.val < 1024) {i : Nat} (hi : i < 64) :
    bitOf mem kb (64 * w.val + i) = (mem (ioA kb w)).val.testBit i := by
  unfold bitOf
  have e : wI (64 * w.val + i) = w := UScalar.eq_of_val_eq (by rw [wI_val (by omega)]; omega)
  rw [e, show (64 * w.val + i) % 64 = i by omega]

theorem word_zero_iff (x : U64) : x = 0#u64 ↔ ∀ i, i < 64 → x.val.testBit i = false := by
  have h0 : (0#u64 : U64).val = 0 := rfl
  constructor
  · rintro rfl i _; rw [h0]; exact Nat.zero_testBit i
  · intro h
    apply UScalar.eq_of_val_eq
    apply Nat.eq_of_testBit_eq
    intro i
    rw [h0, Nat.zero_testBit]
    by_cases hi : i < 64
    · rw [h i hi]
    · have hx : x.val < 2 ^ i :=
        lt_of_lt_of_le (show x.val < 2 ^ 64 by scalar_tac) (Nat.pow_le_pow_right (by decide) (by omega))
      rw [Nat.testBit_lt_two_pow hx]

theorem and_zero_iff (x P : U64) :
    (x &&& P) = 0#u64 ↔ ∀ i, i < 64 → P.val.testBit i = true → x.val.testBit i = false := by
  rw [word_zero_iff]
  simp only [UScalar.val_and, Nat.testBit_land, Bool.and_eq_false_iff]
  constructor
  · intro h i hi hp; rcases h i hi with h | h
    · exact h
    · rw [h] at hp; cases hp
  · intro h i hi
    by_cases hp : P.val.testBit i = true
    · exact Or.inl (h i hi hp)
    · exact Or.inr (by simpa using hp)

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

theorem ks_get_io (s : S) (w : U64) :
    (do let i ← ioport.word_off w; obj.ks_get st s i) = ok (L.mem s (ioA (L.ksb s) w)) := by
  simp only [word_off_eq, bind_ok, obj.ks_get, L.ks_base_eq, lift, L.read_eq]; rfl

/-- The loop of `range_free`: the words `w ..< hw` and the low bits of `hw`. -/
theorem range_free_loop_spec (s : S) (hw hi w : U64) (hhw : hw.val < 1024) (hle : w.val ≤ hw.val)
    (hhi : hi.val < 64) :
    ioport.range_free_loop st s hw hi w ⦃ b =>
      b = decide ((∀ w' : U64, w.val ≤ w'.val → w'.val < hw.val → L.mem s (ioA (L.ksb s) w') = 0#u64) ∧
        ∀ i, i ≤ hi.val → (L.mem s (ioA (L.ksb s) hw)).val.testBit i = false) ⦄ := by
  unfold ioport.range_free_loop
  apply loop.spec_decr_nat (measure := fun x : U64 => hw.val - x.val)
    (inv := fun x : U64 => w.val ≤ x.val ∧ x.val ≤ hw.val ∧
      ∀ w' : U64, w.val ≤ w'.val → w'.val < x.val → L.mem s (ioA (L.ksb s) w') = 0#u64)
  · rintro x ⟨h1, h2, hz⟩
    unfold ioport.range_free_loop.body
    have hrd : ∀ w, L.mem s (core.num.U64.wrapping_add (L.ksb s) (ioOff w)) = L.mem s (ioA (L.ksb s) w) :=
      fun _ => rfl
    by_cases hlt : x < hw
    · rw [if_pos hlt]
      simp only [word_off_eq, obj.ks_get, L.ks_base_eq, lift, L.read_eq, bind_ok, hrd]
      by_cases hn : L.mem s (ioA (L.ksb s) x) = 0#u64
      · simp only [hn, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
        obtain ⟨x1, hx1, hx1v⟩ := spec_exists (U64.add_spec (x := x) (y := 1#u64) (by scalar_tac))
        rw [hx1]; simp only [bind_ok, WP.spec_ok]
        refine ⟨⟨by scalar_tac, by scalar_tac, fun w' a b => ?_⟩, by scalar_tac⟩
        by_cases e : w'.val = x.val
        · rw [UScalar.eq_of_val_eq e]; exact hn
        · exact hz w' a (by scalar_tac)
      · have : (L.mem s (ioA (L.ksb s) x) != 0#u64) = true := by simpa using hn
        simp only [this, ↓reduceIte, WP.spec_ok]
        symm; rw [decide_eq_false_iff_not]
        rintro ⟨h, -⟩
        exact hn (h x h1 (by scalar_tac))
    · rw [if_neg hlt]
      have hxe : x = hw := UScalar.eq_of_val_eq (by scalar_tac)
      subst hxe
      simp only [word_off_eq, obj.ks_get, L.ks_base_eq, lift, L.read_eq, bind_ok, hrd]
      have hsum := add1_val hi hhi
      obtain ⟨P, hP, hPb⟩ := pattern_spec 0#u64 (core.num.U64.wrapping_add hi 1#u64) (by simp) (by simp)
        (by rw [hsum]; omega)
      rw [hP]; simp only [bind_ok, WP.spec_ok]
      rw [Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff, and_zero_iff]
      constructor
      · intro h
        refine ⟨hz, fun i hi' => h i (by omega) (by rw [hPb i (by omega)]; simp; scalar_tac)⟩
      · rintro ⟨-, h⟩ i hi' hp
        rw [hPb i hi'] at hp
        simp at hp
        exact h i (by scalar_tac)
  · exact ⟨le_refl _, hle, fun w' a b => absurd b (by omega)⟩

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **`range_free low high`**: the bits of `low ..= high` are clear. -/
theorem range_free_eq (s : S) (low high : U64) (hlh : low.val ≤ high.val) (hh : high.val < 65536) :
    ioport.range_free st s low high ⦃ b =>
      b = decide (∀ p, low.val ≤ p → p ≤ high.val → bitOf (L.mem s) (L.ksb s) p = false) ⦄ := by
  unfold ioport.range_free
  have hrd : ∀ w, L.mem s (core.num.U64.wrapping_add (L.ksb s) (ioOff w)) = L.mem s (ioA (L.ksb s) w) :=
    fun _ => rfl
  obtain ⟨lw, hlw, hlwv⟩ := shr6_spec low
  obtain ⟨hw, hhw, hhwv⟩ := shr6_spec high
  rw [hlw, hhw]; simp only [lift, bind_ok]
  have hli := and63_val low
  have hhi := and63_val high
  have hbit : ∀ p, bitOf (L.mem s) (L.ksb s) p = (L.mem s (ioA (L.ksb s) (wI p))).val.testBit (p % 64) :=
    fun _ => rfl
  by_cases heq : lw = hw
  · rw [if_pos heq]
    have hlwhw : lw.val = hw.val := by rw [heq]
    simp only [word_off_eq, obj.ks_get, L.ks_base_eq, lift, L.read_eq, bind_ok, hrd]
    have hsum := add1_val (high &&& 63#u64) (by rw [hhi]; omega)
    obtain ⟨P, hP, hPb⟩ := pattern_spec (low &&& 63#u64) (core.num.U64.wrapping_add (high &&& 63#u64) 1#u64)
      (by rw [hli]; omega) (by rw [hli, hsum, hhi]; omega) (by rw [hsum, hhi]; omega)
    rw [hP]; simp only [bind_ok, WP.spec_ok]
    rw [Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff, and_zero_iff]
    constructor
    · intro h p h1 h2
      have hwp : wI p = lw := UScalar.eq_of_val_eq (by rw [wI_val (by omega)]; omega)
      rw [hbit, hwp]
      exact h (p % 64) (by omega) (by rw [hPb _ (by omega)]; exact decide_eq_true ⟨by omega, by omega⟩)
    · intro h i hi hp
      rw [hPb i hi] at hp; have hp' := of_decide_eq_true hp
      have := h (64 * lw.val + i) (by omega) (by omega)
      rwa [bitOf_eq (by omega) hi] at this
  · rw [if_neg heq]
    have hlt : lw.val < hw.val := by
      have : lw.val ≤ hw.val := by rw [hlwv, hhwv]; omega
      have : lw.val ≠ hw.val := fun h => heq (UScalar.eq_of_val_eq h)
      omega
    simp only [word_off_eq, obj.ks_get, L.ks_base_eq, lift, L.read_eq, bind_ok, hrd]
    obtain ⟨P1, hP1, hP1b⟩ := pattern_spec (low &&& 63#u64) 64#u64 (by rw [hli]; omega) (by rw [hli]; simp; omega)
      (by simp)
    rw [hP1]; simp only [bind_ok]
    have h64 : (64#u64 : U64).val = 64 := rfl
    by_cases hz1 : (L.mem s (ioA (L.ksb s) lw) &&& P1) = 0#u64
    · have : ((L.mem s (ioA (L.ksb s) lw) &&& P1) != 0#u64) = false := by simpa using hz1
      rw [this]; simp only [Bool.false_eq_true, ↓reduceIte]
      obtain ⟨w0, hw0, hw0v⟩ := spec_exists (U64.add_spec (x := lw) (y := 1#u64) (by scalar_tac))
      rw [hw0]; simp only [bind_ok]
      refine WP.spec_mono (range_free_loop_spec s hw (high &&& 63#u64) w0 (by omega) (by scalar_tac)
        (by rw [hhi]; omega)) ?_
      intro b hb
      rw [hb, Bool.eq_iff_iff]
      simp only [decide_eq_true_eq]
      rw [and_zero_iff] at hz1
      have h1v : (1#u64 : U64).val = 1 := rfl
      constructor
      · rintro ⟨hmid, hlast⟩ p hp1 hp2
        rw [hbit]
        by_cases e1 : p / 64 = lw.val
        · have hwp : wI p = lw := UScalar.eq_of_val_eq (by rw [wI_val (by omega)]; omega)
          rw [hwp]; exact hz1 (p % 64) (by omega) (by rw [hP1b _ (by omega)]; exact decide_eq_true ⟨by omega, by omega⟩)
        by_cases e3 : p / 64 = hw.val
        · have hwp : wI p = hw := UScalar.eq_of_val_eq (by rw [wI_val (by omega)]; omega)
          rw [hwp]; exact hlast _ (by omega)
        · rw [hmid (wI p) (by rw [wI_val (by omega)]; omega) (by rw [wI_val (by omega)]; omega)]
          rw [show (0#u64 : U64).val = 0 from rfl]; exact Nat.zero_testBit _
      · intro h
        refine ⟨fun w' a b => (word_zero_iff _).2 fun i hi => ?_, fun i hi => ?_⟩
        · have := h (64 * w'.val + i) (by omega) (by omega)
          rwa [bitOf_eq (by omega) hi] at this
        · have := h (64 * hw.val + i) (by omega) (by omega)
          rwa [bitOf_eq (by omega) (by omega)] at this
    · have : ((L.mem s (ioA (L.ksb s) lw) &&& P1) != 0#u64) = true := by simpa using hz1
      rw [this]; simp only [↓reduceIte, WP.spec_ok]
      symm; rw [decide_eq_false_iff_not]
      intro h
      apply hz1
      rw [and_zero_iff]
      intro i hi hp
      rw [hP1b i hi] at hp; have hp' := of_decide_eq_true hp
      have := h (64 * lw.val + i) (by omega) (by omega)
      rwa [bitOf_eq (by omega) hi] at this

end

end

end Fl4Proofs.P3
