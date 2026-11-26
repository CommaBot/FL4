-- AArch64 port of Fl4Proofs.P1.QueueChoose (proofs/scratch/a64/port.py): the x86_64 text, re-checked
-- over Fl4CoreA64. Edits beyond the renaming are marked `-- a64:`.
/-
P1: `choose_thread`'s bitmap lookup (sched.rs `highest_prio`, seL4
`getHighestPrio`): on a consistent bitmap with a set L1 word it returns the
highest priority whose ready queue is non-empty.
-/
import Fl4ProofsA64.P1.QueueCallers
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

theorem log_lt_64 {x : Nat} (hx : x < 2 ^ 64) : Nat.log 2 x < 64 := by
  by_cases h0 : x = 0
  · subst h0; simp
  · have := Nat.pow_log_le_self 2 h0
    by_contra hc
    have : 2 ^ 64 ≤ 2 ^ Nat.log 2 x := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

@[step] theorem sched.highest_set_bit.spec (w : U64) (hw : w ≠ 0#u64) :
    sched.highest_set_bit w ⦃ r => r.val = Nat.log 2 w.val ⦄ := by
  have hv : w.val ≠ 0 := fun e => hw (UScalar.eq_of_val_eq (by simp [e]))
  have hb : w.val < 2 ^ 64 := by have := w.hBounds; simpa using this
  have hl := log_lt_64 hb
  have hbv : w.bv ≠ 0 := fun e => hv (by
    have : w.val = w.bv.toNat := rfl
    rw [this, e]; rfl)
  unfold sched.highest_set_bit
  simp only [lift, bind_ok, WP.spec_ok]
  have hlz : (core.num.U64.leading_zeros w).val = 64 - Nat.log 2 w.val - 1 := by
    show (BitVec.leadingZeros w.bv : BitVec 32).toNat = _
    rw [BitVec.natCast_eq_ofNat, BitVec.toNat_ofNat]
    unfold BitVec.leadingZeros
    rw [if_neg hbv]
    have : w.bv.toNat = w.val := rfl
    rw [this]
    exact Nat.mod_eq_of_lt (by omega)
  have hc : (UScalar.cast .U64 (core.num.U64.leading_zeros w)).val = 64 - Nat.log 2 w.val - 1 := by
    rw [UScalar.cast_val_eq, hlz]; exact Nat.mod_eq_of_lt (by simp; omega)
  rw [UScalar.val_and, core.num.U64.wrapping_sub_val_eq, hc]
  have : (63#u64).val = 63 := rfl
  rw [this]
  have h2 : (63 + (UScalar.size UScalarTy.U64 - (64 - Nat.log 2 w.val - 1))) % UScalar.size UScalarTy.U64 =
      Nat.log 2 w.val := by
    have : UScalar.size UScalarTy.U64 = 2 ^ 64 := by simp [U64.size_def, U64.numBits]
    rw [this]; omega
  rw [h2]
  have := Nat.and_two_pow_sub_one_eq_mod (Nat.log 2 w.val) 6
  simp only [show (2 : Nat) ^ 6 - 1 = 63 from rfl] at this
  rw [this]; exact Nat.mod_eq_of_lt (by omega)


theorem bit_log {x : Nat} (hx : x ≠ 0) : x.testBit (Nat.log 2 x) = true := by
  rw [← Nat.log2_eq_log_two]; exact Nat.testBit_log2 hx

theorem le_log_of_bit {x i : Nat} (h : x.testBit i = true) : i ≤ Nat.log 2 x := by
  have h2 := Nat.ge_two_pow_of_testBit h
  have hx : x ≠ 0 := by intro e; subst e; simp at h
  rw [← Nat.log2_eq_log_two]; exact (Nat.le_log2 hx).2 h2

theorem bv_bit (w : U64) (i : Nat) : w.bv.getLsbD i = w.val.testBit i := rfl

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}

/-- `highest_prio` finds the highest priority the bitmap marks. -/
theorem sched.highest_prio.spec (s : S) (dom : U64) (NE : U64 → Prop)
    (hN : NodePlaced st T s (L.cpu s)) (hB : BitmapOK st s (L.cpu s) NE) (hne : L.l1W s (L.cpu s) ≠ 0#u64) :
    sched.highest_prio st s dom ⦃ p => p.val < 256 ∧ NE p ∧ ∀ p' : U64, p'.val < 256 → NE p' → p'.val ≤ p.val ⦄ := by
  unfold sched.highest_prio sched.bitmap_dom
  simp only [layout.NUM_DOMAINS, fl4_abi.config.NUM_DOMAINS]
  rw [ite_cond_eq_false _ _ (by simp)]
  step as ⟨cpu, cpu_post⟩
  subst cpu_post
  step as ⟨i, i_post⟩
  subst i_post
  step as ⟨l1, l1_post⟩
  have hl1 : l1 = L.l1W s (L.cpu s) := l1_post
  have hl1ne : l1 ≠ 0#u64 := hl1 ▸ hne
  have hl1v : l1.val ≠ 0 := fun e => hl1ne (UScalar.eq_of_val_eq (by simp [e]))
  have hg64 : Nat.log 2 l1.val < 64 := log_lt_64 (by have := l1.hBounds; simpa using this)
  have hbit : l1.bv.getLsbD (Nat.log 2 l1.val) = true := by rw [bv_bit]; exact bit_log hl1v
  obtain ⟨hg4, hl2ne⟩ := (hB.l1 _ hg64).1 (hl1 ▸ hbit)
  step as ⟨l1i, l1i_post⟩
  step as ⟨i1, i1_post, _⟩
  have hi1 : i1.val = Nat.log 2 l1.val := by
    rw [i1_post, UScalar.val_and, l1i_post]
    have := Nat.and_two_pow_sub_one_eq_mod (Nat.log 2 l1.val) 2
    simp only [show (2 : Nat) ^ 2 - 1 = 3 from rfl] at this
    rw [show (3#u64).val = 3 from rfl, this]; omega
  step as ⟨inv, inv_post, _⟩
  step as ⟨i2, i2_post⟩
  have hi2 : i2 = l2Off (Nat.log 2 l1.val) := by rw [i2_post, l2Off, inv_post, hi1]
  subst hi2
  step as ⟨l2, l2_post⟩
  have hl2 : l2 = L.l2W s (L.cpu s) (Nat.log 2 l1.val) := l2_post
  have hl2ne' : l2 ≠ 0#u64 := hl2 ▸ hl2ne
  have hl2v : l2.val ≠ 0 := fun e => hl2ne' (UScalar.eq_of_val_eq (by simp [e]))
  have hb64 : Nat.log 2 l2.val < 64 := log_lt_64 (by have := l2.hBounds; simpa using this)
  step as ⟨i3, i3_post, _⟩
  step as ⟨i4, i4_post⟩
  have hi3 : i3.val = 64 * Nat.log 2 l1.val := by
    rw [i3_post, l1i_post, Nat.shiftLeft_eq]
    have : U64.size = 2 ^ 64 := by simp [U64.size_def, U64.numBits]
    rw [this]; simp; omega
  have hpv : (i3 ||| i4).val = 64 * Nat.log 2 l1.val + Nat.log 2 l2.val := by
    rw [UScalar.val_or, hi3, i4_post]
    have := Nat.two_pow_add_eq_or_of_lt (i := 6) (b := Nat.log 2 l2.val) (by simpa using hb64) (Nat.log 2 l1.val)
    simp only [show (2 : Nat) ^ 6 = 64 from rfl] at this
    exact this.symm
  have hdiv : (i3 ||| i4).val / 64 = Nat.log 2 l1.val := by rw [hpv]; omega
  have hmod : (i3 ||| i4).val % 64 = Nat.log 2 l2.val := by rw [hpv]; omega
  refine ⟨by rw [hpv]; omega, (hB.l2 _ (by rw [hpv]; omega)).1 ?_, fun p' hp' hne' => ?_⟩
  · rw [hdiv, hmod, ← hl2, bv_bit]; exact bit_log hl2v
  · have hb' := (hB.l2 p' hp').2 hne'
    have hw' : L.l2W s (L.cpu s) (p'.val / 64) ≠ 0#u64 := (ne_zero_iff_bit _).2 ⟨_, by omega, hb'⟩
    have hl1b := (hB.l1 (p'.val / 64) (by omega)).2 ⟨by omega, hw'⟩
    rw [← hl1, bv_bit] at hl1b
    have hle := le_log_of_bit hl1b
    rw [hpv]
    rcases Nat.lt_or_ge (p'.val / 64) (Nat.log 2 l1.val) with hlt | hge
    · omega
    · have he : p'.val / 64 = Nat.log 2 l1.val := by omega
      rw [he, ← hl2, bv_bit] at hb'
      have := le_log_of_bit hb'
      omega

/-- `choose_thread`'s pick (before `switch_to_thread`): with the invariant
and a non-empty L1 word, the thread it switches to is the head of the
highest-priority non-empty ready queue of the current core. -/
theorem choose_thread_pick {Cs : Set U64} (s : S) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hne : L.l1W s (L.cpu s) ≠ 0#u64) :
    (do
      let prio ← sched.highest_prio st s 0#u64
      let i3 ← sched.rq_head_off 0#u64 prio
      let q ← sched.q_get st s (L.cpu s) i3
      ok q.head) ⦃ t => ∃ p : U64, p.val < 256 ∧ t ∈ Q (L.cpu s) p ∧ t = (Q (L.cpu s) p).headD 0#u64 ∧
        ∀ p' : U64, p'.val < 256 → Q (L.cpu s) p' ≠ [] → p'.val ≤ p.val ⦄ := by
  have hN' := h.nodes _ h.cur
  have hRQ := h.ready _ h.cur
  refine WP.spec_bind (sched.highest_prio.spec s 0#u64 _ hN' hRQ.2 hne) ?_
  rintro p ⟨hp, hpne, hmax⟩
  step as ⟨off, off_post, off_post1⟩
  step as ⟨q, q_post⟩
  have hq : q = L.rqQ s (L.cpu s) p := by rw [q_post, off_post1, off_post]; rfl
  have hrel := hRQ.1.rel p hp
  refine ⟨p, hp, ?_, by rw [hq, hrel.head], hmax⟩
  rw [hq, hrel.head]; exact headD_mem hpne _

end

end Fl4ProofsA64.P1
