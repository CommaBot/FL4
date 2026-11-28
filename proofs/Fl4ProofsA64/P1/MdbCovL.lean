/-
P1 (aarch64, gen 60): **the CNode lookup returns a covered slot** (l4v `lookup_slot_for_cnode_op` gives
`ex_cte_cap_wp_to`: the slot found lies in the range of a CNode cap held in the CSpace) — the `CoverA` input of the
CNode decode's destination (`hcd` of `cdt.insert_with_cap.cov` / `cdt.move_cap.cov`).

* **`Held st OS s c`**: `c` is the cap of some `OS` slot at `s`. **`SlotCov st OS s y`**: `y` is a slot index below
  `2 ^ radix` of a CNode cap held in `OS`.
* **`cn_cov`** (arithmetic): a CNode cap `CNode p r g b` whose range does not wrap (`UtInvA.reg`: base ≤ top) covers
  (`CovBy`) each of its slots `slotIdx p i`, `i < 2 ^ r` (the slot fitting below `2 ^ 64`, `OSOK.fit`); both the
  case `r + 5 < 64` (top `p + 2 ^ (r + 5) − 1`) and `r + 5 ≥ 64` (`mask` saturates: then `p = 0`, top `2 ^ 64 − 1`).
  **`SlotCov.cov`**: hence a `SlotCov` slot of `OS` is covered by an `OS` cap, given `UtInvA.reg`.
* **`body_cov`** / **`resolve_cov`** / **`lookup_op_cov`** / **`lookup_tgt_cov`**: gen 30's `body_in` /
  `resolve_in` / `lookup_op_in` (QueueSlotTyDec, merged; not edited) with the root also `Held`: each step's slot is
  `slotIdx ptr (… &&& mask radix)` of the current CNode cap, which is the root or was read from an `OS` slot, so the
  slot found is `SlotCov` (and in `OS`, as before). `body_in` / `resolve_in` / `lookup_op_in` are the
  `Held`-free forms of these (an instance relation the proof-collapse PR can make literal).

No named premise; case hypothesis `Held` of the lookup root (at `decode_invocation` the invoked cap is read from an
`OS` slot).
-/
import Fl4ProofsA64.P1.MdbCovR
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts Fl4Proofs.P3

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {Sg : Set U64}
variable {H : Heap} {Rp Nt : Set U64}

local notation "wa" => core.num.U64.wrapping_add

namespace W7
namespace R
namespace ST

variable {OS : Set U64}

/-- **`c` is held by an `OS` slot** (module docstring). -/
def Held (st : machine.Store S) [L : LawfulStore st] (OS : Set U64) (s : S) (c : capability.Cap) : Prop :=
  ∃ z ∈ OS, capA st s z = c

/-- **`y` is a slot of a CNode cap held by an `OS` slot** (module docstring). -/
def SlotCov (st : machine.Store S) [L : LawfulStore st] (OS : Set U64) (s : S) (y : U64) : Prop :=
  ∃ z ∈ OS, ∃ p r g b, capA st s z = .CNode p r g b ∧ ∃ i : U64, i.val < 2 ^ (r.val % 64) ∧ y = slotIdx p i

theorem physA_cnode (p r g b : U64) : physA (.CNode p r g b) = true := by
  have h := physA_eq (.CNode p r g b); simp only [objects.cap_is_physical] at h; exact (okinj h).symm

set_option maxHeartbeats 1000000 in
/-- **A non-wrapping CNode cap covers its slots** (module docstring). -/
theorem cn_cov {p r g b i : U64} (hreg : baseA (.CNode p r g b) ≤ topA (.CNode p r g b)) (hr : r.val < 64)
    (hi : i.val < 2 ^ (r.val % 64)) (hfit : (slotIdx p i).val + 32 ≤ 2 ^ 64) :
    CovBy (.CNode p r g b) (slotIdx p i) := by
  refine ⟨physA_cnode p r g b, rfl, ?_⟩
  rw [Nat.mod_eq_of_lt hr] at hi
  unfold baseA topA at hreg ⊢
  rw [ptrA_cnode, sizeA_cnode] at hreg ⊢
  have hs5 : (wa r fl4_abi.consts.bits.SLOT).val = r.val + 5 := by
    simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits, fl4_abi.consts.bits.SLOT]; omega
  have hsl : (slotIdx p i).val = (p.val + (i.val * 32) % 2 ^ 64) % 2 ^ 64 := by
    unfold slotIdx
    simp [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq, U64.size_def, U64.numBits]
  have htop : ∀ m : U64, (wa p m).val = (p.val + m.val) % 2 ^ 64 := fun m => by
    simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]
  rw [htop] at hreg ⊢
  rw [hsl] at hfit ⊢
  have hpv : p.val < 2 ^ 64 := by have := p.hBounds; simpa [U64.size_def, U64.numBits] using this
  by_cases hk : r.val + 5 < 64
  · have hm : (mskA (wa r fl4_abi.consts.bits.SLOT)).val = 2 ^ (r.val + 5) - 1 := by
      rw [mskA_val (by omega), hs5]
    rw [hm] at hreg ⊢
    have hK : 2 ^ (r.val + 5) = 2 ^ r.val * 32 := by rw [pow_add]; norm_num
    have hK1 : 2 ^ (r.val + 5) ≤ 2 ^ 63 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h1 : 1 ≤ 2 ^ r.val := Nat.one_le_two_pow
    have hi32 : i.val * 32 + 32 ≤ 2 ^ (r.val + 5) := by rw [hK]; omega
    omega
  · have hge : wa r fl4_abi.consts.bits.SLOT ≥ 64#u64 := by
      show (64#u64 : U64).val ≤ (wa r fl4_abi.consts.bits.SLOT).val
      rw [hs5]; simp; omega
    have hm : mskA (wa r fl4_abi.consts.bits.SLOT) = core.num.U64.MAX := by
      have h := mskA_eq (wa r fl4_abi.consts.bits.SLOT)
      unfold objects.mask at h; rw [if_pos hge] at h; exact (okinj h).symm
    have hmv : (core.num.U64.MAX).val = 2 ^ 64 - 1 := by simp [core.num.U64.MAX, U64.rMax]
    rw [hm, hmv] at hreg ⊢
    omega

/-- **A `SlotCov` slot of `OS` is covered by an `OS` cap** (module docstring). -/
theorem SlotCov.cov (hO : OSOK T Ω Sg OS) {s : S}
    (hreg : ∀ x ∈ OS, physA (capA st s x) = true → baseA (capA st s x) ≤ topA (capA st s x))
    (hrad : ∀ x ∈ OS, ∀ p r g b, capA st s x = .CNode p r g b → r.val < 64)
    {y : U64} (hy : y ∈ OS) (h : SlotCov st OS s y) : ∃ z ∈ OS, CovBy (capA st s z) y := by
  obtain ⟨z, hz, p, r, g, b, hc, i, hi, rfl⟩ := h
  refine ⟨z, hz, ?_⟩
  rw [hc]
  have hg := hreg z hz (by rw [hc]; exact physA_cnode p r g b)
  rw [hc] at hg
  exact cn_cov hg (hrad z hz p r g b hc) hi (hO.fit _ hy)

/-! ## The lookup with the root held -/

set_option hygiene false in
local macro "lf_err" : tactic => `(tactic| first
  | (simp only [WP.spec_ok]; done)
  | (simp only [WP.spec_ok]; intro x hx; cases hx; done)
  | (rw [WP.spec_ok]; intro x hx; cases hx; done)
  | (simp [WP.spec_ok]; done))

set_option maxHeartbeats 4000000 in
/-- **One step of `resolve_address_bits` from a held root** (gen 30's `body_in`, module docstring): a resolved slot is
in `OS` and `SlotCov`; a next CNode cap is a held `RootOK` root. -/
theorem body_cov {s : S} (hT : SlotTy st T Ω Sg H Rp Nt OS s) (cptr : U64) (c : capability.Cap)
    (n fuel : U64) (hc : RootOK OS c) (hh : Held st OS s c) :
    cspace.resolve_address_bits_loop.body st s cptr c n fuel ⦃ r =>
      match r with
      | .done y => ∀ x, y = .Ok x → x.slot ∈ OS ∧ SlotCov st OS s x.slot
      | .cont x' => (RootOK OS x'.1 ∧ Held st OS s x'.1) ∧ x'.2.2.val < fuel.val ⦄ := by
  have hS : P0.StoreTotal st := L.total
  cases c
  case CNode ptr radix gs guard =>
    obtain ⟨hin, hr⟩ := hc
    obtain ⟨z, hz, hzc⟩ := hh
    have hr64 : radix.val < 64 := hr _ _ _ _ rfl
    unfold cspace.resolve_address_bits_loop.body
    step as ⟨level, hlev⟩
    split
    · lf_err
    split
    · lf_err
    rename_i hf
    have hf' : 0 < fuel.val := by
      rcases Nat.eq_zero_or_pos fuel.val with h0 | h0
      · exact absurd (UScalar.eq_of_val_eq (by simp [h0])) hf
      · exact h0
    step as ⟨fuel1, hf1⟩
    step as ⟨i, hi⟩
    step as ⟨shift, hsh⟩
    step as ⟨i1, hi1⟩
    step as ⟨i2, hi2⟩
    step as ⟨g, hg⟩
    split
    · lf_err
    split
    · lf_err
    split
    · lf_err
    step as ⟨i3, hi3⟩
    step as ⟨i4, hi4⟩
    step as ⟨i5, hi5⟩
    step with mask_val as ⟨i6, hi6⟩
    step as ⟨offset, hoff⟩
    step with slot_index_in as ⟨slot, hslot⟩
    have hob : offset.val < 2 ^ (radix.val % 64) := by
      rw [Nat.mod_eq_of_lt hr64, hoff]
      exact and_lt_pow hi6
    have hslotO : slot ∈ OS := by
      rw [hslot]
      exact hin.1 ptr radix gs guard rfl offset hob
    have hsc : SlotCov st OS s slot := ⟨z, hz, ptr, radix, gs, guard, hzc, offset, hob, hslot⟩
    split
    · simp only [WP.spec_ok]; rintro x ⟨⟩; exact ⟨hslotO, hsc⟩
    refine WP.spec_bind (spec_eqv (P0.obj.Slot.cap.p0 st slot s hS)) fun nc hnc' => ?_
    have hnc := hnc'.1
    cases nc
    case CNode p' r' g' b' =>
      rw [WP.spec_ok]
      have hd : capability.Cap.decode (L.mem s slot) (L.mem s (wa slot 8#u64)) = ok (.CNode p' r' g' b') := by
        rw [← DPF.slot_cap_dec]; exact hnc
      have h1 : RootOK OS (.CNode p' r' g' b') :=
        ⟨((hT slot hslotO).1 _ hd).2, fun p r g b e => by cases e; exact decode_rad hd⟩
      have h2 : Held st OS s (.CNode p' r' g' b') := ⟨slot, hslotO, okinj ((capA_eq s slot).symm.trans hnc)⟩
      have h3 : fuel1.val < fuel.val := by omega
      first | exact ⟨⟨h1, h2⟩, h3⟩ | exact ⟨h1, h2, h3⟩
    all_goals (simp only [WP.spec_ok]; rintro x ⟨⟩; exact ⟨hslotO, hsc⟩)
  all_goals (unfold cspace.resolve_address_bits_loop.body; lf_err)

/-- **`resolve_address_bits` from a held `RootOK` root returns a `SlotCov` slot of `OS`.** -/
theorem resolve_cov {s : S} (hT : SlotTy st T Ω Sg H Rp Nt OS s) (c : capability.Cap)
    (hc : RootOK OS c) (hh : Held st OS s c) (cptr n : U64) :
    cspace.resolve_address_bits st s c cptr n ⦃ r => ∀ x, r = .Ok x → x.slot ∈ OS ∧ SlotCov st OS s x.slot ⦄ := by
  unfold cspace.resolve_address_bits cspace.resolve_address_bits_loop
  apply loop.spec_decr_nat (measure := fun x => x.2.2.val) (inv := fun x => RootOK OS x.1 ∧ Held st OS s x.1)
  · rintro ⟨c1, n1, f1⟩ hx
    refine WP.spec_mono (body_cov hT cptr c1 n1 f1 hx.1 hx.2) fun r hr => ?_
    cases r with
    | done y => exact hr
    | cont x' => first | exact hr | exact ⟨⟨hr.1.1, hr.1.2⟩, hr.2⟩ | exact ⟨hr.1.1, hr.1.2, hr.2⟩
  · exact ⟨hc, hh⟩

set_option maxHeartbeats 2000000 in
/-- **The CNode operations' lookup from a held `RootOK` root returns a `SlotCov` slot of `OS`** (gen 51's
`lookup_op_in` with the root held). -/
theorem lookup_op_cov {s : S} (hT : SlotTy st T Ω Sg H Rp Nt OS s) (b0 : Bool) (c : capability.Cap)
    (hc : RootOK OS c) (hh : Held st OS s c) (i d : U64) :
    cspace.lookup_slot_for_cnode_op st s b0 c i d ⦃ r => ∀ x, r = .Ok x → x ∈ OS ∧ SlotCov st OS s x ⦄ := by
  unfold cspace.lookup_slot_for_cnode_op
  refine WP.spec_bind (Pₘ := fun _ => True) (by cases c <;> simp [WP.spec_ok]) fun b _ => ?_
  split
  · split
    · lf_err
    split
    · lf_err
    refine WP.spec_bind (resolve_cov hT c hc hh i d) fun r hr => ?_
    rcases r with r1 | lf
    · dsimp only
      split
      · lf_err
      · rw [WP.spec_ok]; intro x hx; cases hx; exact hr r1 rfl
    · dsimp only
      lf_err
  · lf_err

/-- **The CNode operations' target lookup returns a `SlotCov` slot of `OS`** from a held `RootOK` root. -/
theorem lookup_tgt_cov {s : S} (hT : SlotTy st T Ω Sg H Rp Nt OS s) (c : capability.Cap)
    (hc : RootOK OS c) (hh : Held st OS s c) (i d : U64) :
    cspace.lookup_target_slot st s c i d ⦃ r => ∀ x, r = .Ok x → x ∈ OS ∧ SlotCov st OS s x ⦄ :=
  lookup_op_cov hT false c hc hh i d

end ST
end R
end W7

end

end Fl4ProofsA64.P1
