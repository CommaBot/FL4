/-
P1 (aarch64, gen 40): **the Stage-2 (EPT) typing `S2Ty`** over sized ghost objects, the Stage-2 walks
(`ept.find`, `ept.lookup_slot`, `ept.unmap`, `ept.unmap_table`) and the Stage-2 finalisers, with the A64 P1+ Arch
platform record `ArchPlat` (one [P] field).

Source (crates/fl4-core/src/arch/aarch64/ept.rs, vspace.rs; crates/fl4-arch-aarch64):
* `geom` (ept.rs:42–50): IPA width ≤ 42 → 3 levels, top shift 30, **top mask 1023** (a concatenated 8 KiB level-1
  root); 44 → 4 levels, mask 31; else 4 levels, mask 511. `entry_addr` (57–59): `table + ((ipa >> shift) & mask)·8`;
  `table_of` (61–63): `pptr(e & ADDR_MASK)`; `is_table` (65–67): `shift > 12 ∧ e & 3 = 3`.
* `lookup_slot` (129–140): from `entry_addr(root, ipa, top_shift, top_mask)` with `rem = levels − 1`, each table
  descriptor followed one level down (mask 511, `rem − 1`). `find` (143–150): the ASID's pool entry must carry tag 1
  (`ROOT_S2`), the root is the untagged value.
* `unmap_table` (200–232): the same walk from the root, stopping at the descriptor naming `pt`; that slot written
  `0`. `unmap` (319–334): the slot `lookup_slot` finds written `0` if it is the frame's leaf. Both read the depth
  from `Arch::s2_ipa_bits` of the **current** arch state.
* A Stage-2 VSpace object is retyped with `bits::STAGE2_VSPACE` = 13 (objects.rs:42, arch objects.rs:26,
  fl4-abi consts.rs:98) — 8 KiB for every geometry; Stage-2 page tables are `ArmPageTable` objects of 12 bits
  (objects.rs:37; `ept::map_table` installs a `PageTable` cap, ept.rs:174–197).

**`ArchPlat ar`** — the A64 P1+ Arch platform-interface record. Its one field **`s2_ipa_bits_const`** is a
**[P]** premise: `Arch::s2_ipa_bits` returns one constant at every arch state. Justification:
fl4-arch-aarch64/src/arch.rs:195 (`s2_ipa_bits` is `mmu::s2_ipa_bits()`), mmu.rs:395–428 (`S2_IPA_BITS` computed
once on the boot core from `pa_bits` by `vmid::s2_ipa_bits_for_pa` and cached; before caching the same function of
the same `pa_bits`). Not part of `P0.ArchTotal`; theorems take the record, not the bare fact.

**Sized ghost objects.** A ghost set `Pt` with a size function `bits : U64 → Nat` (P1.Heap's `HKind.other z`
exponent): `PtWb Pt bits` are the aligned words `p + o`, `o < 2^(bits p)`. QueueVsPt's `PtW` is `bits = 12`
(`ptwb_12`). `S2OK Te bits Hr` (state-free): every Stage-2 object has `bits ∈ {12, 13}`, is `2^bits`-aligned, and none
of its words is a `HighVSpace` root's entry-511 word. **`Gran Pt bits`** is only the cover of the sized objects'
words by 4 KiB granules (`ptwb_gran`, `gran_ptwb`), so the loop's 4 KiB word predicate `VsR kb Pt` can carry them;
the typing's objects stay the sized ones (an 8 KiB root is one object of `Te`).

**`S2Ty st n Pp Hr Te Re bits s`** (`n` the IPA-width constant, `s2lv n` levels, `s2rb n` the root span the walk
reaches: 13 for 3 levels, 12 for 4):
* `tag`: a nonzero pool entry is tag 0 with a root outside `Hr`, tag 2 with its root in `Hr`, or **tag 1 with its
  root in `Te`, `Re root + 1 = s2lv n` and `s2rb n ≤ bits root`** (gen 39's `HrTy.tag` with the Stage-2 arm;
  `S2Ty.of_hr`: gen 39's `HrTy` is `Te = ∅`);
* `hi`: `R[511] & 3 = 3` for `R ∈ Hr` (gen 39's `HrTy.hi`);
* `desc`: in a table `p ∈ Te` with `Re p > 0`, a descriptor with `e & 3 = 3` names a table of `Te` with
  `Re + 1 = Re p`.
It reads only pool words, `R + 4088` words and `Te` words; a step zeroing or keeping them and keeping the `R + 4088`
words keeps it (`S2Ty.keep`).

Walks / finalisers (at a `VsTy ∧ S2Ty` state with `ks` base `kb`, `n = hPl.ipa`): `ept.find.ty`,
`ept.lookup_slot_loop.ty` / `ept.lookup_slot.ty` (invariant `EkI`), **`ept.unmap.z`**, `ept.unmap_table_loop.ty`
(invariant `UtI`), **`ept.unmap_table.z`** (`Wr0` steps of `Gran Te bits` words), **`vspace.unmap_page_table.s2`**
(all three branches: Stage-2, `HighVSpace`, Stage-1; `Wr0` of `TbO Tb Hr ∪ Gran Te bits`), `fin_pt.s2`, `fin_pd.s2`,
`fin_pdpt.s2`, **`fin_eframe.s2`** (Stage-2-mapped frames, device or not), **`fin_ept.s2`** (`Ept` caps:
`delete_asid` of the tagged root).

Is `S2Ty` true on reachable states (with `Te` the live Stage-2 roots and the tables mapped below them, `Re` their
remaining depth)? Pool entries: `assign` writes tag 0 / 1 / 2 (vspace.rs:1239–1261; tag 1 only with an unmapped
`Ept` level-0 cap, an 8 KiB `ArmStage2VSpace` object) and `delete_asid` clears; `map_table` (ept.rs:174–197) writes a
table descriptor only into an invalid slot found by `lookup_slot` with `shift ≠ 12` (so `rem > 0`), naming an
unmapped `PageTable` (12-bit) object, one level down; `unmap_table` clears it; leaf descriptors with `e & 3 = 3` sit at
`rem = 0` (shift 12), where `desc` asks nothing; block descriptors have `e & 3 = 1`. `n` is constant by the [P].
A case hypothesis of the deletion's / decode's start state. One new named premise: [P] `ArchPlat.s2_ipa_bits_const`.
-/
import Fl4ProofsA64.P1.QueueHiTy
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

/-! ## The platform record -/

/-- **The A64 P1+ Arch platform-interface record** (module docstring). -/
structure ArchPlat {A : Type _} (ar : machine.Arch A) : Prop where
  /-- **[P]** `Arch::s2_ipa_bits` is one constant at every arch state (fl4-arch-aarch64 arch.rs:195,
  mmu.rs:395–428: computed once on the boot core from `pa_bits` and cached). -/
  s2_ipa_bits_const : ∃ n : U64, ∀ a, ar.s2_ipa_bits a = ok n

/-- The Stage-2 IPA-width constant of the platform. -/
noncomputable def ArchPlat.ipa {A : Type _} {ar : machine.Arch A} (h : ArchPlat ar) : U64 :=
  Classical.choose h.s2_ipa_bits_const

theorem ArchPlat.ipa_eq {A : Type _} {ar : machine.Arch A} (h : ArchPlat ar) (a : A) :
    ar.s2_ipa_bits a = ok h.ipa :=
  Classical.choose_spec h.s2_ipa_bits_const a

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]

local notation "wa" => core.num.U64.wrapping_add

/-! ## Sized ghost objects -/

/-- **An aligned word of a sized object of `Pt`** (`o < 2^(bits p)`). -/
def PtWb (Pt : Set U64) (bits : U64 → Nat) (b : U64) : Prop :=
  ∃ p ∈ Pt, ∃ o : U64, o.val < 2 ^ bits p ∧ o.val % 8 = 0 ∧ b = wa p o

/-- QueueVsPt's 4 KiB `PtW` is `PtWb` at `bits = 12`. -/
theorem ptwb_12 {Pt : Set U64} {b : U64} : PtWb Pt (fun _ => 12) b ↔ PtW Pt b := by
  constructor
  · rintro ⟨p, hp, o, ho, h8, e⟩
    exact ⟨p, hp, o, by simpa using ho, h8, e⟩
  · rintro ⟨p, hp, o, ho, h8, e⟩
    exact ⟨p, hp, o, by simpa using ho, h8, e⟩

/-- **The 4 KiB granules covering the words of the sized objects of `Pt`** (sizes 12 or 13): a word cover only. -/
def Gran (Pt : Set U64) (bits : U64 → Nat) : Set U64 :=
  {q | ∃ p ∈ Pt, q = p ∨ (bits p = 13 ∧ q = wa p 4096#u64)}

theorem pow_bits {k : Nat} (h : k = 12 ∨ k = 13) : 4096 ≤ 2 ^ k ∧ 2 ^ k ≤ 8192 := by
  rcases h with rfl | rfl <;> norm_num

/-- A word of a sized object is a word of its granules. -/
theorem ptwb_gran {Pt : Set U64} {bits : U64 → Nat} (hsz : ∀ p ∈ Pt, bits p = 12 ∨ bits p = 13) {b : U64}
    (hb : PtWb Pt bits b) : PtW (Gran Pt bits) b := by
  obtain ⟨p, hp, o, ho, h8, rfl⟩ := hb
  by_cases hl : o.val < 4096
  · exact ⟨p, ⟨p, hp, Or.inl rfl⟩, o, hl, h8, rfl⟩
  · have h13 : bits p = 13 := by
      rcases hsz p hp with e | e
      · rw [e] at ho; norm_num at ho; omega
      · exact e
    rw [h13] at ho
    norm_num at ho
    have hv : (core.num.U64.wrapping_sub o 4096#u64).val = o.val - 4096 := by
      simp [core.num.U64.wrapping_sub_val_eq, U64.size_def, U64.numBits]; omega
    refine ⟨wa p 4096#u64, ⟨p, hp, Or.inr ⟨h13, rfl⟩⟩, core.num.U64.wrapping_sub o 4096#u64, by omega,
      by omega, ?_⟩
    apply UScalar.eq_of_val_eq
    simp only [core.num.U64.wrapping_add_val_eq, hv]
    simp [U64.size_def, U64.numBits]
    omega

/-- A word of a granule is a word of its sized object. -/
theorem gran_ptwb {Pt : Set U64} {bits : U64 → Nat} (hsz : ∀ p ∈ Pt, bits p = 12 ∨ bits p = 13) {b : U64}
    (hb : PtW (Gran Pt bits) b) : PtWb Pt bits b := by
  obtain ⟨q, ⟨p, hp, hq⟩, o, ho, h8, rfl⟩ := hb
  have hpw := pow_bits (hsz p hp)
  rcases hq with rfl | ⟨h13, rfl⟩
  · exact ⟨q, hp, o, by omega, h8, rfl⟩
  · have hv : (wa 4096#u64 o).val = 4096 + o.val := by
      simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
    refine ⟨p, hp, wa 4096#u64 o, by rw [hv, h13]; norm_num; omega, by rw [hv]; omega, ?_⟩
    apply UScalar.eq_of_val_eq
    simp only [core.num.U64.wrapping_add_val_eq, hv]
    simp [U64.size_def, U64.numBits]
    omega

/-- The words of a union of 4 KiB sets. -/
theorem ptw_union {P Q : Set U64} {b : U64} (h : PtW (P ∪ Q) b) : PtW P b ∨ PtW Q b := by
  obtain ⟨p, hp, o, ho, h8, e⟩ := h
  rcases hp with hp | hp
  · exact Or.inl ⟨p, hp, o, ho, h8, e⟩
  · exact Or.inr ⟨p, hp, o, ho, h8, e⟩

/-- **The placement of the Stage-2 objects** (state-free; module docstring). -/
structure S2OK (Te : Set U64) (bits : U64 → Nat) (Hr : Set U64) : Prop where
  sz : ∀ p ∈ Te, bits p = 12 ∨ bits p = 13
  al : ∀ p ∈ Te, 2 ^ bits p ∣ p.val
  hr : ∀ b, PtWb Te bits b → ∀ R ∈ Hr, b ≠ wa R 4088#u64

/-- The words of an aligned sized object do not wrap. -/
theorem S2OK.val {Te Hr : Set U64} {bits : U64 → Nat} (hS : S2OK Te bits Hr) {p o : U64} (hp : p ∈ Te)
    (ho : o.val < 2 ^ bits p) : (wa p o).val = p.val + o.val := by
  have hd := hS.al p hp
  have hlt : p.val ≤ 18446744073709551615 := by scalar_tac
  rcases hS.sz p hp with e | e <;> rw [e] at hd ho <;> norm_num at hd ho <;>
    simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits] <;> omega

/-! ## The typing -/

/-- The number of Stage-2 levels for the IPA width `n` (`geom`). -/
def s2lv (n : U64) : Nat := if n.val ≤ 42 then 3 else 4

/-- The span (in bits) of a Stage-2 root the walk reaches (`(top_mask + 1)·8`). -/
def s2rb (n : U64) : Nat := if n.val ≤ 42 then 13 else 12

theorem s2lv_ge (n : U64) : 3 ≤ s2lv n := by unfold s2lv; split <;> omega

/-- **The Stage-2 typing at `s`** (module docstring). -/
structure S2Ty (st : machine.Store S) [L : LawfulStore st] (n : U64) (Pp Hr Te : Set U64) (Re bits : U64 → Nat)
    (s : S) : Prop where
  tag : ∀ p ∈ Pp, ∀ o : U64, o.val < 4096 → o.val % 8 = 0 → L.mem s (wa p o) ≠ 0#u64 →
    ((L.mem s (wa p o) &&& 3#u64) = 0#u64 ∧ L.mem s (wa p o) ∉ Hr) ∨
    ((L.mem s (wa p o) &&& 3#u64) = 2#u64 ∧ (L.mem s (wa p o) &&& ~~~3#u64) ∈ Hr) ∨
    ((L.mem s (wa p o) &&& 3#u64) = 1#u64 ∧ (L.mem s (wa p o) &&& ~~~3#u64) ∈ Te ∧
      Re (L.mem s (wa p o) &&& ~~~3#u64) + 1 = s2lv n ∧ s2rb n ≤ bits (L.mem s (wa p o) &&& ~~~3#u64))
  hi : ∀ R ∈ Hr, (L.mem s (wa R 4088#u64) &&& 3#u64) = 3#u64
  desc : ∀ p ∈ Te, 0 < Re p → ∀ o : U64, o.val < 2 ^ bits p → o.val % 8 = 0 →
    (L.mem s (wa p o) &&& 3#u64) = 3#u64 →
    wa (L.mem s (wa p o) &&& ept.ADDR_MASK) layout.PPTR_BASE ∈ Te ∧
      Re (wa (L.mem s (wa p o) &&& ept.ADDR_MASK) layout.PPTR_BASE) + 1 = Re p

/-- Gen 39's `HrTy` is `S2Ty` without Stage-2 objects. -/
theorem S2Ty.of_hr {n : U64} {Pp Hr : Set U64} {Re bits : U64 → Nat} {s : S} (h : HrTy st Pp Hr s) :
    S2Ty st n Pp Hr ∅ Re bits s :=
  ⟨fun p hp o ho h8 hne => (h.tag p hp o ho h8 hne).imp id Or.inl, h.hi, fun _ h => by simp at h⟩

/-- **`S2Ty` along a `VsZ` step keeping the `R + 4088` words** (pools and `Te` granules inside `Pt`). -/
theorem S2Ty.keep {kb n : U64} {Pp Hr Te Pt : Set U64} {Re bits : U64 → Nat} {s s' : S} (hPp : Pp ⊆ Pt)
    (hTe : Gran Te bits ⊆ Pt) (hS : S2OK Te bits Hr) (h : S2Ty st n Pp Hr Te Re bits s)
    (z : VsZ st kb Pt s s') (k : HrW st Hr s s') : S2Ty st n Pp Hr Te Re bits s' := by
  refine ⟨fun p hp o ho h8 hne => ?_, fun R hR => by rw [k R hR]; exact h.hi R hR,
    fun p hp hr o ho h8 h3 => ?_⟩
  · rcases z _ (Or.inl (ptw_mono hPp ⟨p, hp, o, ho, h8, rfl⟩)) with e | e
    · rw [e] at hne ⊢; exact h.tag p hp o ho h8 hne
    · exact absurd e hne
  · rcases z _ (Or.inl (ptw_mono hTe (ptwb_gran hS.sz ⟨p, hp, o, ho, h8, rfl⟩))) with e | e
    · rw [e] at h3 ⊢; exact h.desc p hp hr o ho h8 h3
    · rw [e] at h3; exact absurd h3 (by decide)

/-! ## The Stage-2 walks -/

theorem ept.geom.v (n : U64) :
    ept.geom n ⦃ g => g.levels.val = s2lv n ∧ (g.top_mask.val + 1) * 8 ≤ 2 ^ s2rb n ∧ g.top_mask.val ≤ 1023 ⦄ := by
  unfold ept.geom
  split
  · rename_i h
    have h' : n.val ≤ 42 := by scalar_tac
    refine (WP.spec_ok _).2 ⟨?_, ?_, ?_⟩ <;> simp [s2lv, s2rb, h']
  · rename_i h
    have h' : ¬ n.val ≤ 42 := by scalar_tac
    split <;> (refine (WP.spec_ok _).2 ⟨?_, ?_, ?_⟩ <;> simp [s2lv, s2rb, h'])

/-- **`entry_addr`** with a mask `≤ 1023` is a word of the table at an offset `≤ 8·mask`. -/
theorem ept.entry_addr.off (t v sh m : U64) (hm : m.val ≤ 1023) :
    ept.entry_addr t v sh m ⦃ r => ∃ o : U64, o.val ≤ m.val * 8 ∧ o.val % 8 = 0 ∧ r = wa t o ⦄ := by
  unfold ept.entry_addr
  simp only [lift, bind_ok]
  have h63 : (sh &&& 63#u64).val < 64 := by
    rw [UScalar.val_and]; exact Nat.lt_of_le_of_lt Nat.and_le_right (by simp)
  step as ⟨i1, _⟩
  have ha : (i1 &&& m).val ≤ m.val := by rw [UScalar.val_and]; exact Nat.and_le_right
  have ha' : (i1.val &&& m.val) ≤ m.val := Nat.and_le_right
  have hmv : (core.num.U64.wrapping_mul (i1 &&& m) 8#u64).val = (i1 &&& m).val * 8 := by
    simp [core.num.U64.wrapping_mul_val_eq, U64.size_def, U64.numBits]; omega
  all_goals first
    | exact (WP.spec_ok _).2 ⟨core.num.U64.wrapping_mul (i1 &&& m) 8#u64, by rw [hmv]; omega,
        by rw [hmv]; omega, rfl⟩
    | exact ⟨core.num.U64.wrapping_mul (i1 &&& m) 8#u64, by rw [hmv]; omega, by rw [hmv]; omega, rfl⟩

/-- `ept::is_table e sh = true` only for `e & 3 = 3`. -/
theorem ept.is_table.tag (e sh : U64) :
    ept.is_table e sh ⦃ b => b = true → (e &&& 3#u64) = 3#u64 ⦄ := by
  unfold ept.is_table
  split
  · rw [eq_of_spec_fd P0.Consts.ept.D_VALID.spec, eq_of_spec_fd P0.Consts.ept.D_TABLE_OR_PAGE.spec]
    simp only [lift, bind_ok]
    refine (WP.spec_ok _).2 fun hb => ?_
    have e3 : (1#u64 ||| 2#u64) = 3#u64 := by decide
    rw [e3] at hb
    simpa using hb
  · exact (WP.spec_ok _).2 fun hb => by cases hb

section walk
variable {kb n : U64} {Pp Tb Hr Te : Set U64} {Lv Re bits : U64 → Nat}

set_option maxHeartbeats 2000000 in
/-- **`ept::find` returns a Stage-2 root of `Te`** (depth `s2lv n − 1`, span `≥ s2rb n`). -/
theorem ept.find.ty {s : S} (h : VsTy st kb Pp Tb Lv s) (h2 : S2Ty st n Pp Hr Te Re bits s) (hk : L.ksb s = kb)
    (asid : U64) :
    ept.find st s asid ⦃ r => ∀ r1, r = .Ok r1 → r1 ∈ Te ∧ Re r1 + 1 = s2lv n ∧ s2rb n ≤ bits r1 ⦄ := by
  unfold ept.find
  refine WP.spec_bind (vspace.find_asid_raw.ty h hk asid) fun r hr => ?_
  rcases r with r1 | e
  · obtain ⟨p, hp, o, ho, h8, er, hr0⟩ := hr r1 rfl
    have ht := h2.tag p hp o ho h8 (by rw [← er]; exact hr0)
    rw [← er] at ht
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, lift, rtag, rs2]
    split
    · exact (WP.spec_ok _).2 fun r e => by cases e
    · rename_i h1
      have h1' : (r1 &&& 3#u64) = 1#u64 := by apply UScalar.eq_of_val_eq; simpa using h1
      refine (WP.spec_ok _).2 fun r e => ?_
      cases e
      rcases ht with ⟨e0, -⟩ | ⟨e0, -⟩ | ⟨-, hT, hre, hrb⟩
      · rw [e0] at h1'; exact absurd h1' (by decide)
      · rw [e0] at h1'; exact absurd h1' (by decide)
      · exact ⟨hT, hre, hrb⟩
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok]
    exact (WP.spec_ok _).2 fun r e => by cases e

/-- The loop invariant of `lookup_slot_loop`: the slot is a word of a table of `Te` whose depth is `rem`. -/
abbrev EkI (Te : Set U64) (Re bits : U64 → Nat) (x : U64 × U64 × U64) : Prop :=
  ∃ p ∈ Te, Re p = x.2.2.val ∧ ∃ o : U64, o.val < 2 ^ bits p ∧ o.val % 8 = 0 ∧ x.2.1 = wa p o

set_option maxHeartbeats 2000000 in
/-- **The Stage-2 walk stays in `Te`.** -/
theorem ept.lookup_slot_loop.ty {s : S} (h2 : S2Ty st n Pp Hr Te Re bits s) (hS : S2OK Te bits Hr)
    (ipa shift slot rem : U64) (hi : EkI Te Re bits (shift, slot, rem)) :
    ept.lookup_slot_loop st s ipa shift slot rem ⦃ r => PtWb Te bits r.2 ⦄ := by
  unfold ept.lookup_slot_loop
  apply loop.spec_decr_nat (measure := fun x => x.2.2.val) (inv := EkI Te Re bits)
  · rintro ⟨sh, sl, rm⟩ ⟨p, hp, hre, o, ho, h8, e⟩
    simp only at hre e
    subst e
    dsimp only
    unfold ept.lookup_slot_loop.body
    split
    · rename_i hpos
      have hpos' : 0 < rm.val := by first | simpa using hpos | scalar_tac
      rw [L.read_eq, bind_ok]
      refine WP.spec_bind (ept.is_table.tag _ sh) fun b hb => ?_
      split
      · rename_i hbt
        obtain ⟨hT, hR⟩ := h2.desc p hp (by omega) o ho h8 (hb hbt)
        step as ⟨rm1, hrm1⟩
        simp only [lift, bind_ok, ept.table_of, layout.pptr]
        refine WP.spec_bind (ept.entry_addr.off _ ipa _ 511#u64 (by simp)) fun sl1 ⟨o1, ho1, h81, e1⟩ => ?_
        have hpw := pow_bits (hS.sz _ hT)
        have h511 : (511#u64 : U64).val = 511 := by simp
        rw [h511] at ho1
        refine (WP.spec_ok _).2 ⟨⟨_, hT, ?_, o1, by omega, h81, e1⟩, ?_⟩
        · simp only; omega
        · show rm1.val < rm.val
          omega
      · exact (WP.spec_ok _).2 ⟨p, hp, o, ho, h8, rfl⟩
    · exact (WP.spec_ok _).2 ⟨p, hp, o, ho, h8, rfl⟩
  · exact hi

theorem wsub1_le {x : U64} (h : 1 ≤ x.val) : (core.num.U64.wrapping_sub x 1#u64).val = x.val - 1 := by
  have hx : x.val ≤ 18446744073709551615 := by scalar_tac
  simp [core.num.U64.wrapping_sub_val_eq, U64.size_def, U64.numBits]; omega

/-- **`ept::lookup_slot` from a Stage-2 root of `Te`** finds a word of a `Te` object. -/
theorem ept.lookup_slot.ty {s : S} (h2 : S2Ty st n Pp Hr Te Re bits s) (hS : S2OK Te bits Hr) {root : U64}
    (hr : root ∈ Te) (hre : Re root + 1 = s2lv n) (hrb : s2rb n ≤ bits root) (ipa : U64) :
    ept.lookup_slot st s root ipa n ⦃ lu => PtWb Te bits lu.slot ⦄ := by
  unfold ept.lookup_slot
  refine WP.spec_bind (ept.geom.v n) fun g ⟨hl, hm, hm'⟩ => ?_
  refine WP.spec_bind (ept.entry_addr.off root ipa g.top_shift g.top_mask hm') fun sl ⟨o, ho, h8, e⟩ => ?_
  simp only [lift, bind_ok]
  have h3 := s2lv_ge n
  have hsub := wsub1_le (x := g.levels) (by omega)
  have hpb : 2 ^ s2rb n ≤ 2 ^ bits root := Nat.pow_le_pow_right (by norm_num) hrb
  have hi : EkI Te Re bits (g.top_shift, sl, core.num.U64.wrapping_sub g.levels 1#u64) :=
    ⟨root, hr, by simp only; rw [hsub]; omega, o, by omega, h8, e⟩
  refine WP.spec_bind (ept.lookup_slot_loop.ty h2 hS ipa _ sl _ hi) ?_
  rintro ⟨sh, sl1⟩ hs
  exact (WP.spec_ok _).2 hs

/-- The loop invariant of `unmap_table_loop`: the table is in `Te` with depth `rem`, the mask within its span. -/
abbrev UtI (Te : Set U64) (Re bits : U64 → Nat) (x : U64 × U64 × U64 × U64) : Prop :=
  x.1 ∈ Te ∧ Re x.1 = x.2.2.2.val ∧ (x.2.2.1.val + 1) * 8 ≤ 2 ^ bits x.1 ∧ x.2.2.1.val ≤ 1023

set_option maxHeartbeats 2000000 in
/-- **The `unmap_table` walk stays in `Te`**: a found slot is a word of a `Te` object. -/
theorem ept.unmap_table_loop.ty {s : S} (h2 : S2Ty st n Pp Hr Te Re bits s) (hS : S2OK Te bits Hr)
    (ipa pt table shift mask rem : U64) (hi : UtI Te Re bits (table, shift, mask, rem)) :
    ept.unmap_table_loop st s ipa pt table shift mask rem ⦃ r => ∀ sl, r = some sl → PtWb Te bits sl ⦄ := by
  unfold ept.unmap_table_loop
  apply loop.spec_decr_nat (measure := fun x => x.2.2.2.val) (inv := UtI Te Re bits)
  · rintro ⟨t, sh, m, rm⟩ ⟨ht, hre, hm, hm'⟩
    simp only at ht hre hm hm'
    dsimp only
    unfold ept.unmap_table_loop.body
    split
    · rename_i hpos
      have hpos' : 0 < rm.val := by first | simpa using hpos | scalar_tac
      refine WP.spec_bind (ept.entry_addr.off t ipa sh m hm') fun sl hsl => ?_
      obtain ⟨o, ho, h8, e⟩ := hsl
      subst e
      rw [L.read_eq, bind_ok]
      refine WP.spec_bind (ept.is_table.tag _ sh) fun b hb => ?_
      have hw : PtWb Te bits (wa t o) := ⟨t, ht, o, by omega, h8, rfl⟩
      split
      · rename_i hbt
        obtain ⟨hT', hR'⟩ := h2.desc t ht (by omega) o (by omega) h8 (hb hbt)
        simp only [lift, bind_ok, ept.table_of, layout.pptr]
        split
        · exact (WP.spec_ok _).2 fun sl e' => by cases e'; exact hw
        · try simp only [lift, bind_ok]
          step as ⟨rm1, hrm1⟩
          try simp only [lift, bind_ok]
          try rw [WP.spec_ok]
          try dsimp only
          have hpw := pow_bits (hS.sz _ hT')
          have h511 : (511#u64 : U64).val = 511 := by simp
          refine ⟨hT', ?_, ?_, ?_, ?_⟩
          all_goals first | omega | (simp only [h511]; omega) | (simp only; omega) | simp [h511]
      · exact (WP.spec_ok _).2 fun sl e' => by cases e'
    · exact (WP.spec_ok _).2 fun sl e' => by cases e'
  · exact hi

end walk

/-! ## The Stage-2 writes -/

section wr
variable {A : Type _} {ar : machine.Arch A} {kb : U64} {Pp Tb Hr Te : Set U64} {Lv Re bits : U64 → Nat}

set_option maxHeartbeats 2000000 in
/-- **`ept::unmap`** at a `VsTy ∧ S2Ty` state: unchanged, or a word of a `Te` object written `0`. -/
theorem ept.unmap.z (hA : P0.ArchTotal ar) (hPl : ArchPlat ar) {s : S} (h : VsTy st kb Pp Tb Lv s)
    (h2 : S2Ty st hPl.ipa Pp Hr Te Re bits s) (hS : S2OK Te bits Hr) (hk : L.ksb s = kb) (a : A)
    (asid ipa ptr shift : U64) (it : Bool) :
    ept.unmap st ar s a asid ipa ptr shift it ⦃ r => Wr0 st (Gran Te bits) s r.1 ⦄ := by
  have hS' : P0.StoreTotal st := L.total
  unfold ept.unmap
  refine WP.spec_bind (ept.find.ty h h2 hk asid) fun r hr => ?_
  rcases r with r1 | e
  · obtain ⟨hT, hre, hrb⟩ := hr r1 rfl
    try dsimp only
    rw [hPl.ipa_eq a, bind_ok]
    refine WP.spec_bind (ept.lookup_slot.ty h2 hS hT hre hrb ipa) fun lu hlu => ?_
    split
    · exact (WP.spec_ok _).2 (Wr0.refl _)
    step with LawfulStore.read_spec as ⟨e, _⟩
    refine WP.spec_bind (P0.ept.is_leaf.p0 e lu.shift) fun b _ => ?_
    split
    · refine WP.spec_bind (P0.ept.leaf_base.p0 e lu.shift) fun lb _ => ?_
      refine WP.spec_bind (P0.layout.paddr.p0 ptr) fun pa _ => ?_
      split
      · exact (WP.spec_ok _).2 (Wr0.refl _)
      step with LawfulStore.write_spec as ⟨s1, e1⟩
      refine WP.spec_bind (hA.invalidate_stage2_page a asid ipa) fun a1 _ => ?_
      rw [WP.spec_ok, e1]; exact Or.inr ⟨_, ptwb_gran hS.sz hlu, rfl⟩
    · exact (WP.spec_ok _).2 (Wr0.refl _)
  · exact (WP.spec_ok _).2 (Wr0.refl _)

set_option maxHeartbeats 2000000 in
/-- **`ept::unmap_table`** at a `VsTy ∧ S2Ty` state: unchanged, or a word of a `Te` object written `0`. -/
theorem ept.unmap_table.z (hA : P0.ArchTotal ar) (hPl : ArchPlat ar) {s : S} (h : VsTy st kb Pp Tb Lv s)
    (h2 : S2Ty st hPl.ipa Pp Hr Te Re bits s) (hS : S2OK Te bits Hr) (hk : L.ksb s = kb) (a : A)
    (asid ipa pt : U64) :
    ept.unmap_table st ar s a asid ipa pt ⦃ r => Wr0 st (Gran Te bits) s r.1 ⦄ := by
  have hS' : P0.StoreTotal st := L.total
  unfold ept.unmap_table
  refine WP.spec_bind (ept.find.ty h h2 hk asid) fun r hr => ?_
  rcases r with r1 | e
  · obtain ⟨hT, hre, hrb⟩ := hr r1 rfl
    try dsimp only
    rw [hPl.ipa_eq a, bind_ok]
    refine WP.spec_bind (ept.geom.v hPl.ipa) fun g ⟨hl, hm, hm'⟩ => ?_
    simp only [lift, bind_ok]
    have h3 := s2lv_ge hPl.ipa
    have hsub := wsub1_le (x := g.levels) (by omega)
    have hpb : 2 ^ s2rb hPl.ipa ≤ 2 ^ bits r1 := Nat.pow_le_pow_right (by norm_num) hrb
    have hi : UtI Te Re bits (r1, g.top_shift, g.top_mask, core.num.U64.wrapping_sub g.levels 1#u64) :=
      ⟨hT, by simp only; rw [hsub]; omega, by simp only; omega, hm'⟩
    refine WP.spec_bind (ept.unmap_table_loop.ty h2 hS ipa pt _ _ _ _ hi) fun found hf => ?_
    rcases found with _ | sl
    · exact (WP.spec_ok _).2 (Wr0.refl _)
    · try dsimp only
      step with LawfulStore.write_spec as ⟨s1, e1⟩
      refine WP.spec_bind (hA.invalidate_stage2_vmid a asid) fun a1 _ => ?_
      rw [WP.spec_ok, e1]; exact Or.inr ⟨_, ptwb_gran hS.sz (hf sl rfl), rfl⟩
  · exact (WP.spec_ok _).2 (Wr0.refl _)

set_option maxHeartbeats 4000000 in
/-- **`unmap_page_table` at a `VsTy ∧ S2Ty` state** (all three branches): unchanged, or a word of a Stage-1 table
outside `Hr` or of a Stage-2 object written `0`. -/
theorem vspace.unmap_page_table.s2 (hA : P0.ArchTotal ar) (hPl : ArchPlat ar) (hO : HrOK kb Pp Tb Lv Hr)
    (hS : S2OK Te bits Hr) {s : S} (h0 : VsTy st kb Pp Tb Lv s) (h2 : S2Ty st hPl.ipa Pp Hr Te Re bits s)
    (hk : L.ksb s = kb) (a : A) (asid vaddr pt : U64) :
    vspace.unmap_page_table st ar s a asid vaddr pt ⦃ r => Wr0 st (TbO Tb Hr ∪ Gran Te bits) s r.1 ⦄ := by
  unfold vspace.unmap_page_table
  refine WP.spec_bind (vspace.find_asid_raw.ty h0 hk asid) fun r hr => ?_
  rcases r with r1 | e
  · obtain ⟨p, hp, o, ho, h8, er, hr0⟩ := hr r1 rfl
    have hpl := h0.pool p hp o ho h8 (by rw [← er]; exact hr0)
    have hth := h2.tag p hp o ho h8 (by rw [← er]; exact hr0)
    rw [← er] at hpl hth
    simp only [lift, bind_ok, rtag, rs2, rhigh]
    split
    · exact WP.spec_mono (ept.unmap_table.z hA hPl h0 h2 hS hk a asid vaddr pt) fun r w =>
        Wr0.mono (fun _ h => Or.inr h) w
    · rename_i h1
      have htg : ((r1 &&& 3#u64) = 0#u64 ∧ r1 ∉ Hr) ∨ ((r1 &&& 3#u64) = 2#u64 ∧ (r1 &&& ~~~3#u64) ∈ Hr) := by
        rcases hth with h | h | ⟨e, -⟩
        · exact Or.inl h
        · exact Or.inr h
        · exact absurd e h1
      refine WP.spec_bind (Pₘ := fun x : U64 × U64 × U64 => UpH Tb Hr Lv x) ?_ ?_
      · split
        · rename_i h2'
          have hR : (r1 &&& ~~~3#u64) ∈ Hr := by
            rcases htg with ⟨e0, -⟩ | ⟨-, hR⟩
            · rw [e0] at h2'; exact absurd h2' (by decide)
            · exact hR
          obtain ⟨hrT, hr0'⟩ := hpl.2 h2'
          have he := h2.hi _ hR
          step as ⟨i1, hi1⟩
          have e1 : i1 = 4088#u64 := UScalar.eq_of_val_eq (by scalar_tac)
          subst e1
          simp only [lift, bind_ok, L.read_eq, vspace.table_of, layout.pptr]
          obtain ⟨hT1, hL1⟩ := h0.desc _ hrT (by omega) 4088#u64 (by simp) (by simp) he
          rw [WP.spec_ok]
          have hne : ∀ y ∈ Hr, Lv y ≠ 1 := fun y hy => by rw [hO.lv y hy]; omega
          refine ⟨by simp, fun _ => ⟨hT1, ?_, fun hR' => hne _ hR' (hL1.trans (by rw [hr0']))⟩⟩
          simp only; rw [hL1, hr0']; simp
        · rename_i h2'
          have h0' : (r1 &&& 3#u64) = 0#u64 := by
            rcases htg with ⟨e0, -⟩ | ⟨e0, -⟩
            · exact e0
            · exact absurd e0 h2'
          have hnH : r1 ∉ Hr := by
            rcases htg with ⟨-, hn⟩ | ⟨e2, -⟩
            · exact hn
            · exact absurd e2 h2'
          rw [WP.spec_ok]
          refine ⟨by simp, fun _ => ?_⟩
          simp only
          rw [and_not_of r1 3#u64 h0']
          obtain ⟨hT0, hL0⟩ := hpl.1 h0'
          exact ⟨hT0, by rw [hL0]; simp, hnH⟩
      · rintro ⟨t, sh, lv⟩ hi
        try dsimp only
        refine WP.spec_bind (vspace.unmap_page_table_loop.hr hO h0 vaddr pt t sh lv hi) fun found hf => ?_
        rcases found with _ | sl
        · exact (WP.spec_ok _).2 (Wr0.refl _)
        · try dsimp only
          step with LawfulStore.write_spec as ⟨s1, e1⟩
          split
          · refine WP.spec_bind (hA.invalidate_high_vspace a _) fun a1 _ => ?_
            rw [WP.spec_ok, e1]; exact Or.inr ⟨_, ptw_mono (fun _ h => Or.inl h) (hf sl rfl), rfl⟩
          · refine WP.spec_bind (hA.invalidate_asid a asid) fun a1 _ => ?_
            rw [WP.spec_ok, e1]; exact Or.inr ⟨_, ptw_mono (fun _ h => Or.inl h) (hf sl rfl), rfl⟩
  · exact (WP.spec_ok _).2 (Wr0.refl _)

/-! ## The finalisers -/

/-- **A page-table cap's finalisation** at a `VsTy ∧ S2Ty` state (any finality, mapped or not). -/
theorem fin_pt.s2 (hA : P0.ArchTotal ar) (hPl : ArchPlat ar) (hO : HrOK kb Pp Tb Lv Hr) (hS : S2OK Te bits Hr)
    (s : S) (a : A) (ptr : U64) (mapped : Bool) (asid vaddr : U64) (fin : Bool) (h : VsTy st kb Pp Tb Lv s)
    (h2 : S2Ty st hPl.ipa Pp Hr Te Re bits s) (hk : L.ksb s = kb) :
    objects.finalise_cap_object st ar s a (.PageTable ptr mapped asid vaddr) fin ⦃ r =>
      r.1 = (.Null, .Null) ∧ Wr0 st (TbO Tb Hr ∪ Gran Te bits) s r.2.1 ⦄ := by
  unfold objects.finalise_cap_object
  dsimp only
  split
  · split
    · refine WP.spec_bind (vspace.unmap_page_table.s2 hA hPl hO hS h h2 hk a asid vaddr ptr) ?_
      rintro ⟨s1, a1⟩ w1
      exact (WP.spec_ok _).2 ⟨rfl, w1⟩
    · exact (WP.spec_ok _).2 ⟨rfl, Wr0.refl _⟩
  · exact (WP.spec_ok _).2 ⟨rfl, Wr0.refl _⟩

/-- **A `PageDirectory` cap's finalisation** (as `fin_pt.s2`). -/
theorem fin_pd.s2 (hA : P0.ArchTotal ar) (hPl : ArchPlat ar) (hO : HrOK kb Pp Tb Lv Hr) (hS : S2OK Te bits Hr)
    (s : S) (a : A) (ptr : U64) (mapped : Bool) (asid vaddr : U64) (fin : Bool) (h : VsTy st kb Pp Tb Lv s)
    (h2 : S2Ty st hPl.ipa Pp Hr Te Re bits s) (hk : L.ksb s = kb) :
    objects.finalise_cap_object st ar s a (.PageDirectory ptr mapped asid vaddr) fin ⦃ r =>
      r.1 = (.Null, .Null) ∧ Wr0 st (TbO Tb Hr ∪ Gran Te bits) s r.2.1 ⦄ := by
  unfold objects.finalise_cap_object
  dsimp only
  split
  · split
    · refine WP.spec_bind (Pₘ := fun r : S × A => Wr0 st (TbO Tb Hr ∪ Gran Te bits) s r.1) ?_ ?_
      · unfold vspace.unmap_page_directory; exact vspace.unmap_page_table.s2 hA hPl hO hS h h2 hk a asid vaddr ptr
      rintro ⟨s1, a1⟩ w1
      exact (WP.spec_ok _).2 ⟨rfl, w1⟩
    · exact (WP.spec_ok _).2 ⟨rfl, Wr0.refl _⟩
  · exact (WP.spec_ok _).2 ⟨rfl, Wr0.refl _⟩

/-- **A `Pdpt` cap's finalisation** (as `fin_pt.s2`). -/
theorem fin_pdpt.s2 (hA : P0.ArchTotal ar) (hPl : ArchPlat ar) (hO : HrOK kb Pp Tb Lv Hr) (hS : S2OK Te bits Hr)
    (s : S) (a : A) (ptr : U64) (mapped : Bool) (asid vaddr : U64) (fin : Bool) (h : VsTy st kb Pp Tb Lv s)
    (h2 : S2Ty st hPl.ipa Pp Hr Te Re bits s) (hk : L.ksb s = kb) :
    objects.finalise_cap_object st ar s a (.Pdpt ptr mapped asid vaddr) fin ⦃ r =>
      r.1 = (.Null, .Null) ∧ Wr0 st (TbO Tb Hr ∪ Gran Te bits) s r.2.1 ⦄ := by
  unfold objects.finalise_cap_object
  dsimp only
  split
  · split
    · refine WP.spec_bind (Pₘ := fun r : S × A => Wr0 st (TbO Tb Hr ∪ Gran Te bits) s r.1) ?_ ?_
      · unfold vspace.unmap_pdpt; exact vspace.unmap_page_table.s2 hA hPl hO hS h h2 hk a asid vaddr ptr
      rintro ⟨s1, a1⟩ w1
      exact (WP.spec_ok _).2 ⟨rfl, w1⟩
    · exact (WP.spec_ok _).2 ⟨rfl, Wr0.refl _⟩
  · exact (WP.spec_ok _).2 ⟨rfl, Wr0.refl _⟩

/-- **A Stage-2-mapped frame's finalisation** (device or not, any finality, mapped or not): `ept::unmap`, then a
device frame's `retire_dma_frame` (arch state only). -/
theorem fin_eframe.s2 (hA : P0.ArchTotal ar) (hPl : ArchPlat ar) (hS : S2OK Te bits Hr) (s : S) (a : A)
    (ptr : U64) (size : capability.FrameSize) (rights : U64) (dev mapped : Bool) (asid vaddr : U64) (fin : Bool)
    (h : VsTy st kb Pp Tb Lv s) (h2 : S2Ty st hPl.ipa Pp Hr Te Re bits s) (hk : L.ksb s = kb) :
    objects.finalise_cap_object st ar s a (.Frame ptr size rights dev mapped true asid vaddr) fin ⦃ r =>
      r.1 = (.Null, .Null) ∧ Wr0 st (Gran Te bits) s r.2.1 ⦄ := by
  unfold objects.finalise_cap_object
  dsimp only
  refine WP.spec_bind (Pₘ := fun r : S × A => Wr0 st (Gran Te bits) s r.1) ?_ ?_
  · split
    · split
      · simp only [↓reduceIte]
        refine WP.spec_bind (P0.capability.FrameSize.bits.p0 size) fun sh _ => ?_
        exact ept.unmap.z hA hPl h h2 hS hk a asid vaddr ptr sh false
      · exact (WP.spec_ok _).2 (Wr0.refl _)
    · exact (WP.spec_ok _).2 (Wr0.refl _)
  rintro ⟨s1, a1⟩ w1
  try dsimp only
  cases fin
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact (WP.spec_ok _).2 ⟨rfl, w1⟩
  · cases dev
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact (WP.spec_ok _).2 ⟨rfl, w1⟩
    · simp only [↓reduceIte]
      exact WP.spec_bind (P0.objects.retire_dma_frame.p0 st ar s1 a1 ptr size L.total hA) fun a2 _ =>
        (WP.spec_ok _).2 ⟨rfl, w1⟩

/-- **An `Ept` cap's finalisation** (any level, finality, mapped or not): a final mapped level-0 cap runs
`delete_asid` of its tagged root (ept.rs:167–171), a `Wr0` step of a pool word. -/
theorem fin_ept.s2 (hA : P0.ArchTotal ar) (s : S) (a : A) (ptr lvl : U64) (m : Bool) (asid v : U64) (fin : Bool)
    {Pt : Set U64} (hpool : PtPool st Pt s asid) :
    objects.finalise_cap_object st ar s a (.Ept ptr lvl m asid v) fin ⦃ r =>
      r.1 = (.Null, .Null) ∧ Wr0 st Pt s r.2.1 ⦄ := by
  unfold objects.finalise_cap_object
  dsimp only
  split
  · refine WP.spec_bind (Pₘ := fun r : S × A => Wr0 st Pt s r.1) ?_ ?_
    · unfold ept.finalise
      dsimp only
      split
      · split
        · simp only [lift, bind_ok]
          exact vspace.delete_asid.z hA s a asid _ hpool
        · exact (WP.spec_ok _).2 (Wr0.refl _)
      · exact (WP.spec_ok _).2 (Wr0.refl _)
    · rintro ⟨s1, a1⟩ w1
      exact (WP.spec_ok _).2 ⟨rfl, w1⟩
  · exact (WP.spec_ok _).2 ⟨rfl, Wr0.refl _⟩

end wr

end

end Fl4ProofsA64.P1
