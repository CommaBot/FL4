/-
P1 (aarch64, gen 42): **the Stage-2 table map (`ept::map_table`) at function level**, the walk's slot depth,
**the zeroed-unmapped-object fact** `UnmZ`, and **ARMPageTableUnmap's `zero(ptr, 4096)`** as a typing-keeping
step — toward discharging gen 41's [J] `SlotTyEntE` (QueueS2Inv) step by step.

* **The walk's depth** (new lemmas; gen 40's `ept.lookup_slot.ty` unchanged): `ept.geom.vs` (gen 40's `geom.v`
  facts and `top_shift = 9·levels + 3`), `EkD` (gen 40's `EkI` and `shift = 9·rem + 12`),
  `ept.lookup_slot_loop.tyD`, **`ept.lookup_slot.tyD`**: the slot found is a word of some `p ∈ Te` with
  `shift = 9·Re p + 12` (ept.rs:129–140: `rem` starts at `levels − 1` with `shift = top_shift`, each step
  `shift − 9`, `rem − 1`; so `Re p > 0` below the page shift and `Re p = 0` at it).
* **The descriptor value** (pure): `tb_M`, `nat_and_M`, `nat_or3`, `nat_or_M`, `s2tab_v`
  (`make_s2_table x` (ept.rs:91–93) has `e & 3 = 3` and `e & ADDR_MASK = x` for a 4 KiB-aligned `x < 2^48`),
  `wa_ws` (`pptr (paddr p) = p`), `wa_sub_of_le`.
* **`S2Pl kb Pp Tb Te bits`** (state-free placement of the Stage-2 objects, a case hypothesis): physical
  addresses 4 KiB-aligned below `2^48`, no Stage-2 word is a pool word, a Stage-1 table word or an ASID-table word,
  and two Stage-2 objects sharing a word are equal. Source: Stage-2 roots / tables are `ArmStage2VSpace` (13 bits) /
  `ArmPageTable` (12 bits) objects of `create_new_objects` (objects.rs:528; arch/aarch64/objects.rs:26/48/55),
  size-aligned, pairwise disjoint and disjoint from the pools (`ASID_POOL` objects) and the ks area; a 12-bit table is
  a Stage-1 table or a Stage-2 table, never both (it is mapped once: `map_table` / ARMPageTableMap need an
  **unmapped** cap, and `derive_cap`, objects.rs:207–231, refuses to copy an unmapped one); every object lies in the
  kernel window over physical memory (layout.rs: `paddr = p − PPTR_BASE`, physical addresses `< 2^48`).
* **`ept.map_table.ty`** (ept.rs:174–197, the whole function at a `VsTy ∧ S2Ty` state with the scheduler invariant
  `SchedQueuesInvX` for the current-thread write and the cap slot in `OS`): the state unchanged (every error
  return), or `ks` kept, `VsTy` kept and `S2Ty` over `insert pt Te` with the depth extended at `pt` (one level below
  the slot's table): `set_thread_state` and `set_cap` keep every `VsR` word (`VsKeep`), the descriptor write is gen
  41's `S2Ty.map_table` / `VsTy.wr`. Case hypotheses: `pt ∉ Te`, `pt`'s words zero, its placement.
* **[case fact] `UnmZ st OS Pt Te bits s`** (goal 2, *the zeroed-unmapped-object facts*): every unmapped
  `PageTable` cap in an `OS` slot names a 4 KiB object of `Pt`, every unmapped level-0 `Ept` cap an 8 KiB object
  whose granules are in `Pt`; their words are zero and are no word of a `Te` object. Source: such an object is made
  by `create_new_objects` zeroed (objects.rs:528 over a reset / `clear_free`d untyped) with its one unmapped cap;
  an unmapped cap cannot be copied (`derive_cap`, objects.rs:207–231), so it is the object's only cap; the
  object's words are written only through a walk that reaches it, i.e. after `map_table` / ARMPageTableMap /
  ASIDPool `Assign` made the cap mapped; ARMPageTableUnmap (vspace.rs:1097–1107) needs a **final** cap, clears the
  walk's slot and **zeroes** the table before writing the cap unmapped; a mapped level-0 `Ept` cap never becomes
  unmapped (only deleted, `ept::finalise`). `UnmZ.pt_of` (what `map_table` needs), **`ept.map_table.tyU`**
  (`map_table.ty` with `pt ∉ Te`, `pt`'s zero words and `pt ∈ Pt` from `UnmZ` and the cap), **`UnmZ.keep`** (kept
  by a step writing only `VsR` words that keeps or zeroes each — every unmap walk, `Wr0` / `VsZ` step), so
  **`ept.unmap.unmz`**, **`ept.unmap_table.unmz`**, **`vspace.unmap_page_table.unmz`**, **`vspace.unmap_page.unmz`**.
* **ASIDPool `Assign` of a Stage-2 root** (goal 1, decode level): **`vspace.decode.assign_s2`** (vspace.rs:1229–1261,
  `vspace.decode`'s `AsidPool` arm with an unmapped level-0 `Ept` cap in the extra slot): the state unchanged, or `ks`,
  `VsTy` kept and `S2Ty` over `insert r0 Te` with the root at depth `s2lv n − 1` (gen 41's `S2Ty.assign1` /
  `VsTy.assign1`; zero root and `r0 ∉ Te` from `UnmZ.ept`; `s2tag_v`: `r0 | ROOT_S2` has tag 1, untagged part `r0`;
  `nat_low2`, `nat_or1_3`, `tb_N`, `nat_or1_n3`). Case hypothesis `hPA` (state-free): pool words are no ASID-table
  words (pools are `ASID_POOL` objects, disjoint from the ks area).
* **Stage-2 leaves** (goal 3): `B1` (bit 1 clear), `B1.or`, `B1.am`, `B1.ne3`, **`ept.make_s2_leaf.b1`**
  (ept.rs:97–117: below the page shift a block descriptor, `e & 2 = 0`, or `0`), `ty_leaf_wr` (a write of a
  non-descriptor at a positive depth, or any value at depth 0, keeps `VsTy ∧ S2Ty`), **`ept.install_s2_leaf.ty`**
  (ept.rs:290–316, break-before-make), **`ept.map_frame.ty`** (ept.rs:236–287, the whole function: unchanged, or
  `ks`, `VsTy`, `S2Ty` kept; the leaf at the slot `lookup_slot.tyD` finds at the frame's shift).
* **ARMPageTableUnmap's zeroing** (vspace.rs:1101–1102): `zr_vsz`, `zr_hrw`, **`zr.ty`**: `zero(ptr, 4096)` of a
  4 KiB-aligned table no `R + 4088` word lies in keeps `VsTy ∧ S2Ty`, writes only `ptr`'s words, and leaves them
  zero.

**Which part of [J] `SlotTyEntE` each covered step now preserves** (its last four fields are `Gran Te bits ⊆ Pt`,
`HrOK`, `S2OK`, `S2Ty`; `VsTy` is one of `SlotTyEntP`'s):
* `ept::map_table`: `VsTy`, `S2Ty` (over `insert pt Te`, depth extended), `ks`; `Gran` / `S2OK` / `HrOK` are
  state-free and carried by the case hypotheses over `insert pt Te`. Not yet: the slot-typing fields (`SlotTy`,
  `VcTy`, apartness) along the cap write — the cap written is a mapped `PageTable` over a slot of `OS`.
* ASIDPool `Assign` with a Stage-2 root: `VsTy`, `S2Ty` (over `insert r0 Te`), `ks`.
* `ept::map_frame` / `install_s2_leaf`: `VsTy`, `S2Ty` (same ghost sets), `ks`.
* the unmap walks (gen 41) and now also `UnmZ` along them.
* `zero(ptr, 4096)` of ARMPageTableUnmap: `VsTy`, `S2Ty` (and `ptr`'s words zero).

**Still owed** (for discharging `SlotTyEntE` from the steps):
* ASIDPool `Assign` of Stage-1 / `HighVSpace` roots (new roots joining `Tb` / `Hr`: `VsTy` / `HrOK` extension);
* `UnmZ` along `map_table` (needs the uniqueness of an unmapped cap and object disjointness of the `Pt` objects as
  facts) and **after ARMPageTableUnmap** (the unmapped table leaves `Te`: needs "a `Te` table has one parent
  descriptor", so that `S2Ty` holds over `Te \ {ptr}`);
* the decode-level ARMPageTableUnmap / Map wrappers (`vspace.decode_page_table`: final-cap check, the cap writes
  through the slot typing);
* the decode-level frame map (`vspace.decode_frame` → `ept::map_frame`: the root from `ept::root`, the cap slot);
  Stage-1 `decode_page_map` / table map / `map_high_page_table` (`VsTy`);
* ASIDControl `MakePool`, `create_new_objects` / untyped reset of the VSpace kinds (new zero objects joining `Pt`,
  establishing `UnmZ`);
* `S2Pl`, `UnmZ` and `hPA` as fields of the entry fact (they are case hypotheses here).

No named premise is new: [P] `ArchPlat.s2_ipa_bits_const` (QueueS2Ty) is consumed via `hPl`; [J] `SlotTyEntE` is
not consumed here. `S2Pl`, `UnmZ` are case hypotheses (definitions, not premises).
-/
import Fl4ProofsA64.P1.QueueS2Inv
import Fl4ProofsA64.P1.CopT
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64}

local notation "wa" => core.num.U64.wrapping_add

namespace W7
namespace R
namespace ST

/-! ## Values -/

theorem tb_M (i : Nat) : (281474976706560 : Nat).testBit i = (decide (12 ≤ i) && decide (i < 48)) := by
  have hM : (281474976706560 : Nat) = (2 ^ 36 - 1) <<< 12 := by
    first | decide | (rw [Nat.shiftLeft_eq]; norm_num)
  rw [hM, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
  by_cases h : 12 ≤ i <;> simp [h] <;> omega

theorem nat_and_M {x : Nat} (h1 : x % 4096 = 0) (h2 : x < 2 ^ 48) : x &&& 281474976706560 = x := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, tb_M i]
  by_cases hi : i < 12
  · have hx : x.testBit i = false := by
      have h := Nat.testBit_mod_two_pow x 12 i
      rw [show x % 2 ^ 12 = 0 by omega, Nat.zero_testBit] at h
      cases hb : x.testBit i
      · rfl
      · rw [hb] at h; simp [hi] at h
    rw [hx]; simp
  · by_cases hj : i < 48
    · simp [show 12 ≤ i by omega, hj]
    · have hx : x.testBit i = false :=
        Nat.testBit_eq_false_of_lt (Nat.lt_of_lt_of_le h2 (Nat.pow_le_pow_right (by norm_num) (by omega)))
      rw [hx]; simp

theorem nat_or3 (y : Nat) : ((y ||| 1) ||| 2) &&& 3 = 3 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_or, Nat.testBit_or]
  rcases (show i = 0 ∨ i = 1 ∨ 2 ≤ i by omega) with rfl | rfl | hi
  · have e1 : Nat.testBit 1 0 = true := by decide
    have e3 : Nat.testBit 3 0 = true := by decide
    simp [e1, e3]
  · have e2 : Nat.testBit 2 1 = true := by decide
    have e3 : Nat.testBit 3 1 = true := by decide
    simp [e2, e3]
  · have h3 : Nat.testBit 3 i = false :=
      Nat.testBit_eq_false_of_lt (Nat.lt_of_lt_of_le (by norm_num : 3 < 2 ^ 2) (Nat.pow_le_pow_right (by norm_num) hi))
    simp [h3]

theorem nat_or_M (y : Nat) : ((y ||| 1) ||| 2) &&& 281474976706560 = y &&& 281474976706560 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_and, Nat.testBit_or, Nat.testBit_or, tb_M i]
  rcases (show i = 0 ∨ i = 1 ∨ 2 ≤ i by omega) with rfl | rfl | hi
  · simp
  · simp
  · have h1 : Nat.testBit 1 i = false :=
      Nat.testBit_eq_false_of_lt (Nat.lt_of_lt_of_le (by norm_num : 1 < 2 ^ 2) (Nat.pow_le_pow_right (by norm_num) hi))
    have h2 : Nat.testBit 2 i = false :=
      Nat.testBit_eq_false_of_lt (Nat.lt_of_lt_of_le (by norm_num : 2 < 2 ^ 2) (Nat.pow_le_pow_right (by norm_num) hi))
    simp [h1, h2]

/-- **`make_s2_table x`** (ept.rs:91–93) of a 4 KiB-aligned `x < 2^48`: a table descriptor (`e & 3 = 3`) whose
address bits are `x`. -/
theorem s2tab_v (x : U64) (h1 : x.val % 4096 = 0) (h2 : x.val < 2 ^ 48) :
    ept.make_s2_table x ⦃ v => (v &&& 3#u64) = 3#u64 ∧ (v &&& ept.ADDR_MASK) = x ⦄ := by
  unfold ept.make_s2_table
  rw [eq_of_spec_fd P0.Consts.ept.D_VALID.spec, eq_of_spec_fd P0.Consts.ept.D_TABLE_OR_PAGE.spec]
  simp only [lift, bind_ok]
  have e1 : ((1#u64 : U64).val) = 1 := rfl
  have e2 : ((2#u64 : U64).val) = 2 := rfl
  have e3 : ((3#u64 : U64).val) = 3 := rfl
  refine (WP.spec_ok _).2 ⟨UScalar.eq_of_val_eq ?_, UScalar.eq_of_val_eq ?_⟩
  · simp only [UScalar.val_and, UScalar.val_or, e1, e2, e3]
    exact nat_or3 _
  · simp only [UScalar.val_and, UScalar.val_or, ept.ADDR_MASK.val_eq, e1, e2]
    rw [nat_or_M, nat_and_M h1 h2, nat_and_M h1 h2]

/-- `pptr (paddr p) = p`. -/
theorem wa_ws (p b : U64) : wa (core.num.U64.wrapping_sub p b) b = p := by
  apply UScalar.eq_of_val_eq
  have hp : p.val ≤ 18446744073709551615 := by scalar_tac
  have hb : b.val ≤ 18446744073709551615 := by scalar_tac
  simp [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_sub_val_eq, U64.size_def, U64.numBits]
  omega

/-- `p + (b − p) = b` for `p ≤ b`. -/
theorem wa_sub_of_le {p b : U64} (h : p.val ≤ b.val) :
    wa p (core.num.U64.wrapping_sub b p) = b ∧ (core.num.U64.wrapping_sub b p).val = b.val - p.val := by
  have hpv : p.val ≤ 18446744073709551615 := by scalar_tac
  have hbv : b.val ≤ 18446744073709551615 := by scalar_tac
  have hv : (core.num.U64.wrapping_sub b p).val = b.val - p.val := by
    simp [core.num.U64.wrapping_sub_val_eq, U64.size_def, U64.numBits]; omega
  refine ⟨UScalar.eq_of_val_eq ?_, hv⟩
  simp only [core.num.U64.wrapping_add_val_eq, hv]
  simp [U64.size_def, U64.numBits]
  omega

/-! ## The walk's depth -/

theorem ept.geom.vs (n : U64) :
    ept.geom n ⦃ g => g.levels.val = s2lv n ∧ (g.top_mask.val + 1) * 8 ≤ 2 ^ s2rb n ∧ g.top_mask.val ≤ 1023 ∧
      g.top_shift.val = 9 * s2lv n + 3 ⦄ := by
  unfold ept.geom
  split
  · rename_i h
    have h' : n.val ≤ 42 := by scalar_tac
    refine (WP.spec_ok _).2 ⟨?_, ?_, ?_, ?_⟩ <;> simp [s2lv, s2rb, h']
  · rename_i h
    have h' : ¬ n.val ≤ 42 := by scalar_tac
    split <;> (refine (WP.spec_ok _).2 ⟨?_, ?_, ?_, ?_⟩ <;> simp [s2lv, s2rb, h'])

/-- The loop invariant of `lookup_slot_loop` with the shift: `EkI` and `shift = 9·rem + 12`. -/
abbrev EkD (Te : Set U64) (Re bits : U64 → Nat) (x : U64 × U64 × U64) : Prop :=
  EkI Te Re bits x ∧ x.1.val = 9 * x.2.2.val + 12

section walk
variable {n : U64} {Pp Hr Te : Set U64} {Re bits : U64 → Nat}

set_option maxHeartbeats 2000000 in
/-- **The Stage-2 walk stays in `Te`, with its depth**: the slot's table has `Re p` with `shift = 9·Re p + 12`
(so `Re p > 0` below the last level, `Re p = 0` at the page shift). -/
theorem ept.lookup_slot_loop.tyD {s : S} (h2 : S2Ty st n Pp Hr Te Re bits s) (hS : S2OK Te bits Hr)
    (ipa shift slot rem : U64) (hi : EkD Te Re bits (shift, slot, rem)) :
    ept.lookup_slot_loop st s ipa shift slot rem ⦃ r => ∃ p ∈ Te, ∃ o : U64, o.val < 2 ^ bits p ∧
      o.val % 8 = 0 ∧ r.2 = wa p o ∧ r.1.val = 9 * Re p + 12 ⦄ := by
  unfold ept.lookup_slot_loop
  apply loop.spec_decr_nat (measure := fun x => x.2.2.val) (inv := EkD Te Re bits)
  · rintro ⟨sh, sl, rm⟩ ⟨⟨p, hp, hre, o, ho, h8, e⟩, hsh⟩
    simp only at hre e hsh
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
        have hsub : (core.num.U64.wrapping_sub sh 9#u64).val = sh.val - 9 := by
          have hx : sh.val ≤ 18446744073709551615 := by scalar_tac
          simp [core.num.U64.wrapping_sub_val_eq, U64.size_def, U64.numBits]; omega
        have hI : EkI Te Re bits (core.num.U64.wrapping_sub sh 9#u64, sl1, rm1) :=
          ⟨_, hT, by first | omega | (simp only; omega), o1, by omega, h81, e1⟩
        have hE : (core.num.U64.wrapping_sub sh 9#u64).val = 9 * rm1.val + 12 := by rw [hsub]; omega
        have hlt : rm1.val < rm.val := by omega
        have hD : EkD Te Re bits (core.num.U64.wrapping_sub sh 9#u64, sl1, rm1) := And.intro hI hE
        first
          | exact (WP.spec_ok _).2 ⟨hI, hE, hlt⟩
          | exact (WP.spec_ok _).2 (And.intro hD hlt)
      · exact (WP.spec_ok _).2 ⟨p, hp, o, ho, h8, rfl, by first | omega | (simp only; omega)⟩
    · exact (WP.spec_ok _).2 ⟨p, hp, o, ho, h8, rfl, by first | omega | (simp only; omega)⟩
  · exact hi

/-- **`ept::lookup_slot` from a Stage-2 root of `Te`** finds a word of some `p ∈ Te` with
`shift = 9·Re p + 12` (gen 40's `ept.lookup_slot.ty` with the depth). -/
theorem ept.lookup_slot.tyD {s : S} (h2 : S2Ty st n Pp Hr Te Re bits s) (hS : S2OK Te bits Hr) {root : U64}
    (hr : root ∈ Te) (hre : Re root + 1 = s2lv n) (hrb : s2rb n ≤ bits root) (ipa : U64) :
    ept.lookup_slot st s root ipa n ⦃ lu => ∃ p ∈ Te, ∃ o : U64, o.val < 2 ^ bits p ∧ o.val % 8 = 0 ∧
      lu.slot = wa p o ∧ lu.shift.val = 9 * Re p + 12 ⦄ := by
  unfold ept.lookup_slot
  refine WP.spec_bind (ept.geom.vs n) fun g ⟨hl, hm, hm', hsh⟩ => ?_
  refine WP.spec_bind (ept.entry_addr.off root ipa g.top_shift g.top_mask hm') fun sl ⟨o, ho, h8, e⟩ => ?_
  simp only [lift, bind_ok]
  have h3 := s2lv_ge n
  have hsub := wsub1_le (x := g.levels) (by omega)
  have hpb : 2 ^ s2rb n ≤ 2 ^ bits root := Nat.pow_le_pow_right (by norm_num) hrb
  have hi : EkD Te Re bits (g.top_shift, sl, core.num.U64.wrapping_sub g.levels 1#u64) :=
    ⟨⟨root, hr, by simp only; rw [hsub]; omega, o, by omega, h8, e⟩, by simp only; rw [hsub]; omega⟩
  refine WP.spec_bind (ept.lookup_slot_loop.tyD h2 hS ipa _ sl _ hi) ?_
  rintro ⟨sh, sl1⟩ hs
  exact (WP.spec_ok _).2 hs

end walk

/-! ## Placement of the Stage-2 objects -/

theorem ptwb_mono {Te Te' : Set U64} {bits : U64 → Nat} (h : Te ⊆ Te') {b : U64} (hb : PtWb Te bits b) :
    PtWb Te' bits b := by
  obtain ⟨p, hp, o, ho, h8, e⟩ := hb
  exact ⟨p, h hp, o, ho, h8, e⟩

theorem gran_mono {Te Te' : Set U64} {bits : U64 → Nat} (h : Te ⊆ Te') : Gran Te bits ⊆ Gran Te' bits := by
  rintro q ⟨p, hp, hq⟩
  exact ⟨p, h hp, hq⟩

theorem S2OK.sub {Te Te' Hr : Set U64} {bits : U64 → Nat} (hS : S2OK Te' bits Hr) (h : Te ⊆ Te') :
    S2OK Te bits Hr :=
  ⟨fun p hp => hS.sz p (h hp), fun p hp => hS.al p (h hp), fun b hb => hS.hr b (ptwb_mono h hb)⟩

/-- **The Stage-2 objects' placement against the pools, the Stage-1 tables and the ASID table** (state-free;
module docstring for the source). -/
structure S2Pl (kb : U64) (Pp Tb Te : Set U64) (bits : U64 → Nat) : Prop where
  pa : ∀ p ∈ Te, (core.num.U64.wrapping_sub p layout.PPTR_BASE).val % 4096 = 0 ∧
    (core.num.U64.wrapping_sub p layout.PPTR_BASE).val < 2 ^ 48
  pp : ∀ b, PtWb Te bits b → ¬ PtW Pp b
  tb : ∀ b, PtWb Te bits b → ¬ PtW Tb b
  asw : ∀ b, PtWb Te bits b → ¬ AsW kb b
  un : ∀ p ∈ Te, ∀ q ∈ Te, ∀ o o' : U64, o.val < 2 ^ bits p → o.val % 8 = 0 → o'.val < 2 ^ bits q →
    o'.val % 8 = 0 → wa q o' = wa p o → q = p

/-! ## `ept::map_table` -/

set_option hygiene false in
/-- An error return of `map_table` (the state unchanged). -/
macro "mtErr" : tactic => `(tactic| first
  | exact (WP.spec_ok _).2 (Or.inl rfl)
  | (simp only [error.invalid_arg, bind_ok]; exact (WP.spec_ok _).2 (Or.inl rfl)))

section mt
variable {OS Vc Ub : Set U64} {kb : U64} {Pp Tb Pt Hr Te : Set U64} {Lv Re bits : U64 → Nat}
variable {A : Type _} {ar : machine.Arch A}

/-- `set_thread_state` of a thread keeps every `VsR` word (its `STATE` word and the core's `SCHED_ACTION` are
outside `Ω`'s other-object words). -/
theorem stt_vk (hR : VrOK Ω Sg Scs Z OS Vc Ub kb Pt) {X : Set U64} {Q : U64 → U64 → List U64}
    {Rq : U64 → List U64} {s : S} (q : SchedQueuesInvX st T Cs Ω H X s Q Rq) {t v : U64} (ht : t ∈ T) :
    sched.set_thread_state st s t v ⦃ s1 => WritesIn st s s1
      (fun b => b = stA t ∨ b = L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION) ∧ VsKeep st kb Pt s s1 ⦄ := by
  refine WP.spec_mono (sched.set_thread_state.vckW2 s t v q.tcbs (q.nodes _ q.cur) ht) fun s1 hw1 => ?_
  refine ⟨hw1.1, VsKeep.of_w hR.al hw1.1 fun b hb hF => ?_⟩
  have ho' := q.omega _ (hR.om b hb)
  rcases hF with e | e
  · exact out_ne_field (K := 3328#u64) ho' ht (q.tcbs t ht) (by simp) (by rw [← stA_eq, ← e])
  · exact out_ne_node ho' q.cur (q.nodes _ q.cur) (o := layout.node.SCHED_ACTION)
      (by simp [layout.node.SCHED_ACTION]) (by rw [e])

set_option maxHeartbeats 4000000 in
/-- **`ept::map_table` keeps `VsTy` and extends `S2Ty` by the new table** (ept.rs:174–197; module docstring):
the state unchanged, or `ks` kept, `VsTy` kept and `S2Ty` over `insert pt Te` with the depth set at `pt`. -/
theorem ept.map_table.ty (hPl : ArchPlat ar) (hR : VrOK Ω Sg Scs Z OS Vc Ub kb Pt) (hO : OSOK T Ω Sg OS)
    {X : Set U64} {Q : U64 → U64 → List U64} {Rq : U64 → List U64} {s : S}
    (q : SchedQueuesInvX st T Cs Ω H X s Q Rq) (hk : L.ksb s = kb) (hPp : Pp ⊆ Pt) (hTb : Tb ⊆ Pt)
    {pt : U64} (hpt : pt ∉ Te) (hTe : Gran (insert pt Te) bits ⊆ Pt) (hH : HrOK kb Pp Tb Lv Hr)
    (hS : S2OK (insert pt Te) bits Hr) (hD : S2Pl kb Pp Tb (insert pt Te) bits)
    (hY : VsTy st kb Pp Tb Lv s) (h2 : S2Ty st hPl.ipa Pp Hr Te Re bits s)
    (hz : ∀ o : U64, o.val < 2 ^ bits pt → o.val % 8 = 0 → L.mem s (wa pt o) = 0#u64)
    {root : U64} (hr : root ∈ Te) (hre : Re root + 1 = s2lv hPl.ipa) (hrb : s2rb hPl.ipa ≤ bits root)
    (a : A) (asid ipa : U64) {slot : U64} (hsl : slot ∈ OS) :
    ept.map_table st ar s a root asid ipa pt slot ⦃ r => r.2.1 = s ∨ (L.ksb r.2.1 = kb ∧
      VsTy st kb Pp Tb Lv r.2.1 ∧ ∃ Re' : U64 → Nat, (∀ p ∈ Te, Re' p = Re p) ∧
        S2Ty st hPl.ipa Pp Hr (insert pt Te) Re' bits r.2.1) ⦄ := by
  have hsub : Te ⊆ insert pt Te := Set.subset_insert _ _
  have hS0 : S2OK Te bits Hr := S2OK.sub hS hsub
  have hTe0 : Gran Te bits ⊆ Pt := (gran_mono hsub).trans hTe
  unfold ept.map_table
  rw [hPl.ipa_eq a, bind_ok]
  refine WP.spec_bind (P0.ept.ipa_limit.p0 _) fun _ _ => ?_
  refine spec_ite (fun _ => by mtErr) (fun _ => ?_)
  refine WP.spec_bind (ept.lookup_slot.tyD h2 hS0 hr hre hrb ipa) fun lu hlu => ?_
  obtain ⟨p, hp, o, ho, h8, hsl', hpos⟩ := hlu
  refine spec_ite (fun _ => by mtErr) (fun hne => ?_)
  have hRp : 0 < Re p := by
    have : lu.shift.val ≠ 12 := fun h => hne (UScalar.eq_of_val_eq (by rw [h]; simp))
    omega
  refine WP.spec_bind (LawfulStore.read_spec s lu.slot) fun _ _ => ?_
  refine WP.spec_bind P0.ept.D_VALID.p0 fun _ _ => ?_
  try simp only [lift, bind_ok]
  refine spec_ite (fun _ => by mtErr) (fun _ => ?_)
  refine WP.spec_bind (shl_and63u _) fun _ _ => ?_
  try simp only [lift, bind_ok]
  refine WP.spec_bind (sched.cur_thread.spec s) fun ct ect => ?_
  have hct : ct ∈ T := by rw [ect]; exact q.curT
  refine WP.spec_bind (stt_vk hR q hct) fun s1 ⟨w1, k1⟩ => ?_
  refine WP.spec_bind (W7.obj.Slot.set_cap.capw (s := s1) (osw hO hsl)) fun s2 w2 => ?_
  have k12 : VsKeep st kb Pt s s2 := k1.trans (vsk_cw q hR w2)
  have hk2 : L.ksb s2 = kb := by rw [w2.1, w1.1, hk]
  refine WP.spec_bind (show layout.paddr pt ⦃ x => x = core.num.U64.wrapping_sub pt layout.PPTR_BASE ⦄ by
    unfold layout.paddr; exact (WP.spec_ok _).2 rfl) fun x ex => ?_
  subst ex
  have hpa := hD.pa pt (Set.mem_insert _ _)
  refine WP.spec_bind (s2tab_v _ hpa.1 hpa.2) fun v ⟨_, hvm⟩ => ?_
  refine WP.spec_bind (LawfulStore.write_spec s2 lu.slot v) fun s3 e3 => ?_
  subst e3
  rw [hsl']
  have hpi : p ∈ insert pt Te := hsub hp
  have hw : PtWb (insert pt Te) bits (wa p o) := ⟨p, hpi, o, ho, h8, rfl⟩
  have hal : Aligned (wa p o) := hR.al _ (Or.inl (ptw_mono hTe (ptwb_gran hS.sz hw)))
  have hY2 : VsTy st kb Pp Tb Lv s2 := hY.keepZ hPp hTb (VsKeep.vsz k12)
  have h22 : S2Ty st hPl.ipa Pp Hr Te Re bits s2 :=
    h2.keep hPp hTe0 hS0 (VsKeep.vsz k12) fun R hR' => k12 _ (hr_vsr hTb hH hR')
  have hpp : p ≠ pt := fun e => hpt (by rw [← e]; exact hp)
  have hRe : ∀ q ∈ Te, Function.update Re pt (Re p - 1) q = Re q :=
    fun q hq => Function.update_of_ne (fun e => hpt (by rw [← e]; exact hq)) _ _
  refine (WP.spec_ok _).2 (Or.inr ⟨by rw [L.ksb_wr]; exact hk2, ?_, Function.update Re pt (Re p - 1), hRe, ?_⟩)
  · exact VsTy.wr hR.al hPp hTb hal hY2
      (fun o' h1 h2 h8' e _ => (hD.asw _ hw ⟨o', h1, h2, h8', e.symm⟩).elim)
      (fun q hq o' ho' h8' e _ => (hD.pp _ hw ⟨q, hq, o', ho', h8', e.symm⟩).elim)
      (fun q hq _ o' ho' h8' e _ => (hD.tb _ hw ⟨q, hq, o', ho', h8', e.symm⟩).elim)
  · refine S2Ty.map_table hR.al hPp hTe hS (fun R hR' => hR.al _ (hr_vsr hTb hH hR'))
      (S2Ty.congr h22 hRe fun _ _ => rfl) hp ho h8
      (fun q hq o' ho' h8' e => hD.un p hpi q hq o o' ho h8 ho' h8' e)
      (fun q hq o' ho' h8' e => hD.pp _ hw ⟨q, hq, o', ho', h8', e.symm⟩) ?_ ?_ ?_
    · rw [Function.update_self, Function.update_of_ne hpp]; omega
    · intro _ o' ho' h8' h3
      rw [k12 _ (Or.inl (ptw_mono hTe (ptwb_gran hS.sz ⟨pt, Set.mem_insert _ _, o', ho', h8', rfl⟩))),
        hz o' ho' h8'] at h3
      exact absurd h3 (by decide)
    · rw [hvm]; exact wa_ws pt layout.PPTR_BASE

end mt

/-! ## The zeroed-unmapped-object facts -/

/-- **[case fact] Unmapped `PageTable` / level-0 `Ept` caps name zero objects outside `Te`** (module docstring for
the source): the object's words (4 KiB, resp. 8 KiB) are `VsR` words (`Pt`), zero, and no word of a `Te` object. -/
structure UnmZ (st : machine.Store S) [L : LawfulStore st] (OS Pt Te : Set U64) (bits : U64 → Nat) (s : S) :
    Prop where
  pt : ∀ x ∈ OS, ∀ p asid v, obj.Slot.cap st x s = ok (.PageTable p false asid v) →
    p ∈ Pt ∧ ∀ o : U64, o.val < 4096 → o.val % 8 = 0 → ¬ PtWb Te bits (wa p o) ∧ L.mem s (wa p o) = 0#u64
  ept : ∀ x ∈ OS, ∀ p asid v, obj.Slot.cap st x s = ok (.Ept p 0#u64 false asid v) →
    Gran {p} (fun _ => 13) ⊆ Pt ∧
      ∀ o : U64, o.val < 8192 → o.val % 8 = 0 → ¬ PtWb Te bits (wa p o) ∧ L.mem s (wa p o) = 0#u64

section unmz
variable {OS Vc Ub : Set U64} {kb : U64} {Pp Tb Pt Hr Te Te' : Set U64} {Lv Re bits : U64 → Nat}
variable {A : Type _} {ar : machine.Arch A}

/-- What `map_table` needs of the table it maps, from `UnmZ` and its unmapped cap. -/
theorem UnmZ.pt_of {s : S} (hU : UnmZ st OS Pt Te bits s) {x pt asid v : U64} (hx : x ∈ OS)
    (hc : obj.Slot.cap st x s = ok (.PageTable pt false asid v)) (h12 : bits pt = 12) :
    pt ∈ Pt ∧ pt ∉ Te ∧ ∀ o : U64, o.val < 2 ^ bits pt → o.val % 8 = 0 → L.mem s (wa pt o) = 0#u64 := by
  obtain ⟨hp, hf⟩ := hU.pt x hx pt asid v hc
  refine ⟨hp, fun hT => (hf 0#u64 (by simp) (by simp)).1 ⟨pt, hT, 0#u64, ?_, by simp, rfl⟩,
    fun o ho h8 => (hf o (by rw [h12] at ho; simpa using ho) h8).2⟩
  have := @Nat.one_le_two_pow (bits pt)
  simpa using Nat.lt_of_lt_of_le Nat.zero_lt_one this

/-- **`ept::map_table` from `UnmZ`**: `map_table.ty` with `pt ∉ Te`, `pt`'s zero words and `pt ∈ Pt` taken from
`UnmZ` and the slot's unmapped `PageTable` cap (ARMPageTableMap passes that cap's object, vspace.rs:1117–1135). -/
theorem ept.map_table.tyU (hPl : ArchPlat ar) (hR : VrOK Ω Sg Scs Z OS Vc Ub kb Pt) (hO : OSOK T Ω Sg OS)
    {X : Set U64} {Q : U64 → U64 → List U64} {Rq : U64 → List U64} {s : S}
    (q : SchedQueuesInvX st T Cs Ω H X s Q Rq) (hk : L.ksb s = kb) (hPp : Pp ⊆ Pt) (hTb : Tb ⊆ Pt)
    (hTe : Gran Te bits ⊆ Pt) (hH : HrOK kb Pp Tb Lv Hr) {pt asid0 v0 : U64} (h12 : bits pt = 12)
    (hS : S2OK (insert pt Te) bits Hr) (hD : S2Pl kb Pp Tb (insert pt Te) bits) (hU : UnmZ st OS Pt Te bits s)
    (hY : VsTy st kb Pp Tb Lv s) (h2 : S2Ty st hPl.ipa Pp Hr Te Re bits s)
    {root : U64} (hr : root ∈ Te) (hre : Re root + 1 = s2lv hPl.ipa) (hrb : s2rb hPl.ipa ≤ bits root)
    (a : A) (asid ipa : U64) {slot : U64} (hsl : slot ∈ OS)
    (hc : obj.Slot.cap st slot s = ok (.PageTable pt false asid0 v0)) :
    ept.map_table st ar s a root asid ipa pt slot ⦃ r => r.2.1 = s ∨ (L.ksb r.2.1 = kb ∧
      VsTy st kb Pp Tb Lv r.2.1 ∧ ∃ Re' : U64 → Nat, (∀ p ∈ Te, Re' p = Re p) ∧
        S2Ty st hPl.ipa Pp Hr (insert pt Te) Re' bits r.2.1) ⦄ := by
  obtain ⟨hpP, hpt, hz⟩ := hU.pt_of hsl hc h12
  have hTe' : Gran (insert pt Te) bits ⊆ Pt := fun q hq => by
    rcases gran_insert hq with h | ⟨p', hp', hq'⟩
    · exact hTe h
    · rw [Set.mem_singleton_iff] at hp'
      subst hp'
      rcases hq' with rfl | ⟨h13, -⟩
      · exact hpP
      · rw [h12] at h13; exact absurd h13 (by decide)
  exact ept.map_table.ty hPl hR hO q hk hPp hTb hpt hTe' hH hS hD hY h2 hz hr hre hrb a asid ipa hsl

/-- **`UnmZ` along a step writing only `VsR` words, each kept or zeroed** (the cap slots are no `VsR` words). -/
theorem UnmZ.keep (hR : VrOK Ω Sg Scs Z OS Vc Ub kb Pt) (hO : OSOK T Ω Sg OS) {s s' : S}
    (hU : UnmZ st OS Pt Te bits s) (hw : WritesIn st s s' (VsR kb Pt)) (hz : VsZ st kb Pt s s') :
    UnmZ st OS Pt Te bits s' := by
  have hc : ∀ x ∈ OS, obj.Slot.cap st x s' = obj.Slot.cap st x s := by
    intro x hx
    obtain ⟨v8, -, -⟩ := vals hO hx
    rw [DPF.slot_cap_dec, DPF.slot_cap_dec,
      hw.mem_eq (hO.al0 hx) fun hb => hR.os _ hb ⟨x, hx, by omega, by omega⟩,
      hw.mem_eq (hO.al hx (k := 8#u64) (by simp) (by simp)) fun hb => hR.os _ hb ⟨x, hx, by omega, by omega⟩]
  have hm : ∀ b, VsR kb Pt b → L.mem s b = 0#u64 → L.mem s' b = 0#u64 := fun b hb h0 => by
    rcases hz b hb with e | e
    · rw [e, h0]
    · exact e
  refine ⟨fun x hx p asid v e => ?_, fun x hx p asid v e => ?_⟩
  · rw [hc x hx] at e
    obtain ⟨hp, hf⟩ := hU.pt x hx p asid v e
    exact ⟨hp, fun o ho h8 => ⟨(hf o ho h8).1, hm _ (Or.inl ⟨p, hp, o, ho, h8, rfl⟩) (hf o ho h8).2⟩⟩
  · rw [hc x hx] at e
    obtain ⟨hp, hf⟩ := hU.ept x hx p asid v e
    refine ⟨hp, fun o ho h8 => ⟨(hf o ho h8).1, hm _ (Or.inl (ptw_mono hp ?_)) (hf o ho h8).2⟩⟩
    exact ptwb_gran (bits := fun _ => 13) (fun _ _ => Or.inr rfl)
      ⟨p, Set.mem_singleton p, o, lt_of_lt_of_eq ho (by norm_num), h8, rfl⟩

/-- **`UnmZ` along a `Wr0` step of `VsR` words.** -/
theorem UnmZ.wr0 (hR : VrOK Ω Sg Scs Z OS Vc Ub kb Pt) (hO : OSOK T Ω Sg OS) {X : Set U64} (hX : X ⊆ Pt)
    {s s' : S} (hU : UnmZ st OS Pt Te' bits s) (z : Wr0 st X s s') : UnmZ st OS Pt Te' bits s' := by
  have z' : Wr0 st Pt s s' := Or.imp id (fun ⟨b, hb, e⟩ => ⟨b, ptw_mono hX hb, e⟩) z
  exact hU.keep hR hO ((Wr0.w (fun b hb => hR.al b (Or.inl hb)) z').mono fun _ hb => Or.inl hb)
    (Wr0.vsz hR.al z')

/-- **`ept::unmap` keeps `UnmZ`.** -/
theorem ept.unmap.unmz (hA : P0.ArchTotal ar) (hPl : ArchPlat ar) (hR : VrOK Ω Sg Scs Z OS Vc Ub kb Pt)
    (hO : OSOK T Ω Sg OS) (hS : S2OK Te bits Hr) (hTe : Gran Te bits ⊆ Pt) {s : S}
    (hY : VsTy st kb Pp Tb Lv s ∧ S2Ty st hPl.ipa Pp Hr Te Re bits s) (hk : L.ksb s = kb)
    (hU : UnmZ st OS Pt Te' bits s) (a : A) (asid ipa ptr shift : U64) (it : Bool) :
    ept.unmap st ar s a asid ipa ptr shift it ⦃ r => UnmZ st OS Pt Te' bits r.1 ⦄ :=
  WP.spec_mono (ept.unmap.z hA hPl hY.1 hY.2 hS hk a asid ipa ptr shift it) fun _ z =>
    UnmZ.wr0 hR hO hTe hU z

/-- **`ept::unmap_table` keeps `UnmZ`.** -/
theorem ept.unmap_table.unmz (hA : P0.ArchTotal ar) (hPl : ArchPlat ar) (hR : VrOK Ω Sg Scs Z OS Vc Ub kb Pt)
    (hO : OSOK T Ω Sg OS) (hS : S2OK Te bits Hr) (hTe : Gran Te bits ⊆ Pt) {s : S}
    (hY : VsTy st kb Pp Tb Lv s ∧ S2Ty st hPl.ipa Pp Hr Te Re bits s) (hk : L.ksb s = kb)
    (hU : UnmZ st OS Pt Te' bits s) (a : A) (asid ipa pt : U64) :
    ept.unmap_table st ar s a asid ipa pt ⦃ r => UnmZ st OS Pt Te' bits r.1 ⦄ :=
  WP.spec_mono (ept.unmap_table.z hA hPl hY.1 hY.2 hS hk a asid ipa pt) fun _ z =>
    UnmZ.wr0 hR hO hTe hU z

/-- **`unmap_page_table` keeps `UnmZ`** (all three branches). -/
theorem vspace.unmap_page_table.unmz (hA : P0.ArchTotal ar) (hPl : ArchPlat ar)
    (hR : VrOK Ω Sg Scs Z OS Vc Ub kb Pt) (hO : OSOK T Ω Sg OS) (hPp : Pp ⊆ Pt) (hTb : Tb ⊆ Pt)
    (hTe : Gran Te bits ⊆ Pt) (hH : HrOK kb Pp Tb Lv Hr) (hS : S2OK Te bits Hr) {s : S}
    (hY : VsTy st kb Pp Tb Lv s ∧ S2Ty st hPl.ipa Pp Hr Te Re bits s) (hk : L.ksb s = kb)
    (hU : UnmZ st OS Pt Te' bits s) (a : A) (asid vaddr pt : U64) :
    vspace.unmap_page_table st ar s a asid vaddr pt ⦃ r => UnmZ st OS Pt Te' bits r.1 ⦄ :=
  WP.spec_mono (vspace.unmap_page_table.s2 hA hPl hH hS hY.1 hY.2 hk a asid vaddr pt) fun _ z =>
    UnmZ.wr0 hR hO (fun b (h : b ∈ TbO Tb Hr ∪ Gran Te bits) => h.elim (fun h' => hTb h'.1) (fun h' => hTe h')) hU z

/-- **Stage-1 `unmap_page` keeps `UnmZ`.** -/
theorem vspace.unmap_page.unmz (hA : P0.ArchTotal ar) {n : U64} (hR : VrOK Ω Sg Scs Z OS Vc Ub kb Pt)
    (hO : OSOK T Ω Sg OS) (hPp : Pp ⊆ Pt) (hTb : Tb ⊆ Pt) (hTe : Gran Te bits ⊆ Pt) (hH : HrOK kb Pp Tb Lv Hr)
    (hS : S2OK Te bits Hr) {s : S} (hY : VsTy st kb Pp Tb Lv s ∧ S2Ty st n Pp Hr Te Re bits s) (hk : L.ksb s = kb)
    (hU : UnmZ st OS Pt Te' bits s) (a : A) (size : capability.FrameSize) (asid vaddr pptr : U64) :
    vspace.unmap_page st ar s a size asid vaddr pptr ⦃ r => UnmZ st OS Pt Te' bits r.1 ⦄ :=
  WP.spec_mono (vspace.unmap_page.hr hA hH hY.1 hk a size asid vaddr pptr) fun _ z =>
    UnmZ.wr0 hR hO (fun b (h : b ∈ TbO Tb Hr) => hTb h.1) hU z

end unmz

/-! ## ARMPageTableUnmap's `zero(ptr, 4096)` -/

section zr
variable {OS Vc Ub : Set U64} {kb n : U64} {Pp Tb Pt Hr Te : Set U64} {Lv Re bits : U64 → Nat}

/-- `zero(p, 4096)` of an aligned, non-wrapping range keeps or zeroes every word. -/
theorem zr_vsz {s : S} {p : U64} (hal : ∀ b, VsR kb Pt b → Aligned b) (hp : Aligned p)
    (hfit : p.val + 4096 ≤ 2 ^ 64) : VsZ st kb Pt s (L.zr s p 4096#u64) := fun b hb => by
  rw [L.mem_zr s p 4096#u64 b hp (by simp) (by simpa using hfit) (hal b hb)]
  split
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- `zero(p, 4096)` keeps the `R + 4088` words no word of `p` (at an aligned offset) is. -/
theorem zr_hrw {s : S} {p : U64} (hRal : ∀ R ∈ Hr, Aligned (wa R 4088#u64)) (hp : Aligned p)
    (hfit : p.val + 4096 ≤ 2 ^ 64)
    (hh : ∀ R ∈ Hr, ∀ o : U64, o.val < 4096 → o.val % 8 = 0 → wa p o ≠ wa R 4088#u64) :
    HrW st Hr s (L.zr s p 4096#u64) := fun R hR => by
  rw [L.mem_zr s p 4096#u64 _ hp (by simp) (by simpa using hfit) (hRal R hR)]
  split
  · rename_i hin
    exfalso
    have hb8 : (wa R 4088#u64).val % 8 = 0 := hRal R hR
    have hp8 : p.val % 8 = 0 := hp
    have h4 : (4096#u64 : U64).val = 4096 := rfl
    rw [h4] at hin
    obtain ⟨e, hv⟩ := wa_sub_of_le (p := p) (b := wa R 4088#u64) hin.1
    exact hh R hR _ (by omega) (by omega) e
  · rfl

/-- **ARMPageTableUnmap's `zero(ptr, 4096)`** (vspace.rs:1101–1102) of a 4 KiB table no `R + 4088` word lies in:
it writes only `ptr`'s words, leaves them zero, and keeps `VsTy ∧ S2Ty`. -/
theorem zr.ty (hR : VrOK Ω Sg Scs Z OS Vc Ub kb Pt) (hPp : Pp ⊆ Pt) (hTb : Tb ⊆ Pt) (hTe : Gran Te bits ⊆ Pt)
    (hH : HrOK kb Pp Tb Lv Hr) (hS : S2OK Te bits Hr) {s : S}
    (hY : VsTy st kb Pp Tb Lv s ∧ S2Ty st n Pp Hr Te Re bits s) {p : U64} (hp : Aligned p)
    (hfit : p.val + 4096 ≤ 2 ^ 64)
    (hh : ∀ R ∈ Hr, ∀ o : U64, o.val < 4096 → o.val % 8 = 0 → wa p o ≠ wa R 4088#u64) :
    WritesIn st s (L.zr s p 4096#u64) (fun b => p.val ≤ b.val ∧ b.val < p.val + 4096) ∧
      (∀ b, Aligned b → p.val ≤ b.val → b.val < p.val + 4096 → L.mem (L.zr s p 4096#u64) b = 0#u64) ∧
      VsTy st kb Pp Tb Lv (L.zr s p 4096#u64) ∧ S2Ty st n Pp Hr Te Re bits (L.zr s p 4096#u64) := by
  have z := zr_vsz (st := st) (s := s) hR.al hp hfit
  refine ⟨⟨L.ksb_zr _ _ _, L.cpu_zr _ _ _, fun b hb hn => ?_⟩, fun b hb h1 h2 => ?_, hY.1.keepZ hPp hTb z,
    hY.2.keep hPp hTe hS z (zr_hrw (fun R hR' => hR.al _ (hr_vsr hTb hH hR')) hp hfit hh)⟩
  · rw [L.mem_zr s p 4096#u64 b hp (by simp) (by simpa using hfit) hb]
    have h4 : (4096#u64 : U64).val = 4096 := rfl
    rw [h4, if_neg hn]
  · rw [L.mem_zr s p 4096#u64 b hp (by simp) (by simpa using hfit) hb]
    have h4 : (4096#u64 : U64).val = 4096 := rfl
    rw [h4, if_pos ⟨h1, h2⟩]

end zr

/-! ## ASIDPool `Assign` of a Stage-2 root -/

theorem nat_low2 {r : Nat} (h : r % 4 = 0) {j : Nat} (hj : j < 2) : r.testBit j = false := by
  have h' := Nat.testBit_mod_two_pow r 2 j
  rw [show r % 2 ^ 2 = 0 by omega, Nat.zero_testBit] at h'
  cases hb : r.testBit j
  · rfl
  · rw [hb] at h'; simp [hj] at h'

theorem nat_or1_3 {r : Nat} (h : r % 4 = 0) : (r ||| 1) &&& 3 = 1 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_or]
  rcases (show i = 0 ∨ i = 1 ∨ 2 ≤ i by omega) with rfl | rfl | hi
  · rw [nat_low2 h (by omega)]; decide
  · rw [nat_low2 h (by omega)]; decide
  · have h1 : Nat.testBit 1 i = false :=
      Nat.testBit_eq_false_of_lt (Nat.lt_of_lt_of_le (by norm_num : 1 < 2 ^ 2) (Nat.pow_le_pow_right (by norm_num) hi))
    have h3 : Nat.testBit 3 i = false :=
      Nat.testBit_eq_false_of_lt (Nat.lt_of_lt_of_le (by norm_num : 3 < 2 ^ 2) (Nat.pow_le_pow_right (by norm_num) hi))
    simp [h1, h3]

theorem tb_N (i : Nat) : (18446744073709551612 : Nat).testBit i = (decide (2 ≤ i) && decide (i < 64)) := by
  have hM : (18446744073709551612 : Nat) = (2 ^ 62 - 1) <<< 2 := by
    first | decide | (rw [Nat.shiftLeft_eq]; norm_num)
  rw [hM, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
  by_cases h : 2 ≤ i <;> simp [h] <;> omega

theorem nat_or1_n3 {r : Nat} (h : r % 4 = 0) (hr : r < 2 ^ 64) : (r ||| 1) &&& 18446744073709551612 = r := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_or, tb_N i]
  rcases (show i = 0 ∨ i = 1 ∨ 2 ≤ i by omega) with rfl | rfl | hi
  · rw [nat_low2 h (by omega)]; decide
  · rw [nat_low2 h (by omega)]; decide
  · have h1 : Nat.testBit 1 i = false :=
      Nat.testBit_eq_false_of_lt (Nat.lt_of_lt_of_le (by norm_num : 1 < 2 ^ 2) (Nat.pow_le_pow_right (by norm_num) hi))
    by_cases hj : i < 64
    · simp [h1, hi, hj]
    · have hx : r.testBit i = false :=
        Nat.testBit_eq_false_of_lt (Nat.lt_of_lt_of_le hr (Nat.pow_le_pow_right (by norm_num) (by omega)))
      simp [h1, hx]

/-- A pool value `root | ROOT_S2` of a 4-byte-aligned root: tag 1, the root its untagged part. -/
theorem s2tag_v {r : U64} (h : r.val % 4 = 0) :
    ((r ||| vspace.ROOT_S2) &&& 3#u64) = 1#u64 ∧ ((r ||| vspace.ROOT_S2) &&& ~~~3#u64) = r := by
  rw [rs2]
  have e1 : ((1#u64 : U64).val) = 1 := rfl
  have e3 : ((3#u64 : U64).val) = 3 := rfl
  have en : ((~~~3#u64 : U64).val) = 18446744073709551612 := by first | rfl | decide | simp
  have hr : r.val < 2 ^ 64 := by have := r.hBounds; first | omega | scalar_tac
  refine ⟨UScalar.eq_of_val_eq ?_, UScalar.eq_of_val_eq ?_⟩
  · simp only [UScalar.val_and, UScalar.val_or, e1, e3]
    exact nat_or1_3 h
  · simp only [UScalar.val_and, UScalar.val_or, e1, en]
    exact nat_or1_n3 h hr

set_option hygiene false in
/-- An error return of the decode (the state unchanged). -/
macro "asErr" : tactic => `(tactic| first
  | exact (WP.spec_ok _).2 (Or.inl rfl)
  | (simp only [error.invalid_cap, error.illegal, error.truncated, error.invalid_arg, bind_ok]
     exact (WP.spec_ok _).2 (Or.inl rfl)))

section asg
variable {OS Vc Ub : Set U64} {kb : U64} {Pp Tb Pt Hr Te : Set U64} {Lv Re bits : U64 → Nat}
variable {A : Type _} {ar : machine.Arch A}

set_option maxHeartbeats 4000000 in
/-- **ASIDPool `Assign` of an unmapped Stage-2 root** (vspace.rs:1229–1261, the `AsidPool` arm of `vspace.decode`
with an unmapped level-0 `Ept` cap in the extra slot): the state unchanged, or `ks` and `VsTy` kept and `S2Ty`
over `insert r0 Te`, the root at depth `s2lv n − 1` (gen 41's `S2Ty.assign1` / `VsTy.assign1`; the zero root and
`r0 ∉ Te` from `UnmZ.ept`). Case hypotheses: the root's size and placement, pool words no ASID-table words. -/
theorem vspace.decode.assign_s2 (hPl : ArchPlat ar) (hR : VrOK Ω Sg Scs Z OS Vc Ub kb Pt) (hO : OSOK T Ω Sg OS)
    {X : Set U64} {Q : U64 → U64 → List U64} {Rq : U64 → List U64} {s : S}
    (q : SchedQueuesInvX st T Cs Ω H X s Q Rq) (hk : L.ksb s = kb) (hPp : Pp ⊆ Pt) (hTb : Tb ⊆ Pt)
    (hTe : Gran Te bits ⊆ Pt) (hH : HrOK kb Pp Tb Lv Hr) (hPA : ∀ b, PtW Pp b → ¬ AsW kb b)
    {r0 a0 v0 : U64} (h13 : bits r0 = 13) (hS : S2OK (insert r0 Te) bits Hr) (hU : UnmZ st OS Pt Te bits s)
    (hY : VsTy st kb Pp Tb Lv s) (h2 : S2Ty st hPl.ipa Pp Hr Te Re bits s)
    (a : A) (len slot pptr abase : U64) (call : Bool) (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize)
    (hx : ∀ x ∈ extra.val, x ≠ 0#u64 → x ∈ OS ∧ obj.Slot.cap st x s = ok (.Ept r0 0#u64 false a0 v0)) :
    vspace.decode st ar s a fl4_abi.label.ARMASIDPoolAssign len slot (.AsidPool pptr abase) call buf extra
      ⦃ r => r.2.1 = s ∨ (L.ksb r.2.1 = kb ∧ VsTy st kb Pp Tb Lv r.2.1 ∧ ∃ Re' : U64 → Nat,
        (∀ p ∈ Te, Re' p = Re p) ∧ S2Ty st hPl.ipa Pp Hr (insert r0 Te) Re' bits r.2.1) ⦄ := by
  have hS' : P0.StoreTotal st := L.total
  have hsub : Te ⊆ insert r0 Te := Set.subset_insert _ _
  have hS0 : S2OK Te bits Hr := S2OK.sub hS hsub
  unfold vspace.decode
  refine WP.spec_bind (sched.cur_thread.spec s) fun ct ect => ?_
  have hct : ct ∈ T := by rw [ect]; exact q.curT
  try dsimp only
  refine spec_ite (fun _ => by asErr) (fun _ => ?_)
  refine WP.spec_bind (vspace.extra.memA extra 0#usize) fun o ho => ?_
  rcases o with _ | x
  · asErr
  obtain ⟨hxm, hx0⟩ := ho x rfl
  obtain ⟨hxO, hxc⟩ := hx x hxm hx0
  try dsimp only
  rw [hxc, bind_ok]
  try dsimp only
  obtain ⟨hgr, hf⟩ := hU.ept x hxO r0 a0 v0 hxc
  try split
  all_goals try asErr
  refine spec_ite (fun _ => by asErr) (fun _ => ?_)
  refine WP.spec_bind (Pₘ := fun _ => True) (by p0_auto) fun i _ => ?_
  refine WP.spec_bind (vspace.asid_table.w s i) fun pool ⟨oA, hA1, hA2, hA8, epool⟩ => ?_
  refine spec_ite (fun _ => by asErr) (fun hp0 => ?_)
  refine spec_ite (fun _ => by asErr) (fun _ => ?_)
  refine WP.spec_bind (P0.vspace.decode_loop2.p0 st s _ _ _ hS') fun i2 _ => ?_
  refine spec_ite (fun _ => by asErr) (fun _ => ?_)
  try simp only [lift, bind_ok]
  refine WP.spec_bind (stt_vk hR q hct) fun s1 ⟨w1, k1⟩ => ?_
  refine WP.spec_bind (Pₘ := fun s2 => WritesIn st s1 s2 (W7.CapW T {b | InOS OS b} ∅)) (by
    repeat' (first
      | exact W7.obj.Slot.set_cap.capw (osw hO hxO)
      | split)) fun s2 w2 => ?_
  try simp only [lift, bind_ok]
  step as ⟨i4, hi4⟩
  try simp only [lift, bind_ok]
  refine WP.spec_bind (LawfulStore.write_spec s2 _ _) fun s3 e3 => ?_
  subst e3
  have hpP : pool ∈ Pp := by
    have := hY.tbl oA hA1 hA2 hA8 (by rw [← hk, ← epool]; exact hp0)
    rwa [← hk, ← epool] at this
  have ho4 : i4.val < 4096 ∧ i4.val % 8 = 0 := by
    obtain ⟨Y, hY4⟩ : ∃ Y : U64, i4.val = (Y &&& 511#u64).val * 8 := ⟨_, hi4⟩
    have hb : (Y &&& 511#u64).val ≤ 511 := by
      rw [UScalar.val_and]; exact le_trans Nat.and_le_right (by simp)
    omega
  have k12 : VsKeep st kb Pt s s2 := k1.trans (vsk_cw q hR w2)
  have hk2 : L.ksb s2 = kb := by rw [w2.1, w1.1, hk]
  have hY2 : VsTy st kb Pp Tb Lv s2 := hY.keepZ hPp hTb (VsKeep.vsz k12)
  have h22 : S2Ty st hPl.ipa Pp Hr Te Re bits s2 :=
    h2.keep hPp hTe hS0 (VsKeep.vsz k12) fun R hR' => k12 _ (hr_vsr hTb hH hR')
  have hr0w : ∀ o : U64, o.val < 8192 → o.val % 8 = 0 → VsR kb Pt (wa r0 o) := fun o ho h8 =>
    Or.inl (ptw_mono hgr (ptwb_gran (bits := fun _ => 13) (fun _ _ => Or.inr rfl)
      ⟨r0, Set.mem_singleton r0, o, lt_of_lt_of_eq ho (by norm_num), h8, rfl⟩))
  have hr0T : r0 ∉ Te := fun hT => (hf 0#u64 (by simp) (by simp)).1 ⟨r0, hT, 0#u64, by
    have := @Nat.one_le_two_pow (bits r0)
    simpa using Nat.lt_of_lt_of_le Nat.zero_lt_one this, by simp, rfl⟩
  have hTe' : Gran (insert r0 Te) bits ⊆ Pt := fun q hq => by
    rcases gran_insert hq with h | ⟨p', hp', hq'⟩
    · exact hTe h
    · rw [Set.mem_singleton_iff] at hp'
      subst hp'
      exact hgr ⟨p', Set.mem_singleton _, hq'.imp id fun ⟨_, e⟩ => ⟨rfl, e⟩⟩
  have hr4 : r0.val % 4 = 0 := by
    have := hS.al r0 (Set.mem_insert _ _)
    rw [h13] at this
    norm_num at this
    omega
  obtain ⟨hv1, hvr⟩ := s2tag_v hr4
  have hRe : ∀ q ∈ Te, Function.update Re r0 (s2lv hPl.ipa - 1) q = Re q :=
    fun q hq => Function.update_of_ne (fun e => hr0T (by rw [← e]; exact hq)) _ _
  refine (WP.spec_ok _).2 (Or.inr ⟨by rw [L.ksb_wr]; exact hk2, ?_,
    Function.update Re r0 (s2lv hPl.ipa - 1), hRe, ?_⟩)
  · exact VsTy.assign1 hR.al hPp hTb hY2 hpP ho4.1 ho4.2 (hPA _ ⟨pool, hpP, i4, ho4.1, ho4.2, rfl⟩) hv1
  · refine S2Ty.assign1 hR.al hPp hTe' hS (fun R hR' => hR.al _ (hr_vsr hTb hH hR'))
      (S2Ty.congr h22 hRe fun _ _ => rfl) hpP ho4.1 ho4.2
      (fun R hR' e => hH.pp pool hpP i4 ho4.1 ho4.2 R hR' e.symm) hv1 hvr ?_ ?_ ?_
    · rw [Function.update_self]; have := s2lv_ge hPl.ipa; omega
    · rw [h13]; unfold s2rb; split <;> omega
    · intro o ho h8 h3
      rw [h13] at ho
      have ho' : o.val < 8192 := by simpa using ho
      rw [k12 _ (hr0w o ho' h8), (hf o ho' h8).2] at h3
      exact absurd h3 (by decide)

end asg

/-! ## Stage-2 leaves: `make_s2_leaf`, `install_s2_leaf`, `map_frame` -/

/-- Bit 1 of a word clear (no `e & 3 = 3` descriptor). -/
def B1 (x : U64) : Prop := x.val.testBit 1 = false

theorem B1.or {x y : U64} (hx : B1 x) (hy : B1 y) : B1 (x ||| y) := by
  unfold B1 at *; rw [UScalar.val_or, Nat.testBit_or, hx, hy]; rfl

theorem B1.am (p : U64) : B1 (p &&& ept.ADDR_MASK) := by
  unfold B1; rw [UScalar.val_and, Nat.testBit_and, ept.ADDR_MASK.val_eq, tb_M]; simp

theorem B1.ne3 {e : U64} (h : B1 e) : (e &&& 3#u64) ≠ 3#u64 := fun h3 => by
  have h' := congrArg (fun x : U64 => x.val.testBit 1) h3
  have e3 : (3#u64 : U64).val.testBit 1 = true := by decide
  simp only [UScalar.val_and, Nat.testBit_and] at h'
  unfold B1 at h
  rw [h, e3] at h'
  simp at h'

/-- **`make_s2_leaf`** (ept.rs:97–117) below the page shift builds a block descriptor or `0`: bit 1 clear. -/
theorem ept.make_s2_leaf.b1 (pa vm : U64) (cr : Bool) (attr sh : U64) :
    ept.make_s2_leaf pa vm cr attr sh ⦃ e => sh ≠ ept.PAGE_BITS → B1 e ⦄ := by
  by_cases hsh : sh = ept.PAGE_BITS
  · exact WP.spec_mono (P0.ept.make_s2_leaf.p0 pa vm cr attr sh) fun _ _ h => absurd hsh h
  suffices hB : ept.make_s2_leaf pa vm cr attr sh ⦃ e => B1 e ⦄ from WP.spec_mono hB fun _ h _ => h
  unfold ept.make_s2_leaf
  rw [eq_of_spec_fd P0.Consts.ept.S2_AP_RW.spec, eq_of_spec_fd P0.Consts.ept.S2_AP_RO.spec,
    eq_of_spec_fd P0.Consts.ept.S2_MEMATTR_NORMAL_WB.spec, eq_of_spec_fd P0.Consts.ept.S2_MEMATTR_DEVICE.spec,
    eq_of_spec_fd P0.Consts.ept.S2_SH_INNER.spec, eq_of_spec_fd P0.Consts.ept.S2_AF.spec,
    eq_of_spec_fd P0.Consts.ept.S2_XN.spec, eq_of_spec_fd P0.Consts.ept.D_VALID.spec]
  simp only [lift, bind_ok, hsh, ↓reduceIte]
  refine spec_ite (fun _ => ?_) (fun _ => spec_ite (fun _ => ?_) (fun _ => (WP.spec_ok _).2 (by unfold B1; decide)))
  all_goals
    refine WP.spec_bind (P0.vspace.exec_never.p0 attr cr) fun xn _ => ?_
    refine WP.spec_bind (Pₘ := fun p : U64 × U64 => B1 p.1 ∧ B1 p.2)
      (by split <;> exact (WP.spec_ok _).2 ⟨by unfold B1; decide, by unfold B1; decide⟩) ?_
    rintro ⟨m, sh'⟩ ⟨hm, hs⟩
    try dsimp only
    try simp only [lift, bind_ok]
    refine WP.spec_bind (Pₘ := B1) (by split <;> exact (WP.spec_ok _).2 (by unfold B1; decide)) fun i9 h9 => ?_
    exact (WP.spec_ok _).2 (B1.or (B1.or (B1.or (B1.or (B1.or (B1.or (B1.am pa) (by unfold B1; decide)) hm)
      (by unfold B1; decide)) hs) (by unfold B1; decide)) h9)

section leaf
variable {OS Vc Ub : Set U64} {kb n : U64} {Pp Tb Pt Hr Te : Set U64} {Lv Re bits : U64 → Nat}
variable {A : Type _} {ar : machine.Arch A}

/-- **A write of a non-descriptor value into a Stage-2 table at a positive depth** (or any value at depth `0`)
keeps `VsTy ∧ S2Ty`. -/
theorem ty_leaf_wr (hR : VrOK Ω Sg Scs Z OS Vc Ub kb Pt) (hPp : Pp ⊆ Pt) (hTb : Tb ⊆ Pt) (hTe : Gran Te bits ⊆ Pt)
    (hH : HrOK kb Pp Tb Lv Hr) (hS : S2OK Te bits Hr) (hD : S2Pl kb Pp Tb Te bits) {s : S}
    (hY : VsTy st kb Pp Tb Lv s ∧ S2Ty st n Pp Hr Te Re bits s) {p o v : U64} (hp : p ∈ Te)
    (ho : o.val < 2 ^ bits p) (h8 : o.val % 8 = 0) (hv : 0 < Re p → (v &&& 3#u64) ≠ 3#u64) :
    VsTy st kb Pp Tb Lv (L.wr s (wa p o) v) ∧ S2Ty st n Pp Hr Te Re bits (L.wr s (wa p o) v) := by
  have hw : PtWb Te bits (wa p o) := ⟨p, hp, o, ho, h8, rfl⟩
  have hal : Aligned (wa p o) := hR.al _ (Or.inl (ptw_mono hTe (ptwb_gran hS.sz hw)))
  refine ⟨VsTy.wr hR.al hPp hTb hal hY.1 (fun o' h1 h2 h8' e _ => (hD.asw _ hw ⟨o', h1, h2, h8', e.symm⟩).elim)
      (fun q hq o' ho' h8' e _ => (hD.pp _ hw ⟨q, hq, o', ho', h8', e.symm⟩).elim)
      (fun q hq _ o' ho' h8' e _ => (hD.tb _ hw ⟨q, hq, o', ho', h8', e.symm⟩).elim),
    S2Ty.wr hR.al hPp hTe hS (fun R hR' => hR.al _ (hr_vsr hTb hH hR')) hal hY.2
      (fun q hq o' ho' h8' e _ => (hD.pp _ hw ⟨q, hq, o', ho', h8', e.symm⟩).elim)
      (fun R hR' e => hS.hr _ hw R hR' e.symm) (fun q hq hr o' ho' h8' e h3 => ?_)⟩
  obtain rfl := hD.un p hp q hq o o' ho h8 ho' h8' e
  exact absurd h3 (hv hr)

set_option maxHeartbeats 4000000 in
/-- **`ept::install_s2_leaf`** (ept.rs:290–316) at a word of a Stage-2 table, with a value that is no descriptor at
a positive depth: `ks`, `VsTy`, `S2Ty` kept (break-before-make: the slot written `0`, then the value). -/
theorem ept.install_s2_leaf.ty (hA : P0.ArchTotal ar) (hR : VrOK Ω Sg Scs Z OS Vc Ub kb Pt) (hPp : Pp ⊆ Pt)
    (hTb : Tb ⊆ Pt) (hTe : Gran Te bits ⊆ Pt) (hH : HrOK kb Pp Tb Lv Hr) (hS : S2OK Te bits Hr)
    (hD : S2Pl kb Pp Tb Te bits) {s : S} (hY : VsTy st kb Pp Tb Lv s ∧ S2Ty st n Pp Hr Te Re bits s) (a : A)
    (lu : ept.S2Slot) {p o : U64} (hp : p ∈ Te) (ho : o.val < 2 ^ bits p) (h8 : o.val % 8 = 0)
    (hsl : lu.slot = wa p o) (e : U64) (he : 0 < Re p → (e &&& 3#u64) ≠ 3#u64) (root asid ipa ptr : U64)
    (dev : Bool) (attr : U64) :
    ept.install_s2_leaf st ar s a lu e root asid ipa ptr dev attr ⦃ r =>
      L.ksb r.1 = L.ksb s ∧ VsTy st kb Pp Tb Lv r.1 ∧ S2Ty st n Pp Hr Te Re bits r.1 ⦄ := by
  have wr : ∀ s1 : S, (L.ksb s1 = L.ksb s ∧ VsTy st kb Pp Tb Lv s1 ∧ S2Ty st n Pp Hr Te Re bits s1) →
      ∀ v : U64, (0 < Re p → (v &&& 3#u64) ≠ 3#u64) → st.write s1 lu.slot v ⦃ s' =>
        L.ksb s' = L.ksb s ∧ VsTy st kb Pp Tb Lv s' ∧ S2Ty st n Pp Hr Te Re bits s' ⦄ := fun s1 h1 v hv =>
    WP.spec_mono (LawfulStore.write_spec s1 lu.slot v) fun s' e' => by
      subst e'
      rw [hsl]
      obtain ⟨a1, a2⟩ := ty_leaf_wr hR hPp hTb hTe hH hS hD ⟨h1.2.1, h1.2.2⟩ hp ho h8 hv
      exact ⟨by rw [L.ksb_wr]; exact h1.1, a1, a2⟩
  have z0 : 0 < Re p → ((0#u64 : U64) &&& 3#u64) ≠ 3#u64 := fun _ => by decide
  have h0 : L.ksb s = L.ksb s ∧ VsTy st kb Pp Tb Lv s ∧ S2Ty st n Pp Hr Te Re bits s := ⟨rfl, hY.1, hY.2⟩
  unfold ept.install_s2_leaf
  refine WP.spec_bind (LawfulStore.read_spec s lu.slot) fun old _ => ?_
  refine WP.spec_bind (P0.ept.is_leaf.p0 old lu.shift) fun b _ => ?_
  try simp only [lift, bind_ok]
  have cop : ∀ m : Result A, m ⦃ _ => True ⦄ → ∀ s1 : S,
      (L.ksb s1 = L.ksb s ∧ VsTy st kb Pp Tb Lv s1 ∧ S2Ty st n Pp Hr Te Re bits s1) →
      (do
        let a2 ← m
        let s2 ← st.write s1 lu.slot e
        ok (s2, a2)) ⦃ r => L.ksb r.1 = L.ksb s ∧ VsTy st kb Pp Tb Lv r.1 ∧ S2Ty st n Pp Hr Te Re bits r.1 ⦄ :=
    fun m hm s1 h1 => WP.spec_bind hm fun a2 _ => WP.spec_bind (wr s1 h1 e he) fun s2 h2 => (WP.spec_ok _).2 h2
  refine spec_ite (fun _ => ?_) (fun _ => ?_)
  · refine spec_ite (fun _ => ?_) (fun _ => ?_)
    · refine WP.spec_bind P0.ept.S2_BBM_MASK.p0 fun mk _ => ?_
      refine spec_ite (fun _ => ?_) (fun _ => ?_)
      · refine WP.spec_bind (wr s h0 e he) fun s1 h1 => ?_
        refine WP.spec_bind (hA.invalidate_stage2_page a asid ipa) fun a1 _ => ?_
        exact (WP.spec_ok _).2 h1
      · refine WP.spec_bind (wr s h0 0#u64 z0) fun s1 h1 => ?_
        refine WP.spec_bind (hA.invalidate_stage2_page a asid ipa) fun a1 _ => ?_
        exact cop _ (by copT) s1 h1
    · refine WP.spec_bind (wr s h0 0#u64 z0) fun s1 h1 => ?_
      refine WP.spec_bind (hA.invalidate_stage2_page a asid ipa) fun a1 _ => ?_
      exact cop _ (by copT) s1 h1
  · exact cop _ (by copT) s h0

set_option maxHeartbeats 4000000 in
/-- **`ept::map_frame`** (ept.rs:236–287, the whole function): the state unchanged, or `ks`, `VsTy` and `S2Ty` kept
(the leaf goes to the slot `lookup_slot` finds at the frame's shift: a block below the page shift, `Re = 0` at it). -/
theorem ept.map_frame.ty (hA : P0.ArchTotal ar) (hPl : ArchPlat ar) (hR : VrOK Ω Sg Scs Z OS Vc Ub kb Pt)
    (hO : OSOK T Ω Sg OS) {X : Set U64} {Q : U64 → U64 → List U64} {Rq : U64 → List U64} {s : S}
    (q : SchedQueuesInvX st T Cs Ω H X s Q Rq) (hk : L.ksb s = kb) (hPp : Pp ⊆ Pt) (hTb : Tb ⊆ Pt)
    (hTe : Gran Te bits ⊆ Pt) (hH : HrOK kb Pp Tb Lv Hr) (hS : S2OK Te bits Hr) (hD : S2Pl kb Pp Tb Te bits)
    (hY : VsTy st kb Pp Tb Lv s) (h2 : S2Ty st hPl.ipa Pp Hr Te Re bits s)
    {root : U64} (hr : root ∈ Te) (hre : Re root + 1 = s2lv hPl.ipa) (hrb : s2rb hPl.ipa ≤ bits root)
    (a : A) (asid ipa vm attr ptr : U64) (size : capability.FrameSize) (rights : U64) (dev : Bool)
    (masid mvaddr : U64) {slot : U64} (hsl0 : slot ∈ OS) :
    ept.map_frame st ar s a root asid ipa vm attr ptr size rights dev masid mvaddr slot ⦃ r => r.2.1 = s ∨
      (L.ksb r.2.1 = kb ∧ VsTy st kb Pp Tb Lv r.2.1 ∧ S2Ty st hPl.ipa Pp Hr Te Re bits r.2.1) ⦄ := by
  unfold ept.map_frame
  refine WP.spec_bind (P0.capability.FrameSize.bits.p0 size) fun shift _ => ?_
  rw [hPl.ipa_eq a, bind_ok]
  try simp only [lift, bind_ok]
  refine WP.spec_bind (shl_and63u _) fun _ _ => ?_
  try simp only [lift, bind_ok]
  refine spec_ite (fun _ => by asErr) (fun _ => ?_)
  refine spec_ite (fun _ => ?_) (fun _ => ?_)
  all_goals
    repeat' (first
      | (refine spec_ite (fun _ => by asErr) (fun _ => ?_))
      | (refine WP.spec_bind (shl_and63u _) fun _ _ => ?_)
      | (refine WP.spec_bind (P0.ept.ipa_limit.p0 _) fun _ _ => ?_)
      | (simp only [lift, bind_ok]))
    refine WP.spec_bind (ept.lookup_slot.tyD h2 hS hr hre hrb ipa) fun lu ⟨p, hp, o, ho, h8, hsl, hsh⟩ => ?_
    refine spec_ite (fun _ => by asErr) (fun hne => ?_)
    have hls : lu.shift = shift := by
      first
        | simpa using hne
        | (simp at hne; first | exact hne | exact UScalar.eq_of_val_eq hne | (apply UScalar.eq_of_val_eq; simpa using hne))
    refine WP.spec_bind (P0.vspace.rights_readable.p0 _) fun cr _ => ?_
    refine WP.spec_bind (P0.layout.paddr.p0 ptr) fun pa _ => ?_
    refine WP.spec_bind (ept.make_s2_leaf.b1 pa vm cr attr shift) fun e he => ?_
    have he' : 0 < Re p → (e &&& 3#u64) ≠ 3#u64 := fun h => B1.ne3 (he fun e' => by
      have := congrArg UScalar.val (hls.trans e'); rw [ept.PAGE_BITS.val_eq] at this; omega)
    refine WP.spec_bind (sched.cur_thread.spec s) fun ct ect => ?_
    have hct : ct ∈ T := by rw [ect]; exact q.curT
    refine WP.spec_bind (stt_vk hR q hct) fun s1 ⟨w1, k1⟩ => ?_
    repeat' (refine spec_ite (fun _ => ?_) (fun _ => ?_))
    all_goals
      refine WP.spec_bind (W7.obj.Slot.set_cap.capw (s := s1) (osw hO hsl0)) fun s2 w2 => ?_
      have k12 : VsKeep st kb Pt s s2 := k1.trans (vsk_cw q hR w2)
      have hY2 : VsTy st kb Pp Tb Lv s2 := hY.keepZ hPp hTb (VsKeep.vsz k12)
      have h22 : S2Ty st hPl.ipa Pp Hr Te Re bits s2 :=
        h2.keep hPp hTe hS (VsKeep.vsz k12) fun R hR' => k12 _ (hr_vsr hTb hH hR')
      refine WP.spec_bind (ept.install_s2_leaf.ty hA hR hPp hTb hTe hH hS hD ⟨hY2, h22⟩ a lu hp ho h8 hsl e he'
        root asid ipa ptr dev attr) ?_
      rintro ⟨s3, a1⟩ ⟨hk3, hY3, h23⟩
      exact (WP.spec_ok _).2 (Or.inr ⟨by rw [hk3, w2.1, w1.1, hk], hY3, h23⟩)

end leaf

end ST
end R
end W7

end

end Fl4ProofsA64.P1
