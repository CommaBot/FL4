/-
P1 (aarch64, gen 37): **the VSpace typing `VsTy`** — the closure of the ghost page-table / ASID-pool objects'
contents and the ASID table — from which the walk facts `PtWalk` / `PtPool` of QueueVsPt follow at **every** state
that satisfies it, and which VSpace deletions keep (they only write `0`).

Source (crates/fl4-core/src/arch/aarch64/vspace.rs, layout.rs):
* the ASID table is `ks + ASID_TABLE + 8·i`, `i < N_ASID_POOLS` (`asid_table`, vspace.rs:219–222;
  `ks::ASID_TABLE` = 772352 after the 128 nodes, layout.rs:167; `N_ASID_POOLS = 1 << 7`, vspace.rs:61);
* `find_asid_raw` (229–242) reads the pool entry `pool + 8·(asid & 511)` and rejects `0`; `unmap_root` keeps a
  `ROOT_S1` (tag 0) entry and strips the tag of a `ROOT_HIGH` (tag 2) entry, other tags give no root;
* `lookup_pt_slot` (120–130): from `root + 8·((vaddr >> 39) & 511)`, three levels; at level `ℓ > 0` (shift
  `12 + 9ℓ > 12`) a descriptor with `e & 3 = 3` (`is_table`) is followed to `pptr(e & ADDR_MASK)` (`table_of`).

**`VsTy kb Pp Tb Lv s`** over ghost sets `Pp` (ASID pools) and `Tb` (page tables, roots included) and a ghost
level `Lv` (0 for a root, the depth below it otherwise):
* `tbl`: every nonzero ASID-table entry is a pool of `Pp`;
* `pool`: a nonzero entry of a pool with tag 0 is a root of `Tb` of level 0, with tag 2 its untagged value is;
* `desc`: in a table of `Tb` of level `< 3`, a descriptor with `e & 3 = 3` names a table of `Tb` one level down.
It reads only `VsR kb Pt` words (`PtW Pt` words of `Pp ⊆ Pt`, `Tb ⊆ Pt`, and the ASID-table words `AsW kb`), so a
step that keeps each of them **or makes it `0`** (`VsZ`) keeps it (`VsTy.keepZ`): `0` is no entry and no table
descriptor.

* **`vspace.lookup_pt_slot.ty`** (the walk over `lookup_pt_slot_loop`, invariant `LkI`: the slot is a word of a
  table of level `3 - level`, `shift = 12 + 9·level`): from a level-0 root of `Tb` the slot is a `PtW Tb` word.
* **`VsTy.ptWalk`**, **`VsTy.ptPool`**: QueueVsPt's `PtWalk` / `PtPool` at a `VsTy` state whose `ks` base is `kb`.
* zero-write frames: `vspace.unmap_page.z`, `vspace.delete_asid.z`, `fin_frame.z`, `fin_root.z`, `fin_hvs.z` (the
  state is unchanged or one `PtW Pt` word is written `0`), `VsZ.wr0`.

Is `VsTy` true on reachable states (as a fact of the start state of a deletion, with `Pp` the live ASID pools,
`Tb` the live VSpace roots and page tables mapped below them, `Lv` their mapping depth)? Pool entries are set
only by `assign` with the root of a `Pml4` / `HighVSpace` cap (tag 0 / 2) and cleared by `delete_asid`; table
descriptors are written only by `map_page_table` (vspace.rs) at the level the lookup reached, with a page table
of an unmapped cap — a page-table cap cannot be derived while unmapped (seL4 `deriveCap`, FL4's `derive_cap`), so a
table is mapped once, at one depth — and cleared by `unmap_page_table`; leaf (page) descriptors with `e & 3 = 3`
sit at level 3 only, where `desc` asks nothing. No named premise; new definitions and theorems only.
-/
import Fl4ProofsA64.P1.QueueVsPt
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64}

local notation "wa" => core.num.U64.wrapping_add

/-! ## The definitions -/

/-- An ASID-table word (`ks + 772352 + 8·i`, `i < 128`). -/
def AsW (kb b : U64) : Prop := ∃ o : U64, 772352 ≤ o.val ∧ o.val < 773376 ∧ o.val % 8 = 0 ∧ b = wa kb o

/-- **The words `VsTy` reads**: words of the ghost VSpace objects and the ASID-table words. -/
def VsR (kb : U64) (Pt : Set U64) (b : U64) : Prop := PtW Pt b ∨ AsW kb b

/-- **The VSpace typing at `s`** (module docstring). -/
structure VsTy (st : machine.Store S) [L : LawfulStore st] (kb : U64) (Pp Tb : Set U64) (Lv : U64 → Nat) (s : S) :
    Prop where
  tbl : ∀ o : U64, 772352 ≤ o.val → o.val < 773376 → o.val % 8 = 0 → L.mem s (wa kb o) ≠ 0#u64 →
    L.mem s (wa kb o) ∈ Pp
  pool : ∀ p ∈ Pp, ∀ o : U64, o.val < 4096 → o.val % 8 = 0 → L.mem s (wa p o) ≠ 0#u64 →
    ((L.mem s (wa p o) &&& 3#u64) = 0#u64 → L.mem s (wa p o) ∈ Tb ∧ Lv (L.mem s (wa p o)) = 0) ∧
    ((L.mem s (wa p o) &&& 3#u64) = 2#u64 →
      (L.mem s (wa p o) &&& ~~~3#u64) ∈ Tb ∧ Lv (L.mem s (wa p o) &&& ~~~3#u64) = 0)
  desc : ∀ p ∈ Tb, Lv p < 3 → ∀ o : U64, o.val < 4096 → o.val % 8 = 0 → (L.mem s (wa p o) &&& 3#u64) = 3#u64 →
    wa (L.mem s (wa p o) &&& vspace.ADDR_MASK) layout.PPTR_BASE ∈ Tb ∧
      Lv (wa (L.mem s (wa p o) &&& vspace.ADDR_MASK) layout.PPTR_BASE) = Lv p + 1

/-- **Every `VsR` word kept or made `0`.** -/
def VsZ (st : machine.Store S) [L : LawfulStore st] (kb : U64) (Pt : Set U64) (s s' : S) : Prop :=
  ∀ b, VsR kb Pt b → L.mem s' b = L.mem s b ∨ L.mem s' b = 0#u64

theorem VsZ.refl {kb : U64} {Pt : Set U64} (s : S) : VsZ st kb Pt s s := fun _ _ => Or.inl rfl

theorem VsZ.trans {kb : U64} {Pt : Set U64} {s1 s2 s3 : S} (h1 : VsZ st kb Pt s1 s2) (h2 : VsZ st kb Pt s2 s3) :
    VsZ st kb Pt s1 s3 := fun b hb => by
  rcases h2 b hb with e | e
  · rw [e]; exact h1 b hb
  · exact Or.inr e

/-- Every `VsR` word kept is a `VsZ` step. -/
theorem VsZ.of_keep {kb : U64} {Pt : Set U64} {s s' : S} (h : ∀ b, VsR kb Pt b → L.mem s' b = L.mem s b) :
    VsZ st kb Pt s s' := fun b hb => Or.inl (h b hb)

/-- A write set missing every `VsR` word is a `VsZ` step. -/
theorem VsZ.of_w {kb : U64} {Pt : Set U64} {s s' : S} {F : U64 → Prop} (hal : ∀ b, VsR kb Pt b → Aligned b)
    (hw : WritesIn st s s' F) (hF : ∀ b, VsR kb Pt b → ¬ F b) : VsZ st kb Pt s s' :=
  VsZ.of_keep fun b hb => hw.mem_eq (hal b hb) (hF b hb)

/-- **Writing `0` to an aligned word** is a `VsZ` step. -/
theorem VsZ.wr0 {kb : U64} {Pt : Set U64} {s : S} {b : U64} (hal : ∀ b, VsR kb Pt b → Aligned b) (hb : Aligned b) :
    VsZ st kb Pt s (L.wr s b 0#u64) := fun b' hb' => by
  by_cases e : b = b'
  · subst e; exact Or.inr (L.mem_wr_same hb)
  · exact Or.inl (L.mem_wr_ne hb (hal b' hb') (fun h => e (UScalar.eq_of_val_eq h)))

theorem ptw_mono {P Q : Set U64} (h : P ⊆ Q) {b : U64} (hb : PtW P b) : PtW Q b := by
  obtain ⟨p, hp, o, ho, h8, e⟩ := hb
  exact ⟨p, h hp, o, ho, h8, e⟩

/-- **`VsTy` along a `VsZ` step** (the ghost pools and tables inside `Pt`). -/
theorem VsTy.keepZ {kb : U64} {Pp Tb Pt : Set U64} {Lv : U64 → Nat} {s s' : S} (hPp : Pp ⊆ Pt) (hTb : Tb ⊆ Pt)
    (h : VsTy st kb Pp Tb Lv s) (k : VsZ st kb Pt s s') : VsTy st kb Pp Tb Lv s' := by
  refine ⟨fun o h1 h2 h8 hne => ?_, fun p hp o ho h8 hne => ?_, fun p hp hl o ho h8 h3 => ?_⟩
  · rcases k _ (Or.inr ⟨o, h1, h2, h8, rfl⟩) with e | e
    · rw [e] at hne ⊢; exact h.tbl o h1 h2 h8 hne
    · exact absurd e hne
  · rcases k _ (Or.inl (ptw_mono hPp ⟨p, hp, o, ho, h8, rfl⟩)) with e | e
    · rw [e] at hne ⊢; exact h.pool p hp o ho h8 hne
    · exact absurd e hne
  · rcases k _ (Or.inl (ptw_mono hTb ⟨p, hp, o, ho, h8, rfl⟩)) with e | e
    · rw [e] at h3 ⊢; exact h.desc p hp hl o ho h8 h3
    · rw [e] at h3; exact absurd h3 (by decide)

/-! ## The walk -/

theorem and511 (x : U64) : (x &&& 511#u64).val ≤ 511 := by
  rw [UScalar.val_and]; exact Nat.le_trans Nat.and_le_right (by simp)

theorem and127 (x : U64) : (x &&& 127#u64).val ≤ 127 := by
  rw [UScalar.val_and]; exact Nat.le_trans Nat.and_le_right (by simp)

theorem mul8_val {x : U64} (hx : x.val ≤ 511) : (core.num.U64.wrapping_mul x 8#u64).val = x.val * 8 := by
  simp [core.num.U64.wrapping_mul_val_eq, U64.size_def, U64.numBits]; omega

/-- **`entry_addr`** is a word of the table at an offset below 4096. -/
theorem vspace.entry_addr.off (t v sh : U64) :
    vspace.entry_addr t v sh ⦃ r => ∃ o : U64, o.val < 4096 ∧ o.val % 8 = 0 ∧ r = wa t o ⦄ := by
  unfold vspace.entry_addr
  simp only [lift, bind_ok]
  have h63 : (sh &&& 63#u64).val < 64 := by
    rw [UScalar.val_and]; exact Nat.lt_of_le_of_lt Nat.and_le_right (by simp)
  step as ⟨i1, _⟩
  all_goals first
    | exact (WP.spec_ok _).2 ⟨core.num.U64.wrapping_mul (i1 &&& 511#u64) 8#u64,
        by rw [mul8_val (and511 i1)]; have := and511 i1; omega, by rw [mul8_val (and511 i1)]; omega, rfl⟩
    | exact ⟨core.num.U64.wrapping_mul (i1 &&& 511#u64) 8#u64,
        by rw [mul8_val (and511 i1)]; have := and511 i1; omega, by rw [mul8_val (and511 i1)]; omega, rfl⟩

/-- `is_table e sh = true` only for `e & 3 = 3`. -/
theorem vspace.is_table.tag (e sh : U64) :
    vspace.is_table e sh ⦃ b => b = true → (e &&& 3#u64) = 3#u64 ⦄ := by
  unfold vspace.is_table
  split
  · rw [eq_of_spec_fd P0.Consts.vspace.D_VALID.spec, eq_of_spec_fd P0.Consts.vspace.D_TABLE_OR_PAGE.spec]
    simp only [lift, bind_ok]
    refine (WP.spec_ok _).2 fun hb => ?_
    have e3 : (1#u64 ||| 2#u64) = 3#u64 := by decide
    rw [e3] at hb
    simpa using hb
  · exact (WP.spec_ok _).2 fun hb => by cases hb

/-- The loop invariant of `lookup_pt_slot_loop`: the slot is a word of a table of `Tb` of level `3 - level`. -/
def LkI (Tb : Set U64) (Lv : U64 → Nat) (x : U64 × U64 × U64) : Prop :=
  x.2.2.val ≤ 3 ∧ x.1.val = 12 + 9 * x.2.2.val ∧
    ∃ p ∈ Tb, Lv p + x.2.2.val = 3 ∧ ∃ o : U64, o.val < 4096 ∧ o.val % 8 = 0 ∧ x.2.1 = wa p o

set_option maxHeartbeats 2000000 in
/-- **The page-table walk stays in `Tb`.** -/
theorem vspace.lookup_pt_slot_loop.ty {kb : U64} {Pp Tb : Set U64} {Lv : U64 → Nat} {s : S}
    (h : VsTy st kb Pp Tb Lv s) (vaddr shift slot level : U64) (hi : LkI Tb Lv (shift, slot, level)) :
    vspace.lookup_pt_slot_loop st s vaddr shift slot level ⦃ r => PtW Tb r.2 ⦄ := by
  unfold vspace.lookup_pt_slot_loop
  apply loop.spec_decr_nat (measure := fun x => x.2.2.val) (inv := LkI Tb Lv)
  · rintro ⟨sh, sl, lv⟩ ⟨hl3, hsh, p, hp, hlv, o, ho, h8, e⟩
    simp only at hl3 hsh hlv e
    subst e
    dsimp only
    unfold vspace.lookup_pt_slot_loop.body
    split
    · rename_i hpos
      have hpos' : 0 < lv.val := by simpa using hpos
      rw [L.read_eq, bind_ok]
      refine WP.spec_bind (vspace.is_table.tag _ sh) fun b hb => ?_
      split
      · rename_i hbt
        obtain ⟨hT, hL⟩ := h.desc p hp (by omega) o ho h8 (hb hbt)
        step as ⟨lv1, hlv1⟩
        simp only [lift, bind_ok, vspace.table_of, layout.pptr]
        refine WP.spec_bind (vspace.entry_addr.off _ vaddr _) fun sl1 ⟨o1, ho1, h81, e1⟩ => ?_
        refine (WP.spec_ok _).2 ⟨⟨?_, ?_, _, hT, ?_, o1, ho1, h81, e1⟩, ?_⟩
        · simp only; omega
        · simp only
          have h9 : (core.num.U64.wrapping_sub sh 9#u64).val = sh.val - 9 := by
            simp [core.num.U64.wrapping_sub_val_eq, U64.size_def, U64.numBits]; omega
          rw [h9]; omega
        · simp only; rw [hL]; omega
        · show lv1.val < lv.val
          omega
      · exact (WP.spec_ok _).2 ⟨p, hp, o, ho, h8, rfl⟩
    · exact (WP.spec_ok _).2 ⟨p, hp, o, ho, h8, rfl⟩
  · exact hi

/-- **`lookup_pt_slot` from a level-0 root of `Tb` finds a `PtW Tb` word.** -/
theorem vspace.lookup_pt_slot.ty {kb : U64} {Pp Tb : Set U64} {Lv : U64 → Nat} {s : S}
    (h : VsTy st kb Pp Tb Lv s) {root : U64} (hr : root ∈ Tb) (h0 : Lv root = 0) (vaddr : U64) :
    vspace.lookup_pt_slot st s root vaddr ⦃ lu => PtW Tb lu.slot ⦄ := by
  unfold vspace.lookup_pt_slot
  refine WP.spec_bind (vspace.entry_addr.off root vaddr vspace.TOP_LEVEL_SHIFT) fun sl ⟨o, ho, h8, e⟩ => ?_
  have hi : LkI Tb Lv (vspace.TOP_LEVEL_SHIFT, sl, 3#u64) := by
    unfold LkI; exact ⟨by simp, by simp, root, hr, by simp [h0], o, ho, h8, e⟩
  refine WP.spec_bind (vspace.lookup_pt_slot_loop.ty h vaddr _ sl 3#u64 hi) ?_
  rintro ⟨sh, sl1⟩ hs
  exact (WP.spec_ok _).2 hs

/-! ## The ASID side -/

/-- **`asid_table`** reads an ASID-table word. -/
theorem vspace.asid_table.w (s : S) (i : U64) :
    vspace.asid_table st s i ⦃ pool => ∃ o : U64, 772352 ≤ o.val ∧ o.val < 773376 ∧ o.val % 8 = 0 ∧
      pool = L.mem s (wa (L.ksb s) o) ⦄ := by
  unfold vspace.asid_table
  rw [eq_of_spec_fd P0.Consts.vspace.N_ASID_POOLS.spec, eq_of_spec_fd P0.Consts.layout.ks.ASID_TABLE.spec]
  step as ⟨i1, hi1⟩
  try (have e1 : i1 = 127#u64 := UScalar.eq_of_val_eq (by scalar_tac)
       subst e1)
  simp only [lift, bind_ok]
  refine WP.spec_mono (obj.ks_get.spec s _) fun pool e => ⟨_, ?_, ?_, ?_, e⟩
  · have : (i.val &&& 127) ≤ 127 := Nat.and_le_right
    simp [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq, U64.size_def, U64.numBits] <;> omega
  · have : (i.val &&& 127) ≤ 127 := Nat.and_le_right
    simp [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq, U64.size_def, U64.numBits] <;> omega
  · have : (i.val &&& 127) ≤ 127 := Nat.and_le_right
    simp [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq, U64.size_def, U64.numBits] <;> omega

/-- **QueueVsPt's `PtPool` at a `VsTy` state** (its `ks` base `kb`). -/
theorem VsTy.ptPool {kb : U64} {Pp Tb Pt : Set U64} {Lv : U64 → Nat} {s : S} (hPp : Pp ⊆ Pt)
    (h : VsTy st kb Pp Tb Lv s) (hk : L.ksb s = kb) (asid : U64) : PtPool st Pt s asid := by
  intro i
  refine WP.spec_mono (vspace.asid_table.w s i) fun pool ⟨o, h1, h2, h8, e⟩ hp0 => ?_
  rw [hk] at e
  have hpP : pool ∈ Pp := by rw [e]; exact h.tbl o h1 h2 h8 (by rw [← e]; exact hp0)
  refine ptw_mono hPp ⟨pool, hpP, _, ?_, ?_, rfl⟩
  · rw [mul8_val (and511 asid)]; have := and511 asid; omega
  · rw [mul8_val (and511 asid)]; omega

set_option maxHeartbeats 2000000 in
/-- `find_asid_raw` returns a nonzero entry of a pool of `Pp`. -/
theorem vspace.find_asid_raw.ty {kb : U64} {Pp Tb : Set U64} {Lv : U64 → Nat} {s : S}
    (h : VsTy st kb Pp Tb Lv s) (hk : L.ksb s = kb) (asid : U64) :
    vspace.find_asid_raw st s asid ⦃ r => ∀ r1, r = .Ok r1 →
      ∃ p ∈ Pp, ∃ o : U64, o.val < 4096 ∧ o.val % 8 = 0 ∧ r1 = L.mem s (wa p o) ∧ r1 ≠ 0#u64 ⦄ := by
  unfold vspace.find_asid_raw
  step as ⟨i, _⟩
  split
  · exact (WP.spec_ok _).2 fun r1 e => by cases e
  step as ⟨i1, _⟩
  refine WP.spec_bind (vspace.asid_table.w s i1) fun pool ⟨o, h1, h2, h8, e⟩ => ?_
  split
  · exact (WP.spec_ok _).2 fun r1 e => by cases e
  rename_i hp0
  rw [hk] at e
  have hpP : pool ∈ Pp := by rw [e]; exact h.tbl o h1 h2 h8 (by rw [← e]; exact hp0)
  simp only [lift, bind_ok, L.read_eq]
  split
  · exact (WP.spec_ok _).2 fun r1 e => by cases e
  rename_i hr0
  refine (WP.spec_ok _).2 fun r1 er => ?_
  cases er
  refine ⟨pool, hpP, _, ?_, ?_, rfl, hr0⟩
  · rw [mul8_val (and511 asid)]; have := and511 asid; omega
  · rw [mul8_val (and511 asid)]; omega

theorem rtag : vspace.ROOT_TAG = 3#u64 := by unfold vspace.ROOT_TAG; rfl
theorem rs1 : vspace.ROOT_S1 = 0#u64 := by unfold vspace.ROOT_S1; rfl
theorem rhigh : vspace.ROOT_HIGH = 2#u64 := by unfold vspace.ROOT_HIGH; rfl

set_option maxHeartbeats 2000000 in
/-- **`unmap_root` returns a level-0 root of `Tb`.** -/
theorem vspace.unmap_root.ty {kb : U64} {Pp Tb : Set U64} {Lv : U64 → Nat} {s : S}
    (h : VsTy st kb Pp Tb Lv s) (hk : L.ksb s = kb) (asid : U64) :
    vspace.unmap_root st s asid ⦃ o => ∀ root high, o = some (root, high) → root ∈ Tb ∧ Lv root = 0 ⦄ := by
  unfold vspace.unmap_root
  refine WP.spec_bind (vspace.find_asid_raw.ty h hk asid) fun r hr => ?_
  rcases r with r1 | e
  · obtain ⟨p, hp, o, ho, h8, er, hr0⟩ := hr r1 rfl
    have hpl := h.pool p hp o ho h8 (by rw [← er]; exact hr0)
    rw [← er] at hpl
    simp only [lift, bind_ok, rtag, rs1, rhigh]
    split
    · rename_i h0
      exact (WP.spec_ok _).2 fun root high e => by
        cases e; exact hpl.1 h0
    · split
      · rename_i h2
        exact (WP.spec_ok _).2 fun root high e => by
          cases e; exact hpl.2 h2
      · exact (WP.spec_ok _).2 fun root high e => by cases e
  · exact (WP.spec_ok _).2 fun root high e => by cases e

/-- **QueueVsPt's `PtWalk` at a `VsTy` state** (its `ks` base `kb`). -/
theorem VsTy.ptWalk {kb : U64} {Pp Tb Pt : Set U64} {Lv : U64 → Nat} {s : S} (hTb : Tb ⊆ Pt)
    (h : VsTy st kb Pp Tb Lv s) (hk : L.ksb s = kb) (asid vaddr : U64) : PtWalk st Pt s asid vaddr := by
  intro root high hr
  have hs := vspace.unmap_root.ty h hk asid
  rw [hr] at hs
  obtain ⟨hrT, h0⟩ := (WP.spec_ok _).1 hs root high rfl
  exact WP.spec_mono (vspace.lookup_pt_slot.ty h hrT h0 vaddr) fun lu hlu => ptw_mono hTb hlu

/-! ## The VSpace finalisers write `0` to one `Pt` word -/

/-- "The state is unchanged, or one `PtW Pt` word is written `0`." -/
def Wr0 (st : machine.Store S) [L : LawfulStore st] (Pt : Set U64) (s s' : S) : Prop :=
  s' = s ∨ ∃ b, PtW Pt b ∧ s' = L.wr s b 0#u64

theorem Wr0.refl {Pt : Set U64} (s : S) : Wr0 st Pt s s := Or.inl rfl

/-- A `Wr0` step is a `VsZ` step. -/
theorem Wr0.vsz {kb : U64} {Pt : Set U64} {s s' : S} (hal : ∀ b, VsR kb Pt b → Aligned b) (h : Wr0 st Pt s s') :
    VsZ st kb Pt s s' := by
  rcases h with rfl | ⟨b, hb, rfl⟩
  · exact VsZ.refl _
  · exact VsZ.wr0 hal (hal b (Or.inl hb))

/-- A `Wr0` step writes only `PtW Pt` words. -/
theorem Wr0.w {Pt : Set U64} {s s' : S} (hal : ∀ b, PtW Pt b → Aligned b) (h : Wr0 st Pt s s') :
    WritesIn st s s' (PtW Pt) := by
  rcases h with rfl | ⟨b, hb, rfl⟩
  · exact WritesIn.refl _ _
  · exact (writesIn_wr (hal b hb)).mono fun b' e => by rw [e]; exact hb

/-- **`unmap_page`**: unchanged, or the slot `lookup_pt_slot` finds written `0`. -/
theorem vspace.unmap_page.z {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (size : capability.FrameSize) (asid vaddr pptr : U64) {Pt : Set U64} (hpt : PtWalk st Pt s asid vaddr) :
    vspace.unmap_page st ar s a size asid vaddr pptr ⦃ r => Wr0 st Pt s r.1 ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold vspace.unmap_page
  obtain ⟨o, ho⟩ := DPF.spec_tot (P0.vspace.unmap_root.p0 st s asid hS)
  rw [ho, bind_ok]
  rcases o with _ | ⟨root, high⟩
  · exact (WP.spec_ok _).2 (Wr0.refl _)
  try dsimp only
  refine WP.spec_bind (hpt root high ho) fun lu hlu => ?_
  refine WP.spec_bind (P0.vspace.page_shift.p0 size) fun sh _ => ?_
  split
  · exact (WP.spec_ok _).2 (Wr0.refl _)
  step with LawfulStore.read_spec as ⟨e, _⟩
  refine WP.spec_bind (P0.vspace.is_page.p0 e lu.shift) fun b _ => ?_
  split
  · refine WP.spec_bind (P0.vspace.page_base.p0 e lu.shift) fun pb _ => ?_
    refine WP.spec_bind (P0.layout.paddr.p0 pptr) fun pa _ => ?_
    split
    · exact (WP.spec_ok _).2 (Wr0.refl _)
    step with LawfulStore.write_spec as ⟨s1, e1⟩
    split
    · refine WP.spec_bind (hA.invalidate_high_page a vaddr) fun a1 _ => ?_
      rw [WP.spec_ok, e1]; exact Or.inr ⟨_, hlu, rfl⟩
    · refine WP.spec_bind (hA.invalidate_page a asid vaddr) fun a1 _ => ?_
      rw [WP.spec_ok, e1]; exact Or.inr ⟨_, hlu, rfl⟩
  · exact (WP.spec_ok _).2 (Wr0.refl _)

/-- **`delete_asid`**: unchanged, or the pool entry written `0`. -/
theorem vspace.delete_asid.z {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (asid root : U64) {Pt : Set U64} (hpool : PtPool st Pt s asid) :
    vspace.delete_asid st ar s a asid root ⦃ r => Wr0 st Pt s r.1 ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold vspace.delete_asid
  step as ⟨i, _⟩
  refine WP.spec_bind (hpool i) fun pool hp => ?_
  split
  · exact (WP.spec_ok _).2 (Wr0.refl _)
  rename_i hp0
  have he := hp hp0
  simp only [lift, bind_ok]
  step with LawfulStore.read_spec as ⟨v, _⟩
  split
  · refine WP.spec_bind (Pₘ := fun _ => True) ?_ fun a1 _ => ?_
    · split
      · exact hA.invalidate_stage2_vmid a asid
      · split
        · exact hA.invalidate_high_vspace a _
        · exact hA.invalidate_asid a asid
    step with LawfulStore.write_spec as ⟨s1, e1⟩
    step with sched.cur_thread.spec as ⟨ct, _⟩
    refine WP.spec_mono (vspace.set_vm_root.same hA s1 a1 ct) fun r e => ?_
    rw [e, e1]; exact Or.inr ⟨_, he, rfl⟩
  · exact (WP.spec_ok _).2 (Wr0.refl _)

/-- **A non-EPT, non-device frame's finalisation** (any finality): `(Null, Null)`, a `Wr0` step. -/
theorem fin_frame.z {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (ptr : U64) (size : capability.FrameSize) (rights : U64) (mapped : Bool) (asid vaddr : U64) (fin : Bool)
    {Pt : Set U64} (hpt : PtWalk st Pt s asid vaddr) :
    objects.finalise_cap_object st ar s a (.Frame ptr size rights false mapped false asid vaddr) fin ⦃ r =>
      r.1 = (.Null, .Null) ∧ Wr0 st Pt s r.2.1 ⦄ := by
  unfold objects.finalise_cap_object
  dsimp only
  refine WP.spec_bind (Pₘ := fun r : S × A => Wr0 st Pt s r.1) ?_ ?_
  · split
    · split
      · simp only [Bool.false_eq_true, ↓reduceIte]
        exact vspace.unmap_page.z hA s a size asid vaddr ptr hpt
      · exact (WP.spec_ok _).2 (Wr0.refl _)
    · exact (WP.spec_ok _).2 (Wr0.refl _)
  rintro ⟨s1, a1⟩ w1
  try dsimp only
  cases fin <;> (try simp only [Bool.false_eq_true, ↓reduceIte]) <;> exact (WP.spec_ok _).2 ⟨rfl, w1⟩

/-- **A VSpace-root (`Pml4`) cap's finalisation**: `(Null, Null)`, a `Wr0` step. -/
theorem fin_root.z {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (ptr : U64) (mapped : Bool) (asid : U64) (fin : Bool) {Pt : Set U64} (hpool : PtPool st Pt s asid) :
    objects.finalise_cap_object st ar s a (.Pml4 ptr mapped asid) fin ⦃ r =>
      r.1 = (.Null, .Null) ∧ Wr0 st Pt s r.2.1 ⦄ := by
  unfold objects.finalise_cap_object
  dsimp only
  split
  · split
    · refine WP.spec_bind (vspace.delete_asid.z hA s a asid ptr hpool) ?_
      rintro ⟨s1, a1⟩ w1
      exact (WP.spec_ok _).2 ⟨rfl, w1⟩
    · exact (WP.spec_ok _).2 ⟨rfl, Wr0.refl _⟩
  · exact (WP.spec_ok _).2 ⟨rfl, Wr0.refl _⟩

/-- **A `HighVSpace` cap's finalisation**: `(Null, Null)`, a `Wr0` step. -/
theorem fin_hvs.z {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (ptr : U64) (mapped : Bool) (asid : U64) (fin : Bool) {Pt : Set U64} (hpool : PtPool st Pt s asid) :
    objects.finalise_cap_object st ar s a (.HighVSpace ptr mapped asid) fin ⦃ r =>
      r.1 = (.Null, .Null) ∧ Wr0 st Pt s r.2.1 ⦄ := by
  unfold objects.finalise_cap_object
  dsimp only
  split
  · split
    · try simp only [lift, bind_ok]
      refine WP.spec_bind (vspace.delete_asid.z hA s a asid _ hpool) ?_
      rintro ⟨s1, a1⟩ w1
      exact (WP.spec_ok _).2 ⟨rfl, w1⟩
    · exact (WP.spec_ok _).2 ⟨rfl, Wr0.refl _⟩
  · exact (WP.spec_ok _).2 ⟨rfl, Wr0.refl _⟩

end

end Fl4ProofsA64.P1
