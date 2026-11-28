/-
P1 (aarch64, gen 41): **the VSpace typings `VsTy ∧ S2Ty` along the VSpace-writing steps** — the deletion, the
unmap walks, and the data steps of the map / assign writes — and the **entry fact with the Stage-2 typing**, new
[J] `SlotTyEntE`, so the `_ent` decode takes `S2Ty`, `HrOK`, `S2OK` and the Stage-2 placement from the entry fact
instead of case hypotheses.

**Which form (gen 41, goal 1).** A64 has no proved all-steps invariant record: the entry-state bundle is the family
of [J] entry facts `SlotTyEnt*` (QueueSlotTy … QueueZombieQDec), assumed at `P3Ok` states; `JV` (QueueVcTy) is the
deletion's step relation (`J ∧ VcTy`), not a reachability invariant. Proving `VsTy ∧ S2Ty` preserved by **every**
A64 kernel step that writes VSpace words or caps needs, beyond the walks below, the decode-level ARMPageTableMap /
Unmap (cap and thread-state writes, the `zero(ptr, 4096)` of an unmapped table), `ept::map_table` /
`ept::map_frame` / `install_s2_leaf`, Stage-1 `decode_page_map` / `map_high_page_table`, ASIDPool `Assign`,
ASIDControl `MakePool`, `create_new_objects` for the VSpace kinds, and the reachability facts those need ("an
unmapped page-table cap names a zeroed object", "an unmapped `Ept` root is zeroed") — far more than one generation.
So the typing is **folded into a widened entry fact** (cheapest honest form), and preservation is proved for the
steps that can be closed now.

* **Deletion keeps the typing** (QueueZombieQ's gen-41 `zqIGT`): **`cdt.delete.zqET`**, **`cdt.delete.threadQET`**
  (post `JV ∧ VsTy ∧ S2Ty`).
* **Unmap walks keep it**: **`ept.unmap.ty`**, **`ept.unmap_table.ty`**, **`vspace.unmap_page_table.ty`** (all three
  branches), **`vspace.unmap_page.ty`** (Stage-1 frames); each writes only `VsR` words.
* **Write lemmas** (pure state; the data part of the map / assign steps): `mem_wr_cases`, **`VsTy.wr`**,
  **`S2Ty.wr`** (a word written with a value meeting the clause of every typing position it occupies),
  **`S2Ty.addT`** (a new table / root with no descriptor-like word joins `Te`), `S2Ty.congr` (`Re`, `bits` read only
  on `Te`), `S2OK.addT`, `gran_insert`; **`S2Ty.map_table`** (`ept::map_table`'s descriptor write,
  ept.rs:174–197: a `Te` table one level up, the new table joining `Te` one level down), **`S2Ty.assign1`** /
  **`VsTy.assign1`** (ASIDPool `Assign` with `ROOT_S2`, vspace.rs:1239–1261: the pool word `root | 1`, the root
  joining `Te` at depth `s2lv n − 1`).
* **[J] `SlotTyEntE n`** (new, named): [J] `SlotTyEntP`'s fields (QueueZombieQDec) and, for the same ghost sets,
  `HighVSpace` roots `Hr`, Stage-2 objects `Te` with depth `Re` and sizes `bits`: `Gran Te bits ⊆ Pt`,
  `HrOK (ks e) Pp Tb Lv Hr`, `S2OK Te bits Hr`, `S2Ty st n Pp Hr Te Re bits e`. `SlotTyEntE.toP`,
  **`SlotTyEntE.entAt`** (its facts at every `EntAt` state: the entry prefix writes no `VsR` word, `VsEntApart`),
  **`syscall.decode_invocation.del_zqE_entE`** (gen 40's `del_zqE_ent` with `S2Ty`, `HrOK`, `S2OK` and the Stage-2
  placement from the entry fact; only the deletion's domain facts remain case hypotheses).

**Source for [J] `SlotTyEntE`** (crates/fl4-core/src/…), beyond QueueZombieQDec's for `SlotTyEntP`:
* Placement (`Gran Te bits ⊆ Pt` with `VrOK … Pt`, `S2OK`, `HrOK`): a Stage-2 root is an `ArmStage2VSpace` object
  retyped with `bits::STAGE2_VSPACE = 13` (objects.rs:42, arch/aarch64/objects.rs:26/55, fl4-abi consts.rs:98),
  Stage-2 tables are 12-bit `ArmPageTable` objects (arch/aarch64/objects.rs:48), all from `create_new_objects`
  (objects.rs:528), size-aligned and disjoint from every other object, `HighVSpace` roots included (so no Stage-2
  word is an `R + 4088` word, no pool or ASID-table word is one, a Stage-1 table word equal to `R + 4088` is `R`'s).
* `S2Ty.tag`: pool words are written only by ASIDPool `Assign` (vspace.rs:1239–1261: tag 0 `Pml4`, 1 `Ept`
  level 0, 2 `HighVSpace`, each with an **unmapped** cap — and `derive_cap` (objects.rs:207–231) refuses to copy an
  unmapped VSpace / table cap, so an unmapped cap is the object's only cap) and cleared by `delete_asid`
  (vspace.rs:529–549).
* `S2Ty.hi`: `init_high_vspace` (vspace.rs:276–297) writes entry 511 as a table descriptor; no path clears it while
  the root is assigned (`map_high_page_table`, 1146–1165, refuses the top level).
* `S2Ty.desc` (with `Te` the tables reachable from live tag-1 pool entries, `Re` the remaining depth): descriptors
  with `e & 3 = 3` below the last level are written only by `ept::map_table` (ept.rs:174–197: into an **invalid**
  slot found by `lookup_slot` with `shift ≠ PAGE_BITS`, so `rem > 0`, naming the 12-bit table of an unmapped
  `PageTable` cap, one level down); leaves at `shift = 12` (`rem = 0`, `make_s2_leaf`, ept.rs:97–117) are where
  `desc` asks nothing; blocks have `e & 3 = 1`; `unmap_table` (200–232) and ARMPageTableUnmap (vspace.rs:1097–1107:
  the walk's slot cleared, then the table **zeroed**) clear. A table reachable along two paths would need a second
  `map_table` of a table whose cap is mapped (refused, vspace.rs:1116) or of a stale table (zeroed by Unmap before
  its cap becomes unmapped), so the depth is a function. `n` is the [P] constant of `ArchPlat`.
Checked not false on reachable states as far as the source shows (ghost sets chosen per entry state; at the boot
state there are no Stage-2 objects, `Te = ∅`, `S2Ty` is gen 39's `HrTy`).

**Preservation still owed** (for discharging the [J] from the steps): ARMPageTableMap (Stage-2 via `ept::map_table`:
the descriptor write is `S2Ty.map_table`, the cap / thread-state writes are outside `VsR`; owed: the function-level
lemma and "an unmapped table cap's object is zero"), ARMPageTableUnmap (`vspace.unmap_page_table.ty` + the `zero`
of the table), `ept::map_frame` / `install_s2_leaf` (leaf / block writes, `e & 3 ≠ 3` above the last level),
Stage-1 `decode_page_map` / table map / `map_high_page_table` (`VsTy`), ASIDPool `Assign` (the pool write is
`S2Ty.assign1` / `VsTy.assign1`; owed: the decode-level lemma and "an unmapped `Ept` root is zero"), ASIDControl
`MakePool` (`clear_free` + `set_asid_table`), `create_new_objects` / untyped reset of VSpace kinds (new zeroed
objects outside the ghost sets).

Named premises: **[J] `SlotTyEntE`** (new); [P] `ArchPlat.s2_ipa_bits_const` (QueueS2Ty), consumed via `hPl`.
-/
import Fl4ProofsA64.P1.QueueS2K
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64} {P3Ok : S → Prop} {U : Set U64}

local notation "wa" => core.num.U64.wrapping_add

namespace W7
namespace R
namespace ST

/-! ## Writes -/

/-- A read after an aligned write: the written word, or an unchanged other word. -/
theorem mem_wr_cases {s : S} {b v w : U64} (hb : Aligned b) (hw : Aligned w) :
    (w = b ∧ L.mem (L.wr s b v) w = v) ∨ (w ≠ b ∧ L.mem (L.wr s b v) w = L.mem s w) := by
  by_cases e : w = b
  · subst e; exact Or.inl ⟨rfl, L.mem_wr_same hb⟩
  · exact Or.inr ⟨e, L.mem_wr_ne hb hw fun h => e (UScalar.eq_of_val_eq h).symm⟩

/-- `S2Ty.tag`'s clause for a pool value. -/
abbrev TagC (n : U64) (Hr Te : Set U64) (Re bits : U64 → Nat) (x : U64) : Prop :=
  ((x &&& 3#u64) = 0#u64 ∧ x ∉ Hr) ∨ ((x &&& 3#u64) = 2#u64 ∧ (x &&& ~~~3#u64) ∈ Hr) ∨
    ((x &&& 3#u64) = 1#u64 ∧ (x &&& ~~~3#u64) ∈ Te ∧ Re (x &&& ~~~3#u64) + 1 = s2lv n ∧
      s2rb n ≤ bits (x &&& ~~~3#u64))

/-- `S2Ty.desc`'s clause for a descriptor value in a table of depth `r`. -/
abbrev DescC (Te : Set U64) (Re : U64 → Nat) (x : U64) (r : Nat) : Prop :=
  wa (x &&& ept.ADDR_MASK) layout.PPTR_BASE ∈ Te ∧ Re (wa (x &&& ept.ADDR_MASK) layout.PPTR_BASE) + 1 = r

/-- `VsTy.pool`'s clause for a pool value. -/
abbrev PoolC (Tb : Set U64) (Lv : U64 → Nat) (x : U64) : Prop :=
  ((x &&& 3#u64) = 0#u64 → x ∈ Tb ∧ Lv x = 0) ∧ ((x &&& 3#u64) = 2#u64 → (x &&& ~~~3#u64) ∈ Tb ∧ Lv (x &&& ~~~3#u64) = 0)

/-- `VsTy.desc`'s clause for a descriptor value in a table of level `l`. -/
abbrev VDescC (Tb : Set U64) (Lv : U64 → Nat) (x : U64) (l : Nat) : Prop :=
  wa (x &&& vspace.ADDR_MASK) layout.PPTR_BASE ∈ Tb ∧ Lv (wa (x &&& vspace.ADDR_MASK) layout.PPTR_BASE) = l + 1

section wrs
variable {kb n : U64} {Pp Tb Pt Hr Te : Set U64} {Lv Re bits : U64 → Nat}

/-- **`VsTy` after one aligned write** whose value meets the clause of every `VsTy` position the word occupies. -/
theorem VsTy.wr (hal : ∀ w, VsR kb Pt w → Aligned w) (hPp : Pp ⊆ Pt) (hTb : Tb ⊆ Pt) {s : S} {b v : U64}
    (hb : Aligned b) (h : VsTy st kb Pp Tb Lv s)
    (ht : ∀ o : U64, 772352 ≤ o.val → o.val < 773376 → o.val % 8 = 0 → wa kb o = b → v ≠ 0#u64 → v ∈ Pp)
    (hp : ∀ p ∈ Pp, ∀ o : U64, o.val < 4096 → o.val % 8 = 0 → wa p o = b → v ≠ 0#u64 → PoolC Tb Lv v)
    (hd : ∀ p ∈ Tb, Lv p < 3 → ∀ o : U64, o.val < 4096 → o.val % 8 = 0 → wa p o = b → (v &&& 3#u64) = 3#u64 →
      VDescC Tb Lv v (Lv p)) :
    VsTy st kb Pp Tb Lv (L.wr s b v) := by
  refine ⟨fun o h1 h2 h8 hne => ?_, fun p hp' o ho h8 hne => ?_, fun p hp' hl o ho h8 h3 => ?_⟩
  · rcases mem_wr_cases (L := L) (s := s) (v := v) hb (hal _ (Or.inr ⟨o, h1, h2, h8, rfl⟩)) with ⟨e, hm⟩ | ⟨-, hm⟩
    · rw [hm] at hne ⊢; exact ht o h1 h2 h8 e hne
    · rw [hm] at hne ⊢; exact h.tbl o h1 h2 h8 hne
  · rcases mem_wr_cases (L := L) (s := s) (v := v) hb (hal _ (Or.inl (ptw_mono hPp ⟨p, hp', o, ho, h8, rfl⟩))) with
      ⟨e, hm⟩ | ⟨-, hm⟩
    · rw [hm] at hne ⊢; exact hp p hp' o ho h8 e hne
    · rw [hm] at hne ⊢; exact h.pool p hp' o ho h8 hne
  · rcases mem_wr_cases (L := L) (s := s) (v := v) hb (hal _ (Or.inl (ptw_mono hTb ⟨p, hp', o, ho, h8, rfl⟩))) with
      ⟨e, hm⟩ | ⟨-, hm⟩
    · rw [hm] at h3 ⊢; exact hd p hp' hl o ho h8 e h3
    · rw [hm] at h3 ⊢; exact h.desc p hp' hl o ho h8 h3

/-- **`S2Ty` after one aligned write** that is no `R + 4088` word and whose value meets the clause of every
`S2Ty` position the word occupies. -/
theorem S2Ty.wr (hal : ∀ w, VsR kb Pt w → Aligned w) (hPp : Pp ⊆ Pt) (hTe : Gran Te bits ⊆ Pt)
    (hS : S2OK Te bits Hr) (hRal : ∀ R ∈ Hr, Aligned (wa R 4088#u64)) {s : S} {b v : U64} (hb : Aligned b)
    (h : S2Ty st n Pp Hr Te Re bits s)
    (hp : ∀ p ∈ Pp, ∀ o : U64, o.val < 4096 → o.val % 8 = 0 → wa p o = b → v ≠ 0#u64 → TagC n Hr Te Re bits v)
    (hh : ∀ R ∈ Hr, wa R 4088#u64 ≠ b)
    (hd : ∀ p ∈ Te, 0 < Re p → ∀ o : U64, o.val < 2 ^ bits p → o.val % 8 = 0 → wa p o = b →
      (v &&& 3#u64) = 3#u64 → DescC Te Re v (Re p)) :
    S2Ty st n Pp Hr Te Re bits (L.wr s b v) := by
  refine ⟨fun p hp' o ho h8 hne => ?_, fun R hR => ?_, fun p hp' hr o ho h8 h3 => ?_⟩
  · rcases mem_wr_cases (L := L) (s := s) (v := v) hb (hal _ (Or.inl (ptw_mono hPp ⟨p, hp', o, ho, h8, rfl⟩))) with
      ⟨e, hm⟩ | ⟨-, hm⟩
    · rw [hm] at hne ⊢; exact hp p hp' o ho h8 e hne
    · rw [hm] at hne ⊢; exact h.tag p hp' o ho h8 hne
  · rcases mem_wr_cases (L := L) (s := s) (v := v) hb (hRal R hR) with ⟨e, -⟩ | ⟨-, hm⟩
    · exact absurd e (hh R hR)
    · rw [hm]; exact h.hi R hR
  · rcases mem_wr_cases (L := L) (s := s) (v := v) hb
      (hal _ (Or.inl (ptw_mono hTe (ptwb_gran hS.sz ⟨p, hp', o, ho, h8, rfl⟩)))) with ⟨e, hm⟩ | ⟨-, hm⟩
    · rw [hm] at h3 ⊢; exact hd p hp' hr o ho h8 e h3
    · rw [hm] at h3 ⊢; exact h.desc p hp' hr o ho h8 h3

/-- **A new Stage-2 object joins `Te`** when, at a positive depth, none of its words looks like a descriptor. -/
theorem S2Ty.addT {s : S} {t : U64} (h : S2Ty st n Pp Hr Te Re bits s)
    (hz : 0 < Re t → ∀ o : U64, o.val < 2 ^ bits t → o.val % 8 = 0 → (L.mem s (wa t o) &&& 3#u64) ≠ 3#u64) :
    S2Ty st n Pp Hr (insert t Te) Re bits s := by
  refine ⟨fun p hp o ho h8 hne => ?_, h.hi, fun p hp hr o ho h8 h3 => ?_⟩
  · rcases h.tag p hp o ho h8 hne with a | a | ⟨a, b, c, d⟩
    · exact Or.inl a
    · exact Or.inr (Or.inl a)
    · exact Or.inr (Or.inr ⟨a, Set.mem_insert_of_mem _ b, c, d⟩)
  · rcases hp with rfl | hp
    · exact absurd h3 (hz hr o ho h8)
    · obtain ⟨a, b⟩ := h.desc p hp hr o ho h8 h3
      exact ⟨Set.mem_insert_of_mem _ a, b⟩

/-- **`S2Ty` reads `Re` and `bits` only on `Te`.** -/
theorem S2Ty.congr {s : S} {Re' bits' : U64 → Nat} (h : S2Ty st n Pp Hr Te Re bits s)
    (hRe : ∀ p ∈ Te, Re' p = Re p) (hbits : ∀ p ∈ Te, bits' p = bits p) : S2Ty st n Pp Hr Te Re' bits' s := by
  refine ⟨fun p hp o ho h8 hne => ?_, h.hi, fun p hp hr o ho h8 h3 => ?_⟩
  · rcases h.tag p hp o ho h8 hne with a | a | ⟨a, b, c, d⟩
    · exact Or.inl a
    · exact Or.inr (Or.inl a)
    · exact Or.inr (Or.inr ⟨a, b, by rw [hRe _ b]; exact c, by rw [hbits _ b]; exact d⟩)
  · rw [hRe p hp] at hr
    rw [hbits p hp] at ho
    obtain ⟨a, b⟩ := h.desc p hp hr o ho h8 h3
    exact ⟨a, by rw [hRe _ a, hRe p hp]; exact b⟩

/-- **`S2OK` with a new object** (its size, alignment, and no `R + 4088` word). -/
theorem S2OK.addT (hS : S2OK Te bits Hr) {t : U64} (hsz : bits t = 12 ∨ bits t = 13) (hal : 2 ^ bits t ∣ t.val)
    (hhr : ∀ o : U64, o.val < 2 ^ bits t → o.val % 8 = 0 → ∀ R ∈ Hr, wa t o ≠ wa R 4088#u64) :
    S2OK (insert t Te) bits Hr := by
  refine ⟨fun p hp => ?_, fun p hp => ?_, fun b hb => ?_⟩
  · rcases hp with rfl | hp
    · exact hsz
    · exact hS.sz p hp
  · rcases hp with rfl | hp
    · exact hal
    · exact hS.al p hp
  · obtain ⟨p, hp, o, ho, h8, rfl⟩ := hb
    rcases hp with rfl | hp
    · exact hhr o ho h8
    · exact hS.hr _ ⟨p, hp, o, ho, h8, rfl⟩

/-- The granules of `insert t Te`. -/
theorem gran_insert {t : U64} : Gran (insert t Te) bits ⊆ Gran Te bits ∪ Gran {t} bits := by
  rintro q ⟨p, hp, hq⟩
  rcases hp with rfl | hp
  · exact Or.inr ⟨p, rfl, hq⟩
  · exact Or.inl ⟨p, hp, hq⟩

/-- **`ept::map_table`'s descriptor write** (ept.rs:174–197; the data step): in a table `p ∈ Te` at a positive
depth, the slot written with a table descriptor of `t` (one level down, no descriptor-like word in `t` at a positive
depth); the slot is no pool word, and every Stage-2 object containing it is `p`. `t` joins `Te`. -/
theorem S2Ty.map_table (hal : ∀ w, VsR kb Pt w → Aligned w) (hPp : Pp ⊆ Pt) {t : U64}
    (hTe : Gran (insert t Te) bits ⊆ Pt) (hS : S2OK (insert t Te) bits Hr) (hRal : ∀ R ∈ Hr, Aligned (wa R 4088#u64))
    {s : S} (h : S2Ty st n Pp Hr Te Re bits s) {p o v : U64} (hp : p ∈ Te) (ho : o.val < 2 ^ bits p)
    (h8 : o.val % 8 = 0)
    (hun : ∀ q ∈ insert t Te, ∀ o' : U64, o'.val < 2 ^ bits q → o'.val % 8 = 0 → wa q o' = wa p o → q = p)
    (hnp : ∀ q ∈ Pp, ∀ o' : U64, o'.val < 4096 → o'.val % 8 = 0 → wa q o' ≠ wa p o)
    (hRt : Re t + 1 = Re p)
    (hz : 0 < Re t → ∀ o : U64, o.val < 2 ^ bits t → o.val % 8 = 0 → (L.mem s (wa t o) &&& 3#u64) ≠ 3#u64)
    (hvt : wa (v &&& ept.ADDR_MASK) layout.PPTR_BASE = t) :
    S2Ty st n Pp Hr (insert t Te) Re bits (L.wr s (wa p o) v) := by
  have hpi : p ∈ insert t Te := Set.mem_insert_of_mem _ hp
  have hw : PtWb (insert t Te) bits (wa p o) := ⟨p, hpi, o, ho, h8, rfl⟩
  refine S2Ty.wr hal hPp hTe hS hRal (hal _ (Or.inl (ptw_mono hTe (ptwb_gran hS.sz hw)))) (S2Ty.addT h hz)
    (fun q hq o' ho' h8' e _ => absurd e (hnp q hq o' ho' h8')) (fun R hR e => hS.hr _ hw R hR e.symm)
    (fun q hq _ o' ho' h8' e _ => ?_)
  obtain rfl := hun q hq o' ho' h8' e
  refine ⟨?_, ?_⟩
  · rw [hvt]; exact Set.mem_insert t Te
  · rw [hvt]; exact hRt

/-- **ASIDPool `Assign`'s pool write with `ROOT_S2`** (vspace.rs:1239–1261; the data step): a pool word written
`v` with tag 1 naming a root `r` of depth `s2lv n − 1` and span `≥ s2rb n` with no descriptor-like word; `r` joins
`Te`. -/
theorem S2Ty.assign1 (hal : ∀ w, VsR kb Pt w → Aligned w) (hPp : Pp ⊆ Pt) {r : U64}
    (hTe : Gran (insert r Te) bits ⊆ Pt) (hS : S2OK (insert r Te) bits Hr) (hRal : ∀ R ∈ Hr, Aligned (wa R 4088#u64))
    {s : S} (h : S2Ty st n Pp Hr Te Re bits s) {q o v : U64} (hq : q ∈ Pp) (ho : o.val < 4096) (h8 : o.val % 8 = 0)
    (hhr : ∀ R ∈ Hr, wa R 4088#u64 ≠ wa q o)
    (hv1 : (v &&& 3#u64) = 1#u64) (hvr : (v &&& ~~~3#u64) = r) (hRr : Re r + 1 = s2lv n) (hrb : s2rb n ≤ bits r)
    (hz : ∀ o : U64, o.val < 2 ^ bits r → o.val % 8 = 0 → (L.mem s (wa r o) &&& 3#u64) ≠ 3#u64) :
    S2Ty st n Pp Hr (insert r Te) Re bits (L.wr s (wa q o) v) := by
  refine S2Ty.wr hal hPp hTe hS hRal (hal _ (Or.inl (ptw_mono hPp ⟨q, hq, o, ho, h8, rfl⟩)))
    (S2Ty.addT h fun _ => hz) (fun _ _ _ _ _ _ _ => ?_) hhr (fun _ _ _ _ _ _ _ h3 => ?_)
  · exact Or.inr (Or.inr ⟨hv1, by rw [hvr]; exact Set.mem_insert r Te, by rw [hvr]; exact hRr, by rw [hvr]; exact hrb⟩)
  · rw [hv1] at h3; exact absurd h3 (by decide)

/-- **`VsTy` along ASIDPool `Assign`'s pool write with `ROOT_S2`**: a tag-1 value asks nothing of `VsTy` (the word
is no ASID-table word). -/
theorem VsTy.assign1 (hal : ∀ w, VsR kb Pt w → Aligned w) (hPp : Pp ⊆ Pt) (hTb : Tb ⊆ Pt) {s : S}
    (h : VsTy st kb Pp Tb Lv s) {q o v : U64} (hq : q ∈ Pp) (ho : o.val < 4096) (h8 : o.val % 8 = 0)
    (hnA : ¬ AsW kb (wa q o)) (hv1 : (v &&& 3#u64) = 1#u64) :
    VsTy st kb Pp Tb Lv (L.wr s (wa q o) v) := by
  refine VsTy.wr hal hPp hTb (hal _ (Or.inl (ptw_mono hPp ⟨q, hq, o, ho, h8, rfl⟩))) h
    (fun o' h1 h2 h8' e _ => (hnA ⟨o', h1, h2, h8', e.symm⟩).elim) (fun _ _ _ _ _ _ _ => ⟨fun h0 => ?_, fun h2 => ?_⟩)
    (fun _ _ _ _ _ _ _ h3 => ?_)
  · rw [hv1] at h0; exact absurd h0 (by decide)
  · rw [hv1] at h2; exact absurd h2 (by decide)
  · rw [hv1] at h3; exact absurd h3 (by decide)

end wrs

/-! ## The unmap walks keep the typing -/

section unm
variable {OS Vc Ub : Set U64} {kb : U64} {Pp Tb Pt Hr Te : Set U64} {Lv Re bits : U64 → Nat}
variable {A : Type _} {ar : machine.Arch A}

/-- **`ept::unmap` keeps `VsTy ∧ S2Ty`** and writes only `VsR` words. -/
theorem ept.unmap.ty (hA : P0.ArchTotal ar) (hPl : ArchPlat ar) (hR : VrOK Ω Sg Scs Z OS Vc Ub kb Pt)
    (hPp : Pp ⊆ Pt) (hTb : Tb ⊆ Pt) (hTe : Gran Te bits ⊆ Pt) (hO : HrOK kb Pp Tb Lv Hr) (hS : S2OK Te bits Hr)
    {s : S} (hY : VsTy st kb Pp Tb Lv s ∧ S2Ty st hPl.ipa Pp Hr Te Re bits s) (hk : L.ksb s = kb) (a : A)
    (asid ipa ptr shift : U64) (it : Bool) :
    ept.unmap st ar s a asid ipa ptr shift it ⦃ r => WritesIn st s r.1 (VsR kb Pt) ∧
      (VsTy st kb Pp Tb Lv r.1 ∧ S2Ty st hPl.ipa Pp Hr Te Re bits r.1) ⦄ :=
  WP.spec_mono (ept.unmap.z hA hPl hY.1 hY.2 hS hk a asid ipa ptr shift it) fun _ z =>
    ty_wr0s hR hPp hTb hTe hO hS hTe (fun b hb => hS.hr b (gran_ptwb hS.sz hb)) hY z

/-- **`ept::unmap_table` keeps `VsTy ∧ S2Ty`** and writes only `VsR` words. -/
theorem ept.unmap_table.ty (hA : P0.ArchTotal ar) (hPl : ArchPlat ar) (hR : VrOK Ω Sg Scs Z OS Vc Ub kb Pt)
    (hPp : Pp ⊆ Pt) (hTb : Tb ⊆ Pt) (hTe : Gran Te bits ⊆ Pt) (hO : HrOK kb Pp Tb Lv Hr) (hS : S2OK Te bits Hr)
    {s : S} (hY : VsTy st kb Pp Tb Lv s ∧ S2Ty st hPl.ipa Pp Hr Te Re bits s) (hk : L.ksb s = kb) (a : A)
    (asid ipa pt : U64) :
    ept.unmap_table st ar s a asid ipa pt ⦃ r => WritesIn st s r.1 (VsR kb Pt) ∧
      (VsTy st kb Pp Tb Lv r.1 ∧ S2Ty st hPl.ipa Pp Hr Te Re bits r.1) ⦄ :=
  WP.spec_mono (ept.unmap_table.z hA hPl hY.1 hY.2 hS hk a asid ipa pt) fun _ z =>
    ty_wr0s hR hPp hTb hTe hO hS hTe (fun b hb => hS.hr b (gran_ptwb hS.sz hb)) hY z

/-- **`unmap_page_table` keeps `VsTy ∧ S2Ty`** (all three branches) and writes only `VsR` words. -/
theorem vspace.unmap_page_table.ty (hA : P0.ArchTotal ar) (hPl : ArchPlat ar) (hR : VrOK Ω Sg Scs Z OS Vc Ub kb Pt)
    (hPp : Pp ⊆ Pt) (hTb : Tb ⊆ Pt) (hTe : Gran Te bits ⊆ Pt) (hO : HrOK kb Pp Tb Lv Hr) (hS : S2OK Te bits Hr)
    {s : S} (hY : VsTy st kb Pp Tb Lv s ∧ S2Ty st hPl.ipa Pp Hr Te Re bits s) (hk : L.ksb s = kb) (a : A)
    (asid vaddr pt : U64) :
    vspace.unmap_page_table st ar s a asid vaddr pt ⦃ r => WritesIn st s r.1 (VsR kb Pt) ∧
      (VsTy st kb Pp Tb Lv r.1 ∧ S2Ty st hPl.ipa Pp Hr Te Re bits r.1) ⦄ := by
  have hU : TbO Tb Hr ∪ Gran Te bits ⊆ Pt := fun _ h => h.elim (fun h' => hTb h'.1) (fun h' => hTe h')
  exact WP.spec_mono (vspace.unmap_page_table.s2 hA hPl hO hS hY.1 hY.2 hk a asid vaddr pt) fun _ z =>
    ty_wr0s hR hPp hTb hTe hO hS hU (fun b hb => s2_ne hO hS hb) hY z

/-- **Stage-1 `unmap_page` keeps `VsTy ∧ S2Ty`** and writes only `VsR` words. -/
theorem vspace.unmap_page.ty (hA : P0.ArchTotal ar) {n : U64} (hR : VrOK Ω Sg Scs Z OS Vc Ub kb Pt)
    (hPp : Pp ⊆ Pt) (hTb : Tb ⊆ Pt) (hTe : Gran Te bits ⊆ Pt) (hO : HrOK kb Pp Tb Lv Hr) (hS : S2OK Te bits Hr)
    {s : S} (hY : VsTy st kb Pp Tb Lv s ∧ S2Ty st n Pp Hr Te Re bits s) (hk : L.ksb s = kb) (a : A)
    (size : capability.FrameSize) (asid vaddr pptr : U64) :
    vspace.unmap_page st ar s a size asid vaddr pptr ⦃ r => WritesIn st s r.1 (VsR kb Pt) ∧
      (VsTy st kb Pp Tb Lv r.1 ∧ S2Ty st n Pp Hr Te Re bits r.1) ⦄ :=
  WP.spec_mono (vspace.unmap_page.hr hA hO hY.1 hk a size asid vaddr pptr) fun _ z =>
    ty_wr0s (X := TbO Tb Hr) hR hPp hTb hTe hO hS (fun _ h => hTb h.1) (fun b hb => hO.tbo hb) hY z

end unm

/-! ## The deletion keeps the typing -/

section del
variable {OS Vc Ub D Fp : Set U64} {Pp Tb Pt Hr Te : Set U64} {Lv Re bits : U64 → Nat}
variable {A : Type _} {ar : machine.Arch A}

/-- **The exposed `cdt.delete` of a `ZQ S2Q` slot over a domain of `ZQ S2Q` caps keeps `JV` and `VsTy ∧ S2Ty`**
(gen 40's `cdt.delete.zqE` with the typing at the end state). -/
theorem cdt.delete.zqET (hP : P0.ArchTotal ar) (hPl : ArchPlat ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS) (hDC : DCan D)
    (hPp : Pp ⊆ Pt) (hTb : Tb ⊆ Pt) (hTe : Gran Te bits ⊆ Pt) {s0 s : S}
    (hR : VrOK Ω Sg Scs Z OS Vc Ub (L.ksb s0) Pt) (hH : HrOK (L.ksb s0) Pp Tb Lv Hr) (hS : S2OK Te bits Hr)
    (hW : WuApart OS (L.ksb s0)) (hIO : IrqOK OS D (L.ksb s0)) (hap : IrqStApart OS (L.ksb s0))
    {a : A} {x : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hx : x ∈ OS) (hxI : ¬ IslN (L.ksb s0) x)
    (hD : DomQ st S2Q Vc D Scs Fp (L.idleW s) (L.mem s (scA (L.idleW s))) s)
    (hX : XQ st S2Q Vc D Scs Fp (L.idleW s) (L.mem s (scA (L.idleW s))) x s) (hN : IrqN st (L.ksb s0) s)
    (hY : VsTy st (L.ksb s0) Pp Tb Lv s) (h2 : S2Ty st hPl.ipa Pp Hr Te Re bits s) :
    cdt.delete st ar s a x true ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ∧
      VsTy st (L.ksb s0) Pp Tb Lv r.2.1 ∧ S2Ty st hPl.ipa Pp Hr Te Re bits r.2.1 ⦄ :=
  cdt.delete.zqIGT (Ty := fun s => VsTy st (L.ksb s0) Pp Tb Lv s ∧ S2Ty st hPl.ipa Pp Hr Te Re bits s) hP hO hA hV
    hDO hDC hR (finKT_s2 hP hPl hR hPp hTb hTe hH hS) (tyk_s2 hPp hTb hTe hH hS) hW hIO hap h hx hxI hD hX rfl rfl
    hN ⟨hY, h2⟩

/-- **The thread kind over a domain of `ZQ S2Q` caps keeps `JV` and `VsTy ∧ S2Ty`** (gen 40's
`cdt.delete.threadQE` with the typing at the end state). -/
theorem cdt.delete.threadQET (hP : P0.ArchTotal ar) (hPl : ArchPlat ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS) (hDC : DCan D)
    (hPp : Pp ⊆ Pt) (hTb : Tb ⊆ Pt) (hTe : Gran Te bits ⊆ Pt) {s0 s : S}
    (hR : VrOK Ω Sg Scs Z OS Vc Ub (L.ksb s0) Pt) (hH : HrOK (L.ksb s0) Pp Tb Lv Hr) (hS : S2OK Te bits Hr)
    (hW : WuApart OS (L.ksb s0)) (hIO : IrqOK OS D (L.ksb s0)) (hap : IrqStApart OS (L.ksb s0))
    {a : A} {x p : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hx : x ∈ OS) (hxI : ¬ IslN (L.ksb s0) x)
    (hD : DomQ st S2Q Vc D Scs Fp (L.idleW s) (L.mem s (scA (L.idleW s))) s) (hN : IrqN st (L.ksb s0) s)
    (hY : VsTy st (L.ksb s0) Pp Tb Lv s) (h2 : S2Ty st hPl.ipa Pp Hr Te Re bits s)
    (hc : obj.Slot.cap st x s = ok (.Thread p)) (hid : p ≠ L.idleW s) (hpF : p ∉ Fp)
    (hcov : ∀ i : U64, i.val < 7 → slotIdx p i ∈ D) :
    cdt.delete st ar s a x true ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ∧
      VsTy st (L.ksb s0) Pp Tb Lv r.2.1 ∧ S2Ty st hPl.ipa Pp Hr Te Re bits r.2.1 ⦄ :=
  cdt.delete.zqET hP hPl hO hA hV hDO hDC hPp hTb hTe hR hH hS hW hIO hap h hx hxI hD (fun c hc' => by
    rw [hc] at hc'; rw [← okinj hc']
    refine Or.inl ⟨Or.inl (Or.inr (Or.inl ⟨p, rfl, hid, hcov⟩)), ?_⟩
    rintro p' (⟨r, g, b, e⟩ | e | ⟨t', n', e⟩)
    · cases e
    · cases e; exact hpF
    · cases e) hN hY h2

end del

/-! ## The entry fact with the Stage-2 typing -/

/-- **[J] (a64) `SlotTyEntE n`**: [J] `SlotTyEntP`'s fields and, for the same ghost sets, `HighVSpace` roots `Hr`
and Stage-2 objects `Te` (depth `Re`, sizes `bits`) with `Gran Te bits ⊆ Pt`, `HrOK (ks e) Pp Tb Lv Hr`,
`S2OK Te bits Hr` and `S2Ty st n Pp Hr Te Re bits e` (module docstring for the source, file:line, and the
preservation still owed). At `P3Ok` states only, over ghost sets, not over a word class. -/
def SlotTyEntE (st : machine.Store S) [L : LawfulStore st] (T Cs Ω Sg : Set U64) (H : Heap) (Rp Scs Nt : Set U64)
    (Z : U64 → Nat) (n : U64) (P3Ok : S → Prop) : Prop :=
  ∀ e, P3Ok e → ∃ OS Vc Ub Pp Tb Pt Hr Te : Set U64, ∃ Lv Re bits : U64 → Nat,
    OSOK T Ω Sg OS ∧ SlotTy st T Ω Sg H Rp Nt OS e ∧ EntApart st e OS ∧
    (∀ t ∈ T, t ∈ OS) ∧ IrqStApart OS (L.ksb e) ∧ ScApart Scs Z OS ∧ VcOK T Scs Z OS Vc Ub ∧
    VcTy st T Cs Ω H Sg Scs Z Vc Ub e ∧ VcEntApart st T e Vc ∧ WuApart OS (L.ksb e) ∧
    Pp ⊆ Pt ∧ Tb ⊆ Pt ∧ VrOK Ω Sg Scs Z OS Vc Ub (L.ksb e) Pt ∧ VsTy st (L.ksb e) Pp Tb Lv e ∧
    VsEntApart st e (L.ksb e) Pt ∧
    Gran Te bits ⊆ Pt ∧ HrOK (L.ksb e) Pp Tb Lv Hr ∧ S2OK Te bits Hr ∧ S2Ty st n Pp Hr Te Re bits e

/-- `SlotTyEntE` implies `SlotTyEntP` (fields dropped). -/
theorem SlotTyEntE.toP {n : U64} (h : SlotTyEntE st T Cs Ω Sg H Rp Scs Nt Z n P3Ok) :
    SlotTyEntP st T Cs Ω Sg H Rp Scs Nt Z P3Ok := fun e he => by
  obtain ⟨OS, Vc, Ub, Pp, Tb, Pt, _, _, Lv, _, _, a, b, c, d, f, g, i, j, k, l, m, o, p, q, r, -⟩ := h e he
  exact ⟨OS, Vc, Ub, Pp, Tb, Pt, Lv, a, b, c, d, f, g, i, j, k, l, m, o, p, q, r⟩

/-- **`SlotTyEntE` at every `EntAt` state** (QueueZombieQDec's `SlotTyEntP.entAt` text, with `S2Ty` carried: the
entry prefix writes no `VsR` word, the `R + 4088` words among them; the `ks` base is kept). -/
theorem SlotTyEntE.entAt {n : U64} (hJ : SlotTyEntE st T Cs Ω Sg H Rp Scs Nt Z n P3Ok) {s : S}
    (hE : EntAt st P3Ok s) (hTP : TcbPlaced T) :
    ∃ OS Vc Ub Pp Tb Pt Hr Te : Set U64, ∃ Lv Re bits : U64 → Nat,
      OSOK T Ω Sg OS ∧ SlotTy st T Ω Sg H Rp Nt OS s ∧ (∀ t ∈ T, t ∈ OS) ∧ IrqStApart OS (L.ksb s) ∧
      ScApart Scs Z OS ∧ VcOK T Scs Z OS Vc Ub ∧ VcTy st T Cs Ω H Sg Scs Z Vc Ub s ∧ WuApart OS (L.ksb s) ∧
      Pp ⊆ Pt ∧ Tb ⊆ Pt ∧ VrOK Ω Sg Scs Z OS Vc Ub (L.ksb s) Pt ∧ VsTy st (L.ksb s) Pp Tb Lv s ∧
      Gran Te bits ⊆ Pt ∧ HrOK (L.ksb s) Pp Tb Lv Hr ∧ S2OK Te bits Hr ∧ S2Ty st n Pp Hr Te Re bits s := by
  obtain ⟨e, he, hw⟩ := hE
  obtain ⟨OS'', Vc', Ub', Pp, Tb, Pt, Hr, Te, Lv, Re, bits, hO', hT', hA', hc', hap', hsc', hV', hv', hVA', hwu,
    hPp, hTb, hR, hY, hVE, hTe, hH, hS, h2⟩ := hJ e he
  have hz : VsZ st (L.ksb e) Pt e s := VsZ.of_keep fun b hb => hw.mem_eq (hR.al b hb) fun hb' => hVE b hb' hb
  have hY' : VsTy st (L.ksb e) Pp Tb Lv s := hY.keepZ hPp hTb hz
  have hk : HrW st Hr e s := fun R hRm =>
    hw.mem_eq (hR.al _ (hr_vsr hTb hH hRm)) fun hb' => hVE _ hb' (hr_vsr hTb hH hRm)
  have h2' : S2Ty st n Pp Hr Te Re bits s := h2.keep hPp hTe hS hz hk
  refine ⟨OS'', Vc', Ub', Pp, Tb, Pt, Hr, Te, Lv, Re, bits, hO', fun y hy => ?_, hc', by rw [hw.1]; exact hap',
    hsc', hV', hv'.keep ?_, by rw [hw.1]; exact hwu, hPp, hTb, by rw [hw.1]; exact hR, by rw [hw.1]; exact hY', hTe,
    by rw [hw.1]; exact hH, hS, h2'⟩
  · obtain ⟨v8, v16, v24⟩ := vals hO' hy
    have k : ∀ b, Aligned b → y.val ≤ b.val → b.val < y.val + 32 → L.mem s b = L.mem e b :=
      fun b hb h1 h2 => hw.mem_eq hb fun hb' => hA' b hb' y hy ⟨h1, h2⟩
    exact (hT' y hy).of_eq (k _ (hO'.al0 hy) (by omega) (by omega))
      (k _ (hO'.al hy (by simp) (by simp)) (by omega) (by omega))
      (k _ (hO'.al hy (by simp) (by simp)) (by omega) (by omega))
      (k _ (hO'.al hy (by simp) (by simp)) (by omega) (by omega))
  · refine ⟨hw.1, fun b hb => hw.mem_eq (hv'.w hb).1 fun hb' => (hVA' b hb').1 hb,
      fun t ht => hw.mem_eq (field_aligned (hTP t ht) (by simp) (by simp)) fun hb' => (hVA' _ hb').2 t ht |>.1 rfl,
      fun t ht => hw.mem_eq (field_aligned (hTP t ht) (by simp) (by simp)) fun hb' => (hVA' _ hb').2 t ht |>.2 rfl,
      fun t ht => Or.inl ?_⟩
    have hy := hV'.bcov t ht
    obtain ⟨v8, -, -⟩ := vals hO' hy
    have k : ∀ b, Aligned b → (sbWordA t).val ≤ b.val → b.val < (sbWordA t).val + 32 → L.mem s b = L.mem e b :=
      fun b hb h1 h2 => hw.mem_eq hb fun hb' => hA' b hb' _ hy ⟨h1, h2⟩
    rw [DPF.slot_cap_dec, DPF.slot_cap_dec, k _ (hO'.al0 hy) (by omega) (by omega),
      k _ (hO'.al hy (k := 8#u64) (by simp) (by simp)) (by omega) (by omega)]

section deqE
variable {OS Vc Ub : Set U64} {Dm Fp : Set U64}

/-- **The `ZQ S2Q` decode on [J] `SlotTyEntE`**: gen 40's `del_zqE_ent` with `S2Ty`, `HrOK`, `S2OK` and the
Stage-2 placement taken from the entry fact (no case hypothesis on the VSpace typing); the deletion's domain facts
(`Dm`, `Fp`, `DomQ`, `XQ`, `IrqOK`, `IrqN`) remain case hypotheses of the decode start. -/
theorem syscall.decode_invocation.del_zqE_entE {A : Type _} {ar : machine.Arch A} (hP : P0.ArchTotal ar)
    (hPl : ArchPlat ar) (hJ : SlotTyEntE st T Cs Ω Sg H Rp Scs Nt Z hPl.ipa P3Ok) {s : S} (hE : EntAt st P3Ok s)
    {cap : capability.Cap} {extra : Aeneas.Std.Array obj.Slot 3#usize}
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) :
    ∃ OS Vc Ub, OSOK T Ω Sg OS ∧ SlotTy st T Ω Sg H Rp Nt OS s ∧ VcTy st T Cs Ω H Sg Scs Z Vc Ub s ∧
      ∀ (a : A) (len : U64) (slot : obj.Slot) (blk call don fp : Bool) (buf : U64) (Dm Fp : Set U64),
        Dm ⊆ OS → DCan Dm → IrqOK OS Dm (L.ksb s) → IrqN st (L.ksb s) s →
        DomQ st S2Q Vc Dm Scs Fp (L.idleW s) (L.mem s (scA (L.idleW s))) s →
        capFam cap = .cnode → slot ∈ OS → obj.Slot.cap st slot s = ok cap →
        TgtP st (fun x => XQ st S2Q Vc Dm Scs Fp (L.idleW s) (L.mem s (scA (L.idleW s))) x s ∧
          ¬ IslN (L.ksb s) x) s cap buf →
        syscall.decode_invocation st ar s a fl4_abi.label.CNodeDelete len slot cap blk call don fp buf extra
          ⦃ r s' _ => DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ∧ SlotTy st T Ω Sg H Rp Nt OS s' ∧
            VcTy st T Cs Ω H Sg Scs Z Vc Ub s' ⦄ := by
  have q := D.bxi.1.choose_spec.choose_spec
  obtain ⟨OS, Vc, Ub, Pp, Tb, Pt, Hr, Te, Lv, Re, bits, hO, hT, -, hap, hA, hV, hv, hW, hPp, hTb, hR, hY, hTe, hH,
    hS, h2⟩ := hJ.entAt hE q.tcbs
  exact ⟨OS, Vc, Ub, hO, hT, hv, fun a len slot blk call don fp buf Dm Fp hDO hDC hIO hN hD hf hs hc hk =>
    syscall.decode_invocation.del_zqE hP hPl hO hA hV hDO hDC hPp hTb hTe a len slot cap blk call don fp buf extra D
      hT hv hR hH hS hW hIO hap hN hY h2 hD hf hs hc hk⟩

end deqE

end ST
end R
end W7

end

end Fl4ProofsA64.P1
