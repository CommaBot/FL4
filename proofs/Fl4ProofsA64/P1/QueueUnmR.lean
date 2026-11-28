/-
P1 (aarch64, gen 45): **ARMPageTableUnmap over the narrowed typings** (QueueReach): after `unmap_page_table` the
unmapped table is **no longer reachable** (Stage-1 or Stage-2), so `UnmZ` over the reachable objects can hold
after the table is zeroed, while the table stays in `Te` / `Tb` (Architect ruling: placement sets are never shrunk).

* `S2Reach.vsz`, `VsReach.vsz`: along a `VsZ` step (every `VsR` word kept or zeroed) reachability only shrinks —
  a zero word is no pool root and no table descriptor.
* `S2Nm st Pp Re bits s t b` / `VsNm st Pp Hr Lv s t b`: the word `b` of a reachable Stage-2 (resp. Stage-1) table, at
  a depth where `desc` applies, holds a table descriptor naming `t`. `NoRoot st Pp Hr s t`: `t` is no `HighVSpace`
  root and no pool entry names it (as a tag-0 value, or as the untagged value of a tagged entry).
  `S2Reach.no` / `VsReach.no`: a table that is no root and that no reachable descriptor names is unreachable.
  `S2Nm.vsz`, `VsNm.vsz`: such a descriptor after a `VsZ` step was one before, with the same word.
* **[case fact] `PtFnd st n Pp Hr Lv Re bits s asid vaddr ptr`** (a definition, not a premise): `ptr` is no root,
  and every reachable Stage-2 (resp. Stage-1) descriptor naming `ptr` is the slot the `unmap_page_table` walk for
  `(asid, vaddr)` finds: the ASID's pool entry is tagged `ROOT_S2` and `ept::unmap_table`'s loop from `ept::find`'s
  root and `geom`'s start returns that slot (resp. the entry is not tagged `ROOT_S2` and `unmap_page_table`'s Stage-1
  loop, from the root or — for `ROOT_HIGH` — from the table entry 511 names, returns it).
  Source / justification (l4v `valid_vs_lookup` + `unique_table_refs` + `unique_table_caps`, ArchVSpace_AI): a
  table is mapped only by ARMPageTableMap (vspace.rs:1108–1135, ept.rs:174–197), which writes its one descriptor into
  the slot `lookup_slot` / `lookup_pt_slot` finds for the cap's `(asid, vaddr)` and records them in the (now mapped)
  cap; a mapped cap's `(asid, vaddr)` never change (copies keep them, `derive_cap` objects.rs:207–231); a table is
  mapped at most once while mapped (its unmapped cap is unique, `UnmU.one`); an intermediate table on that walk is
  removed from it only by an unmap of that table (which clears the one slot), so as long as the descriptor is
  reachable the walk from the same ASID meets the same tables and stops at the first descriptor naming `ptr`; an
  ASID's pool entry is rewritten only by `Assign` (an unmapped root cap: a fresh VSpace, whose tables are not yet
  reachable) and cleared by `delete_asid` (then nothing below it is reachable). A page table is never a pool root
  (`Assign` takes `Pml4` / `HighVSpace` / `Ept` caps, vspace.rs:1229–1261, of other objects).
  In the gen-43 counterexample (the VSpace deleted first) no reachable descriptor names the table, so the fact is
  vacuous there.
* `vspace.unmap_page_table.fnd2` / `.fnd1`: when the walk finds `b`, the state after is `wr s b 0`.
* **`vspace.unmap_page_table.unr`**: at a `VsTyR ∧ S2TyR` state with `PtFnd`, `unmap_page_table` writes `0` to at most
  one word of a reachable table (gen 40's `Wr0` at the reachable parts, `vspace.unmap_page_table.s2R`) and afterwards
  **no reachable descriptor names `ptr`**; with `NoRoot` after, `ptr` is unreachable (`S2Reach.no`, `VsReach.no`).

* **`UnmZ.unmap`** (the data step of the cap write): the slot that held `ptr`'s cap now holds an unmapped one, the
  other caps kept, no other `OS` slot named `ptr`, `ptr`'s words zero / in `Pt` / no words of a `Te'` object, `Te'`
  words `Te` words: `UnmZ` over `Te'` and `UnmU` after. `NoRoot.vsz`.
* **`unmapR.post`** (ARMPageTableUnmap's data steps: walk, `zero(ptr, 4096)`, cap write): from `VsTyR ∧ S2TyR`,
  `UnmZ` over the reachable Stage-2 objects, `UnmT` over the reachable Stage-1 tables, `UnmU`, `NoRoot` and the walk's
  "no reachable descriptor names `ptr`" — `ptr` unreachable at the end, `VsTyR ∧ S2TyR` over the **same** `Tb` / `Te`,
  `UnmZ` / `UnmT` over the reachable parts of the end state, `UnmU`. Case hypotheses: `hD2` / `hD1` (`ptr`'s words
  meet no other `Te` object / `Tb` table: the placement, as `S2Pl.un` / `S1Pl.un` with `ptr` added) and `hone` (no
  other `OS` slot names `ptr`: what `is_final_capability` gives under the MDB same-range adjacency, owed to
  `RngOneA64`).
* Decode-level instances over the narrowed typings: `vspace.decode_page_table.unmap_tyR`, `.map_s2R` (the table
  need only be unmapped with `UnmZ` over the reachable objects; after, `UnmZ` over the reachable objects of the new
  state), `.map_s1R` (`UnmT` over the reachable Stage-1 tables). So gen 44's `UnmT` is **restated over reachable
  tables** (not dropped): it still supplies "the new table is unreachable" and "the descriptor's slot is no unmapped
  object's word".

Not yet: the decode-level ARMPageTableUnmap lemma assembling `unr` and `unmapR.post` (needs `PtFnd` at the state
after `set_thread_state`, i.e. that the walk reads only `VsR` words — owed), and `hone` from `RngOneA64`.

No named premise; new definitions and theorems only.
-/
import Fl4ProofsA64.P1.QueueReach
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

/-! ## Reachability along `VsZ` steps; descriptors naming a table -/

/-- A reachable Stage-2 descriptor at `b` naming `t`. -/
def S2Nm (st : machine.Store S) [L : LawfulStore st] (Pp : Set U64) (Re bits : U64 → Nat) (s : S) (t b : U64) :
    Prop :=
  ∃ p o : U64, S2Reach st Pp Re bits s p ∧ 0 < Re p ∧ o.val < 2 ^ bits p ∧ o.val % 8 = 0 ∧ b = wa p o ∧
    (L.mem s b &&& 3#u64) = 3#u64 ∧ wa (L.mem s b &&& ept.ADDR_MASK) layout.PPTR_BASE = t

/-- A reachable Stage-1 descriptor at `b` naming `t`. -/
def VsNm (st : machine.Store S) [L : LawfulStore st] (Pp Hr : Set U64) (Lv : U64 → Nat) (s : S) (t b : U64) : Prop :=
  ∃ p o : U64, VsReach st Pp Hr Lv s p ∧ Lv p < 3 ∧ o.val < 4096 ∧ o.val % 8 = 0 ∧ b = wa p o ∧
    (L.mem s b &&& 3#u64) = 3#u64 ∧ wa (L.mem s b &&& vspace.ADDR_MASK) layout.PPTR_BASE = t

/-- `t` is no `HighVSpace` root and no pool entry names it. -/
def NoRoot (st : machine.Store S) [L : LawfulStore st] (Pp Hr : Set U64) (s : S) (t : U64) : Prop :=
  t ∉ Hr ∧ ∀ p ∈ Pp, ∀ o : U64, o.val < 4096 → o.val % 8 = 0 → L.mem s (wa p o) ≠ 0#u64 →
    ((L.mem s (wa p o) &&& 3#u64) = 0#u64 → L.mem s (wa p o) ≠ t) ∧
    ((L.mem s (wa p o) &&& 3#u64) ≠ 0#u64 → (L.mem s (wa p o) &&& ~~~3#u64) ≠ t)

section nm
variable {kb n : U64} {Pp Tb Pt Hr Te : Set U64} {Lv Re bits : U64 → Nat}

/-- **Stage-2 reachability only shrinks along a `VsZ` step.** -/
theorem S2Reach.vsz {s s' : S} (hPp : Pp ⊆ Pt) (hTe : Gran Te bits ⊆ Pt) (hS : S2OK Te bits Hr)
    (h : S2TyR st n Pp Hr Te Re bits s) (z : VsZ st kb Pt s s') {p : U64} (hr : S2Reach st Pp Re bits s' p) :
    S2Reach st Pp Re bits s p := by
  induction hr with
  | @root q o hq ho h8 h1 =>
    rcases z _ (Or.inl (ptw_mono hPp ⟨q, hq, o, ho, h8, rfl⟩)) with e | e
    · rw [e] at h1 ⊢; exact S2Reach.root hq ho h8 h1
    · rw [e] at h1; exact absurd h1 (by decide)
  | @step q o _ hpos ho h8 h3 ih =>
    have hq : q ∈ Te := (h.sub.reach ih).1
    rcases z _ (Or.inl (ptw_mono hTe (ptwb_gran hS.sz ⟨q, hq, o, ho, h8, rfl⟩))) with e | e
    · rw [e] at h3 ⊢; exact S2Reach.step ih hpos ho h8 h3
    · rw [e] at h3; exact absurd h3 (by decide)

/-- **Stage-1 reachability only shrinks along a `VsZ` step.** -/
theorem VsReach.vsz {s s' : S} (hPp : Pp ⊆ Pt) (hTb : Tb ⊆ Pt) (hH : Hr ⊆ Tb) (h : VsTyR st kb Pp Hr Tb Lv s)
    (z : VsZ st kb Pt s s') {p : U64} (hr : VsReach st Pp Hr Lv s' p) : VsReach st Pp Hr Lv s p := by
  induction hr with
  | hr hR => exact VsReach.hr hR
  | @root0 q o hq ho h8 hne h0 =>
    rcases z _ (Or.inl (ptw_mono hPp ⟨q, hq, o, ho, h8, rfl⟩)) with e | e
    · rw [e] at hne h0 ⊢; exact VsReach.root0 hq ho h8 hne h0
    · exact absurd e hne
  | @root2 q o hq ho h8 h2 =>
    rcases z _ (Or.inl (ptw_mono hPp ⟨q, hq, o, ho, h8, rfl⟩)) with e | e
    · rw [e] at h2 ⊢; exact VsReach.root2 hq ho h8 h2
    · rw [e] at h2; exact absurd h2 (by decide)
  | @step q o _ hl ho h8 h3 ih =>
    have hq : q ∈ Tb := (h.sub.reach (hr_rt hH) ih).1
    rcases z _ (Or.inl (ptw_mono hTb ⟨q, hq, o, ho, h8, rfl⟩)) with e | e
    · rw [e] at h3 ⊢; exact VsReach.step ih hl ho h8 h3
    · rw [e] at h3; exact absurd h3 (by decide)

/-- **A table that is no root and that no reachable descriptor names is not Stage-2 reachable.** -/
theorem S2Reach.no {s : S} {t : U64} (hR : NoRoot st Pp Hr s t) (hN : ¬ ∃ b, S2Nm st Pp Re bits s t b) :
    ¬ S2Reach st Pp Re bits s t := by
  intro hr
  cases hr with
  | @root q o hq ho h8 h1 =>
    have hne : L.mem s (wa q o) ≠ 0#u64 := fun e => by rw [e] at h1; exact absurd h1 (by decide)
    exact (hR.2 q hq o ho h8 hne).2 (by rw [h1]; decide) rfl
  | @step q o hq hpos ho h8 h3 => exact hN ⟨_, q, o, hq, hpos, ho, h8, rfl, h3, rfl⟩

/-- **A table that is no root and that no reachable descriptor names is not Stage-1 reachable.** -/
theorem VsReach.no {s : S} {t : U64} (hR : NoRoot st Pp Hr s t) (hN : ¬ ∃ b, VsNm st Pp Hr Lv s t b) :
    ¬ VsReach st Pp Hr Lv s t := by
  intro hr
  cases hr with
  | hr h => exact hR.1 h
  | @root0 q o hq ho h8 hne h0 => exact (hR.2 q hq o ho h8 hne).1 h0 rfl
  | @root2 q o hq ho h8 h2 =>
    have hne : L.mem s (wa q o) ≠ 0#u64 := fun e => by rw [e] at h2; exact absurd h2 (by decide)
    exact (hR.2 q hq o ho h8 hne).2 (by rw [h2]; decide) rfl
  | @step q o hq hl ho h8 h3 => exact hN ⟨_, q, o, hq, hl, ho, h8, rfl, h3, rfl⟩

/-- **A reachable Stage-2 descriptor after a `VsZ` step was one before**, with the same word. -/
theorem S2Nm.vsz {s s' : S} (hPp : Pp ⊆ Pt) (hTe : Gran Te bits ⊆ Pt) (hS : S2OK Te bits Hr)
    (h : S2TyR st n Pp Hr Te Re bits s) (z : VsZ st kb Pt s s') {t b : U64} (hb : S2Nm st Pp Re bits s' t b) :
    S2Nm st Pp Re bits s t b ∧ L.mem s' b = L.mem s b := by
  obtain ⟨p, o, hp, hpos, ho, h8, rfl, h3, ht⟩ := hb
  have hp0 := S2Reach.vsz hPp hTe hS h z hp
  have hq : p ∈ Te := (h.sub.reach hp0).1
  rcases z _ (Or.inl (ptw_mono hTe (ptwb_gran hS.sz ⟨p, hq, o, ho, h8, rfl⟩))) with e | e
  · rw [e] at h3 ht; exact ⟨⟨p, o, hp0, hpos, ho, h8, rfl, h3, ht⟩, e⟩
  · rw [e] at h3; exact absurd h3 (by decide)

/-- **A reachable Stage-1 descriptor after a `VsZ` step was one before**, with the same word. -/
theorem VsNm.vsz {s s' : S} (hPp : Pp ⊆ Pt) (hTb : Tb ⊆ Pt) (hH : Hr ⊆ Tb) (h : VsTyR st kb Pp Hr Tb Lv s)
    (z : VsZ st kb Pt s s') {t b : U64} (hb : VsNm st Pp Hr Lv s' t b) :
    VsNm st Pp Hr Lv s t b ∧ L.mem s' b = L.mem s b := by
  obtain ⟨p, o, hp, hl, ho, h8, rfl, h3, ht⟩ := hb
  have hp0 := VsReach.vsz hPp hTb hH h z hp
  have hq : p ∈ Tb := (h.sub.reach (hr_rt hH) hp0).1
  rcases z _ (Or.inl (ptw_mono hTb ⟨p, hq, o, ho, h8, rfl⟩)) with e | e
  · rw [e] at h3 ht; exact ⟨⟨p, o, hp0, hl, ho, h8, rfl, h3, ht⟩, e⟩
  · rw [e] at h3; exact absurd h3 (by decide)

theorem S2Nm.al {s : S} (hal : ∀ w, VsR kb Pt w → Aligned w) (hTe : Gran Te bits ⊆ Pt) (hS : S2OK Te bits Hr)
    (h : S2TyR st n Pp Hr Te Re bits s) {t b : U64} (hb : S2Nm st Pp Re bits s t b) : Aligned b := by
  obtain ⟨p, o, hp, -, ho, h8, rfl, -⟩ := hb
  exact hal _ (Or.inl (ptw_mono hTe (ptwb_gran hS.sz ⟨p, (h.sub.reach hp).1, o, ho, h8, rfl⟩)))

theorem VsNm.al {s : S} (hal : ∀ w, VsR kb Pt w → Aligned w) (hTb : Tb ⊆ Pt) (hH : Hr ⊆ Tb)
    (h : VsTyR st kb Pp Hr Tb Lv s) {t b : U64} (hb : VsNm st Pp Hr Lv s t b) : Aligned b := by
  obtain ⟨p, o, hp, -, ho, h8, rfl, -⟩ := hb
  exact hal _ (Or.inl (ptw_mono hTb ⟨p, (h.sub.reach (hr_rt hH) hp).1, o, ho, h8, rfl⟩))

/-- A `Wr0` step over a set of tables inside `Pt` is a `VsZ` step. -/
theorem Wr0.vsz {X : Set U64} {s s' : S} (hal : ∀ w, VsR kb Pt w → Aligned w) (hX : X ⊆ Pt) (h : Wr0 st X s s') :
    VsZ st kb Pt s s' := by
  rcases h with rfl | ⟨b, hb, rfl⟩
  · exact VsZ.refl _
  · exact VsZ.wr0 hal (hal _ (Or.inl (ptw_mono hX hb)))

end nm

/-! ## The case fact and the walk -/

/-- **[case fact] Every reachable descriptor naming `ptr` is the slot the `(asid, vaddr)` unmap walk finds**, and
`ptr` is no root (module docstring for the source). -/
structure PtFnd (st : machine.Store S) [L : LawfulStore st] (n : U64) (Pp Hr : Set U64) (Lv Re bits : U64 → Nat)
    (s : S) (asid vaddr ptr : U64) : Prop where
  root : NoRoot st Pp Hr s ptr
  s2 : ∀ b, S2Nm st Pp Re bits s ptr b → ∃ r1 root : U64, ∃ g : ept.S2Geom,
    vspace.find_asid_raw st s asid = ok (.Ok r1) ∧ (r1 &&& 3#u64) = 1#u64 ∧ ept.find st s asid = ok (.Ok root) ∧
    ept.geom n = ok g ∧
    ept.unmap_table_loop st s vaddr ptr root g.top_shift g.top_mask (core.num.U64.wrapping_sub g.levels 1#u64) =
      ok (some b)
  s1 : ∀ b, VsNm st Pp Hr Lv s ptr b → ∃ r1 t sh lv : U64,
    vspace.find_asid_raw st s asid = ok (.Ok r1) ∧ (r1 &&& 3#u64) ≠ 1#u64 ∧
    (((r1 &&& 3#u64) = 2#u64 ∧
        t = wa (L.mem s (wa (r1 &&& ~~~3#u64) 4088#u64) &&& vspace.ADDR_MASK) layout.PPTR_BASE ∧
        sh = 30#u64 ∧ lv = 1#u64) ∨
      ((r1 &&& 3#u64) ≠ 2#u64 ∧ t = (r1 &&& ~~~3#u64) ∧ sh = vspace.TOP_LEVEL_SHIFT ∧ lv = 0#u64)) ∧
    vspace.unmap_page_table_loop st s vaddr ptr t sh lv = ok (some b)

section walk
variable {A : Type _} {ar : machine.Arch A} {kb : U64} {Pp Tb Pt Hr Te : Set U64} {Lv Re bits : U64 → Nat}

set_option maxHeartbeats 2000000 in
/-- **The Stage-2 branch when the walk finds `b`**: the state after is `wr s b 0`. -/
theorem vspace.unmap_page_table.fnd2 (hA : P0.ArchTotal ar) (hPl : ArchPlat ar) {s : S} {asid vaddr ptr r1 root b : U64}
    {g : ept.S2Geom} (hraw : vspace.find_asid_raw st s asid = ok (.Ok r1)) (h1 : (r1 &&& 3#u64) = 1#u64)
    (hf : ept.find st s asid = ok (.Ok root)) (hg : ept.geom hPl.ipa = ok g)
    (hl : ept.unmap_table_loop st s vaddr ptr root g.top_shift g.top_mask (core.num.U64.wrapping_sub g.levels 1#u64) =
      ok (some b)) (a : A) :
    vspace.unmap_page_table st ar s a asid vaddr ptr ⦃ r => r.1 = L.wr s b 0#u64 ⦄ := by
  unfold vspace.unmap_page_table
  rw [hraw, bind_ok]
  try dsimp only
  simp only [lift, bind_ok, rtag, rs2, rhigh]
  split
  · unfold ept.unmap_table
    rw [hf, bind_ok]
    try dsimp only
    rw [hPl.ipa_eq a, bind_ok, hg, bind_ok]
    simp only [lift, bind_ok]
    rw [hl, bind_ok]
    try dsimp only
    rw [L.write_eq, bind_ok]
    refine WP.spec_bind (hA.invalidate_stage2_vmid a asid) fun a1 _ => ?_
    exact (WP.spec_ok _).2 rfl
  · rename_i hn; exact absurd h1 hn

set_option maxHeartbeats 2000000 in
/-- **The Stage-1 / `HighVSpace` branch when the walk finds `b`**: the state after is `wr s b 0`. -/
theorem vspace.unmap_page_table.fnd1 (hA : P0.ArchTotal ar) {s : S} {asid vaddr ptr r1 t sh lv b : U64}
    (hraw : vspace.find_asid_raw st s asid = ok (.Ok r1)) (h1 : (r1 &&& 3#u64) ≠ 1#u64)
    (hst : ((r1 &&& 3#u64) = 2#u64 ∧
        t = wa (L.mem s (wa (r1 &&& ~~~3#u64) 4088#u64) &&& vspace.ADDR_MASK) layout.PPTR_BASE ∧
        sh = 30#u64 ∧ lv = 1#u64) ∨
      ((r1 &&& 3#u64) ≠ 2#u64 ∧ t = (r1 &&& ~~~3#u64) ∧ sh = vspace.TOP_LEVEL_SHIFT ∧ lv = 0#u64))
    (hl : vspace.unmap_page_table_loop st s vaddr ptr t sh lv = ok (some b)) (a : A) :
    vspace.unmap_page_table st ar s a asid vaddr ptr ⦃ r => r.1 = L.wr s b 0#u64 ⦄ := by
  unfold vspace.unmap_page_table
  rw [hraw, bind_ok]
  try dsimp only
  simp only [lift, bind_ok, rtag, rs2, rhigh]
  split
  · rename_i h; exact absurd h h1
  refine WP.spec_bind (Pₘ := fun x : U64 × U64 × U64 => x = (t, sh, lv)) ?_ ?_
  · split
    · rename_i h2
      rcases hst with ⟨-, rfl, rfl, rfl⟩ | ⟨hn, -⟩
      · step as ⟨i1, hi1⟩
        have e1 : i1 = 4088#u64 := UScalar.eq_of_val_eq (by scalar_tac)
        subst e1
        simp only [lift, bind_ok, L.read_eq, vspace.table_of, layout.pptr]
        exact (WP.spec_ok _).2 rfl
      · exact absurd h2 hn
    · rename_i h2
      rcases hst with ⟨e2, -⟩ | ⟨-, rfl, rfl, rfl⟩
      · exact absurd e2 h2
      · exact (WP.spec_ok _).2 rfl
  · rintro ⟨t', sh', lv'⟩ e
    simp only [Prod.mk.injEq] at e
    obtain ⟨rfl, rfl, rfl⟩ := e
    refine WP.spec_bind (Pₘ := fun r => r = some b) (by rw [hl]; exact (WP.spec_ok _).2 rfl) ?_
    rintro _ rfl
    try dsimp only
    rw [L.write_eq, bind_ok]
    split
    · refine WP.spec_bind (hA.invalidate_high_vspace a _) fun a1 _ => ?_
      exact (WP.spec_ok _).2 rfl
    · refine WP.spec_bind (hA.invalidate_asid a asid) fun a1 _ => ?_
      exact (WP.spec_ok _).2 rfl

theorem rOk_inj {x y : U64} (h : (ok (.Ok x) : Result (core.result.Result U64 error.LookupFault)) = ok (.Ok y)) :
    x = y := by
  have := okinj h
  cases this
  rfl

set_option maxHeartbeats 4000000 in
/-- **After `unmap_page_table` no reachable descriptor names the unmapped table** (module docstring): at a
`VsTyR ∧ S2TyR` state with `PtFnd`, at most one word of a reachable table is written `0`, and afterwards no reachable
Stage-1 or Stage-2 descriptor names `ptr`. -/
theorem vspace.unmap_page_table.unr (hA : P0.ArchTotal ar) (hPl : ArchPlat ar) (hO : HrOK kb Pp Tb Lv Hr)
    (hS : S2OK Te bits Hr) (hal : ∀ w, VsR kb Pt w → Aligned w) (hPp : Pp ⊆ Pt) (hTb : Tb ⊆ Pt)
    (hTe : Gran Te bits ⊆ Pt) {s : S} (h0 : VsTyR st kb Pp Hr Tb Lv s) (h2 : S2TyR st hPl.ipa Pp Hr Te Re bits s)
    (hk : L.ksb s = kb) (a : A) {asid vaddr ptr : U64} (hF : PtFnd st hPl.ipa Pp Hr Lv Re bits s asid vaddr ptr) :
    vspace.unmap_page_table st ar s a asid vaddr ptr ⦃ r =>
      Wr0 st (TbO (VsRt st Pp Hr Tb Lv s) Hr ∪ Gran (S2Rt st Pp Te Re bits s) bits) s r.1 ∧
      (¬ ∃ b, S2Nm st Pp Re bits r.1 ptr b) ∧ ¬ ∃ b, VsNm st Pp Hr Lv r.1 ptr b ⦄ := by
  have hW := vspace.unmap_page_table.s2R hA hPl hO hS h0 h2 hk a asid vaddr ptr
  have hX : TbO (VsRt st Pp Hr Tb Lv s) Hr ∪ Gran (S2Rt st Pp Te Re bits s) bits ⊆ Pt :=
    Set.union_subset (fun _ h => hTb h.1.1) ((gran_mono S2Rt_sub).trans hTe)
  have hH := hO.sub
  by_cases hex : (∃ b, S2Nm st Pp Re bits s ptr b) ∨ (∃ b, VsNm st Pp Hr Lv s ptr b)
  · -- the walk finds the descriptor `b0`; the state after is `wr s b0 0`
    have key : ∃ b0, Aligned b0 ∧ (vspace.unmap_page_table st ar s a asid vaddr ptr ⦃ r => r.1 = L.wr s b0 0#u64 ⦄) ∧
        ∀ b, (S2Nm st Pp Re bits s ptr b ∨ VsNm st Pp Hr Lv s ptr b) → b = b0 := by
      rcases hex with ⟨b0, hb0⟩ | ⟨b0, hb0⟩
      · obtain ⟨r1, root, g, hraw, h1, hf, hg, hl⟩ := hF.s2 b0 hb0
        refine ⟨b0, S2Nm.al hal hTe hS h2 hb0, vspace.unmap_page_table.fnd2 hA hPl hraw h1 hf hg hl a, fun b hb => ?_⟩
        rcases hb with hb | hb
        · obtain ⟨r1', root', g', hraw', -, hf', hg', hl'⟩ := hF.s2 b hb
          rw [hraw] at hraw'; rw [hf] at hf'; rw [hg] at hg'
          obtain rfl := rOk_inj hf'
          obtain rfl := okinj hg'
          rw [hl] at hl'
          exact (Option.some.inj (okinj hl')).symm
        · obtain ⟨r1', t, sh, lv, hraw', h1', -⟩ := hF.s1 b hb
          rw [hraw] at hraw'; obtain rfl := rOk_inj hraw'
          exact absurd h1 h1'
      · obtain ⟨r1, t, sh, lv, hraw, h1, hst, hl⟩ := hF.s1 b0 hb0
        refine ⟨b0, VsNm.al hal hTb hH h0 hb0, vspace.unmap_page_table.fnd1 hA hraw h1 hst hl a, fun b hb => ?_⟩
        rcases hb with hb | hb
        · obtain ⟨r1', root', g', hraw', h1', -⟩ := hF.s2 b hb
          rw [hraw] at hraw'; obtain rfl := rOk_inj hraw'
          exact absurd h1' h1
        · obtain ⟨r1', t', sh', lv', hraw', -, hst', hl'⟩ := hF.s1 b hb
          rw [hraw] at hraw'; obtain rfl := rOk_inj hraw'
          have e : t' = t ∧ sh' = sh ∧ lv' = lv := by
            rcases hst with ⟨e2, rfl, rfl, rfl⟩ | ⟨n2, rfl, rfl, rfl⟩ <;>
              rcases hst' with ⟨e2', rfl, rfl, rfl⟩ | ⟨n2', rfl, rfl, rfl⟩
            · exact ⟨rfl, rfl, rfl⟩
            · exact absurd e2 n2'
            · exact absurd e2' n2
            · exact ⟨rfl, rfl, rfl⟩
          obtain ⟨rfl, rfl, rfl⟩ := e
          rw [hl] at hl'
          exact (Option.some.inj (okinj hl')).symm
    obtain ⟨b0, hal0, hE, huniq⟩ := key
    obtain ⟨v, hv, hv1⟩ := spec_exists_u hE
    rw [hv, WP.spec_ok] at hW ⊢
    have z : VsZ st kb Pt s v.1 := Wr0.vsz hal hX hW
    have hb0 : ∀ b, (L.mem v.1 b &&& 3#u64) = 3#u64 → b ≠ b0 := by
      rintro b h3 rfl
      rw [hv1, L.mem_wr_same hal0] at h3; exact absurd h3 (by decide)
    refine ⟨hW, fun ⟨b, hb⟩ => ?_, fun ⟨b, hb⟩ => ?_⟩
    · obtain ⟨hb', -⟩ := S2Nm.vsz hPp hTe hS h2 z hb
      obtain ⟨-, -, -, -, -, -, -, h3, -⟩ := hb
      exact hb0 b h3 (huniq b (Or.inl hb'))
    · obtain ⟨hb', -⟩ := VsNm.vsz hPp hTb hH h0 z hb
      obtain ⟨-, -, -, -, -, -, -, h3, -⟩ := hb
      exact hb0 b h3 (huniq b (Or.inr hb'))
  · refine WP.spec_mono hW fun r hw => ⟨hw, fun ⟨b, hb⟩ => ?_, fun ⟨b, hb⟩ => ?_⟩
    · exact hex (Or.inl ⟨b, (S2Nm.vsz hPp hTe hS h2 (Wr0.vsz hal hX hw) hb).1⟩)
    · exact hex (Or.inr ⟨b, (VsNm.vsz hPp hTb hH h0 (Wr0.vsz hal hX hw) hb).1⟩)

end walk


/-! ## `UnmZ` / `UnmU` after the table becomes unmapped -/

section unmz
variable {OS : Set U64} {kb n : U64} {Pp Tb Pt Hr Te : Set U64} {Lv Re bits : U64 → Nat}

/-- **`UnmZ` and `UnmU` after ARMPageTableUnmap's cap write** (the data step): the slot `x0`, which held a
`PageTable` cap of `ptr`, now holds an unmapped one; the other `OS` caps are kept; no other `OS` slot named `ptr`
(what `is_final_capability` establishes, owed to the MDB adjacency fact); `ptr`'s words are zero, in `Pt` and no
words of a `Te'` object; `Te'`'s words are `Te` words (e.g. `Te'` the reachable objects after, `Te` before); every
`VsR` word outside a write set `W` kept, `W` missing the other unmapped objects' words. -/
theorem UnmZ.unmap {W : U64 → Prop} {Te' : Set U64} {s s' : S} {x0 ptr : U64} (hx0 : x0 ∈ OS)
    (hU : UnmZ st OS Pt Te bits s) (hV : UnmU st OS Pp s)
    (hc : ∀ x ∈ OS, x ≠ x0 → obj.Slot.cap st x s' = obj.Slot.cap st x s)
    (hc0 : ∃ a v, obj.Slot.cap st x0 s' = ok (.PageTable ptr false a v))
    (hv0 : ∃ m a v, obj.Slot.cap st x0 s = ok (.PageTable ptr m a v))
    (hone : ∀ y ∈ OS, y ≠ x0 → ¬ NmC st y ptr s)
    (hptr : ptr ∈ Pt) (hz : ∀ o : U64, o.val < 4096 → o.val % 8 = 0 → L.mem s' (wa ptr o) = 0#u64)
    (hnT : ∀ o : U64, o.val < 4096 → o.val % 8 = 0 → ¬ PtWb Te' bits (wa ptr o))
    (hm : ∀ b, VsR kb Pt b → ¬ W b → L.mem s' b = L.mem s b)
    (hW : ∀ x ∈ OS, ∀ p n, UnmC st x p n s → p ≠ ptr → ∀ o : U64, o.val < n → o.val % 8 = 0 → ¬ W (wa p o))
    (hT : ∀ b, PtWb Te' bits b → PtWb Te bits b) :
    UnmZ st OS Pt Te' bits s' ∧ UnmU st OS Pp s' := by
  obtain ⟨a0, v0, e0⟩ := hc0
  obtain ⟨m0, a1, v1, e1⟩ := hv0
  have hn0 : NmC st x0 ptr s := Or.inl ⟨m0, a1, v1, e1⟩
  have hne : ∀ x ∈ OS, x ≠ x0 → ∀ p n, UnmC st x p n s → p ≠ ptr := by
    rintro x hx hxn p n hu rfl
    exact hxn (hV.one x hx x0 hx0 p n hu hn0).symm
  have hVs : ∀ x ∈ OS, ∀ p n, VsC st x p n s' → VsC st x p n s := by
    intro x hx p n h
    by_cases hxn : x = x0
    · subst hxn
      rcases h with ⟨hn, m, a, v, e⟩ | ⟨hn, m, a, v, e⟩
      · rw [e0] at e; cases okinj e
        exact Or.inl ⟨hn, m0, a1, v1, e1⟩
      · rw [e0] at e; cases okinj e
    · exact (VsC.congr (hc x hx hxn)).1 h
  refine ⟨⟨fun x hx p asid v hcx => ?_, fun x hx p asid v hcx => ?_⟩,
    ⟨fun x hx y hy p n hu hn => ?_,
     fun x hx y hy p q n m hp hq hpq => hV.dis x hx y hy p q n m (hVs x hx p n hp) (hVs y hy q m hq) hpq,
     fun x hx p n hp => hV.pool x hx p n (hVs x hx p n hp)⟩⟩
  · by_cases hxn : x = x0
    · subst hxn; rw [e0] at hcx; cases okinj hcx
      exact ⟨hptr, fun o ho h8 => ⟨hnT o ho h8, hz o ho h8⟩⟩
    · rw [hc x hx hxn] at hcx
      obtain ⟨hp, hf⟩ := hU.pt x hx p asid v hcx
      have hu : UnmC st x p 4096 s := Or.inl ⟨rfl, asid, v, hcx⟩
      refine ⟨hp, fun o ho h8 => ⟨fun hw => (hf o ho h8).1 (hT _ hw), ?_⟩⟩
      rw [hm _ (UnmZ.words (kb := kb) hU hx hu ho h8).1 (hW x hx p 4096 hu (hne x hx hxn p 4096 hu) o ho h8)]
      exact (hf o ho h8).2
  · by_cases hxn : x = x0
    · subst hxn; rw [e0] at hcx; cases okinj hcx
    · rw [hc x hx hxn] at hcx
      obtain ⟨hp, hf⟩ := hU.ept x hx p asid v hcx
      have hu : UnmC st x p 8192 s := Or.inr ⟨rfl, asid, v, hcx⟩
      refine ⟨hp, fun o ho h8 => ⟨fun hw => (hf o ho h8).1 (hT _ hw), ?_⟩⟩
      rw [hm _ (UnmZ.words (kb := kb) hU hx hu ho h8).1 (hW x hx p 8192 hu (hne x hx hxn p 8192 hu) o ho h8)]
      exact (hf o ho h8).2
  · by_cases hxn : x = x0
    · subst hxn
      have hp : p = ptr := by
        rcases hu with ⟨-, a, v, e⟩ | ⟨-, a, v, e⟩ <;> rw [e0] at e <;> (cases okinj e) <;> rfl
      subst hp
      by_contra hyx
      exact hone y hy hyx ((NmC.congr (hc y hy hyx)).1 hn)
    · have hu0 : UnmC st x p n s := (UnmC.congr (hc x hx hxn)).1 hu
      by_cases hyn : y = x0
      · subst hyn
        have hp : p = ptr := by
          rcases hn with ⟨m, a, v, e⟩ | ⟨l, m, a, v, e⟩ <;> rw [e0] at e <;> (cases okinj e) <;> rfl
        exact absurd hp (hne x hx hxn p n hu0)
      · exact hV.one x hx y hy p n hu0 ((NmC.congr (hc y hy hyn)).1 hn)


/-- `NoRoot` along a `VsZ` step (a zeroed pool entry names nothing). -/
theorem NoRoot.vsz {s s' : S} {t : U64} (hPp : Pp ⊆ Pt) (h : NoRoot st Pp Hr s t) (z : VsZ st kb Pt s s') :
    NoRoot st Pp Hr s' t :=
  ⟨h.1, fun p hp o ho h8 hne => by
    rcases z _ (Or.inl (ptw_mono hPp ⟨p, hp, o, ho, h8, rfl⟩)) with e | e
    · rw [e] at hne ⊢; exact h.2 p hp o ho h8 hne
    · exact absurd e hne⟩

set_option maxHeartbeats 4000000 in
/-- **ARMPageTableUnmap's data steps over the narrowed typings** (the walk `s → s3`, the `zero` and the cap write
`s3 → s5`): if after the walk no reachable descriptor names `ptr` (`vspace.unmap_page_table.unr`) and `ptr` is no root,
then at the end `ptr` is unreachable, `VsTyR ∧ S2TyR` hold over the same `Tb` / `Te`, and `UnmZ` / `UnmT` hold over
the **reachable** objects / tables, with `UnmU` — the gen-43 counterexample shape (a deleted VSpace: nothing
reachable names `ptr`) included. Case hypotheses: `ptr`'s words meet no other `Te` object / `Tb` table (`hD2`,
`hD1`, the placement), no other `OS` slot names `ptr` (`hone`, what `is_final_capability` gives under the MDB
adjacency fact, owed). -/
theorem unmapR.post (hPp : Pp ⊆ Pt) (hTb : Tb ⊆ Pt) (hTe : Gran Te bits ⊆ Pt) (hS : S2OK Te bits Hr)
    (hH : Hr ⊆ Tb) {s s3 s5 : S} {x0 ptr : U64} (hx0 : x0 ∈ OS)
    (h0 : VsTyR st kb Pp Hr Tb Lv s) (h2 : S2TyR st n Pp Hr Te Re bits s)
    (hU : UnmZ st OS Pt (S2Rt st Pp Te Re bits s) bits s) (hT : UnmT st OS (VsRt st Pp Hr Tb Lv s) s)
    (hV : UnmU st OS Pp s) (hR : NoRoot st Pp Hr s ptr)
    (z3 : VsZ st kb Pt s s3) (hk3 : HrW st Hr s s3) (hn2 : ¬ ∃ b, S2Nm st Pp Re bits s3 ptr b)
    (hn1 : ¬ ∃ b, VsNm st Pp Hr Lv s3 ptr b) (z5 : VsZ st kb Pt s3 s5) (hk5 : HrW st Hr s s5)
    (hc : ∀ x ∈ OS, x ≠ x0 → obj.Slot.cap st x s5 = obj.Slot.cap st x s)
    (hc0 : ∃ a v, obj.Slot.cap st x0 s5 = ok (.PageTable ptr false a v))
    (hv0 : ∃ m a v, obj.Slot.cap st x0 s = ok (.PageTable ptr m a v))
    (hone : ∀ y ∈ OS, y ≠ x0 → ¬ NmC st y ptr s)
    (hptr : ptr ∈ Pt) (hz : ∀ o : U64, o.val < 4096 → o.val % 8 = 0 → L.mem s5 (wa ptr o) = 0#u64)
    (hm : ∀ b, VsR kb Pt b → ¬ (PtW (TbO (VsRt st Pp Hr Tb Lv s) Hr ∪ Gran (S2Rt st Pp Te Re bits s) bits) b ∨
      ∃ o : U64, o.val < 4096 ∧ o.val % 8 = 0 ∧ b = wa ptr o) → L.mem s5 b = L.mem s b)
    (hD2 : ∀ q ∈ Te, q ≠ ptr → ∀ o o' : U64, o.val < 4096 → o.val % 8 = 0 → o'.val < 2 ^ bits q →
      o'.val % 8 = 0 → wa q o' ≠ wa ptr o)
    (hD1 : ∀ q ∈ Tb, q ≠ ptr → ∀ o o' : U64, o.val < 4096 → o.val % 8 = 0 → o'.val < 4096 → o'.val % 8 = 0 →
      wa q o' ≠ wa ptr o) :
    VsTyR st kb Pp Hr Tb Lv s5 ∧ S2TyR st n Pp Hr Te Re bits s5 ∧
      UnmZ st OS Pt (S2Rt st Pp Te Re bits s5) bits s5 ∧ UnmT st OS (VsRt st Pp Hr Tb Lv s5) s5 ∧
      UnmU st OS Pp s5 := by
  have z : VsZ st kb Pt s s5 := z3.trans z5
  have h03 : VsTyR st kb Pp Hr Tb Lv s3 := VsTyR.keepZ hPp hTb hH h0 z3
  have h23 : S2TyR st n Pp Hr Te Re bits s3 := S2TyR.keep hPp hTe hS h2 z3 hk3
  have h05 : VsTyR st kb Pp Hr Tb Lv s5 := VsTyR.keepZ hPp hTb hH h0 z
  have h25 : S2TyR st n Pp Hr Te Re bits s5 := S2TyR.keep hPp hTe hS h2 z hk5
  have hR5 : NoRoot st Pp Hr s5 ptr := NoRoot.vsz hPp hR z
  have hn2' : ¬ ∃ b, S2Nm st Pp Re bits s5 ptr b := fun ⟨b, hb⟩ => hn2 ⟨b, (S2Nm.vsz hPp hTe hS h23 z5 hb).1⟩
  have hn1' : ¬ ∃ b, VsNm st Pp Hr Lv s5 ptr b := fun ⟨b, hb⟩ => hn1 ⟨b, (VsNm.vsz hPp hTb hH h03 z5 hb).1⟩
  have hu2 : ¬ S2Reach st Pp Re bits s5 ptr := S2Reach.no hR5 hn2'
  have hu1 : ¬ VsReach st Pp Hr Lv s5 ptr := VsReach.no hR5 hn1'
  have hsub2 : S2Rt st Pp Te Re bits s5 ⊆ S2Rt st Pp Te Re bits s :=
    fun q hq => ⟨hq.1, S2Reach.vsz hPp hTe hS h2 z hq.2⟩
  have hsub1 : VsRt st Pp Hr Tb Lv s5 ⊆ VsRt st Pp Hr Tb Lv s :=
    fun q hq => ⟨hq.1, VsReach.vsz hPp hTb hH h0 z hq.2⟩
  obtain ⟨m0, a1, v1, e1⟩ := hv0
  have hvc0 : VsC st x0 ptr 4096 s := Or.inl ⟨rfl, m0, a1, v1, e1⟩
  have hW : ∀ x ∈ OS, ∀ p n, UnmC st x p n s → p ≠ ptr → ∀ o : U64, o.val < n → o.val % 8 = 0 →
      ¬ (PtW (TbO (VsRt st Pp Hr Tb Lv s) Hr ∪ Gran (S2Rt st Pp Te Re bits s) bits) (wa p o) ∨
        ∃ o' : U64, o'.val < 4096 ∧ o'.val % 8 = 0 ∧ wa p o = wa ptr o') := by
    rintro x hx p n hu hp o ho h8 (hw | ⟨o', ho', h8', e⟩)
    · rcases ptw_union hw with hw | hw
      · exact hT x hx p n hu o ho h8 (ptw_mono tbo_sub hw)
      · exact (UnmZ.words (kb := kb) hU hx hu ho h8).2.1 (gran_ptwb (Pt := S2Rt st Pp Te Re bits s) (fun q (hq : q ∈ S2Rt st Pp Te Re bits s) => hS.sz q hq.1) hw)
    · exact hV.dis x hx x0 hx0 p ptr n 4096 (UnmC.vs hu) hvc0 hp o o' ho h8 ho' h8' e
  have hnT : ∀ o : U64, o.val < 4096 → o.val % 8 = 0 → ¬ PtWb (S2Rt st Pp Te Re bits s5) bits (wa ptr o) := by
    rintro o ho h8 ⟨q, hq, o', ho', h8', e⟩
    have hne : q ≠ ptr := fun h => by subst h; exact hu2 hq.2
    exact hD2 q hq.1 hne o o' ho h8 ho' h8' e.symm
  obtain ⟨hUZ, hUU⟩ := UnmZ.unmap (kb := kb) (Te' := S2Rt st Pp Te Re bits s5) hx0 hU hV hc hc0
    ⟨m0, a1, v1, e1⟩ hone hptr hz hnT hm hW (fun b hb => ptwb_mono hsub2 hb)
  have hUT : UnmT st OS (VsRt st Pp Hr Tb Lv s5) s5 := by
    intro x hx p n hu o ho h8 hw
    obtain ⟨q, hq, o', ho', h8', e⟩ := hw
    by_cases hxn : x = x0
    · subst hxn
      obtain ⟨a0, v0, e0⟩ := hc0
      have hp : p = ptr ∧ n = 4096 := by
        rcases hu with ⟨hn, a, v, e'⟩ | ⟨hn, a, v, e'⟩ <;> rw [e0] at e' <;> (cases okinj e')
        exact ⟨rfl, hn⟩
      obtain ⟨rfl, rfl⟩ := hp
      have hne : q ≠ p := fun h => by subst h; exact hu1 hq.2
      exact hD1 q hq.1 hne o o' ho h8 ho' h8' e.symm
    · have hu0 : UnmC st x p n s := (UnmC.congr (hc x hx hxn)).1 hu
      exact hT x hx p n hu0 o ho h8 ⟨q, hsub1 hq, o', ho', h8', e⟩
  exact ⟨h05, h25, hUZ, hUT, hUU⟩

end unmz


/-! ## The decode-level table steps over the narrowed typings (instances) -/

section decR
variable {OS Vc Ub : Set U64} {kb n : U64} {Pp Tb Pt Hr Te : Set U64} {Lv Re bits : U64 → Nat}
variable {A : Type _} {ar : machine.Arch A}

/-- **ARMPageTableUnmap keeps the narrowed typings** (gen 43's `unmap_ty` at the reachable parts). -/
theorem vspace.decode_page_table.unmap_tyR (hA : P0.ArchTotal ar) (hPl : ArchPlat ar)
    (hR : VrOK Ω Sg Scs Z OS Vc Ub kb Pt) (hO : OSOK T Ω Sg OS)
    {X : Set U64} {Q : U64 → U64 → List U64} {Rq : U64 → List U64} {s : S}
    (q : SchedQueuesInvX st T Cs Ω H X s Q Rq) (hk : L.ksb s = kb) (hPp : Pp ⊆ Pt) (hTb : Tb ⊆ Pt)
    (hTe : Gran Te bits ⊆ Pt) (hH : HrOK kb Pp Tb Lv Hr) (hS : S2OK Te bits Hr)
    (hY : VsTyR st kb Pp Hr Tb Lv s) (h2 : S2TyR st hPl.ipa Pp Hr Te Re bits s)
    (a : A) (len slot buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize) (ptr : U64) (mapped : Bool)
    (masid mvaddr : U64) (hsl : slot ∈ OS) (hal : Aligned ptr) (hfit : ptr.val + 4096 ≤ 2 ^ 64)
    (hh : ∀ R ∈ Hr, ∀ o : U64, o.val < 4096 → o.val % 8 = 0 → wa ptr o ≠ wa R 4088#u64) :
    vspace.decode_page_table st ar s a fl4_abi.label.ARMPageTableUnmap len slot
      (.PageTable ptr mapped masid mvaddr) buf extra ⦃ r => r.2.1 = s ∨
        (L.ksb r.2.1 = kb ∧ VsTyR st kb Pp Hr Tb Lv r.2.1 ∧ S2TyR st hPl.ipa Pp Hr Te Re bits r.2.1) ⦄ :=
  WP.spec_mono (vspace.decode_page_table.unmap_ty hA hPl hR hO q hk hPp (VsRt_sub.trans hTb)
    ((gran_mono S2Rt_sub).trans hTe) (hH.mono VsRt_sub (hr_rt hH.sub)) (S2OK.sub hS S2Rt_sub) hY.sub h2.sub a len
    slot buf extra ptr mapped masid mvaddr hsl hal hfit hh) fun _ hr => hr.imp id fun ⟨hk', y, z⟩ =>
      ⟨hk', y.toRsub VsRt_sub (hr_rt hH.sub), z.toRsub S2Rt_sub⟩

/-- **ARMPageTableMap into a Stage-2 VSpace over the narrowed typings** (gen 43's `map_s2` at the reachable parts):
the table need only be unmapped with `UnmZ` over the **reachable** objects (it may be an old, unreachable member of
`Te`); after, `UnmZ` over the reachable objects of the new state. -/
theorem vspace.decode_page_table.map_s2R (hPl : ArchPlat ar) (hR : VrOK Ω Sg Scs Z OS Vc Ub kb Pt)
    (hO : OSOK T Ω Sg OS) {X : Set U64} {Q : U64 → U64 → List U64} {Rq : U64 → List U64} {s : S}
    (q : SchedQueuesInvX st T Cs Ω H X s Q Rq) (hk : L.ksb s = kb) (hPp : Pp ⊆ Pt) (hTb : Tb ⊆ Pt)
    (hTe : Gran Te bits ⊆ Pt) (hH : HrOK kb Pp Tb Lv Hr) {ptr asid0 v0 : U64} (h12 : bits ptr = 12)
    (hS : S2OK (insert ptr Te) bits Hr) (hD : S2Pl kb Pp Tb (insert ptr Te) bits)
    (hU : UnmZ st OS Pt (S2Rt st Pp Te Re bits s) bits s) (hV : UnmU st OS Pp s)
    (hY : VsTyR st kb Pp Hr Tb Lv s) (h2 : S2TyR st hPl.ipa Pp Hr Te Re bits s)
    (a : A) (len slot buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize) (hsl : slot ∈ OS)
    (hc : obj.Slot.cap st slot s = ok (.PageTable ptr false asid0 v0))
    (hx : ∀ x ∈ extra.val, x ≠ 0#u64 → ∃ p l m asid v, obj.Slot.cap st x s = ok (.Ept p l m asid v)) :
    vspace.decode_page_table st ar s a fl4_abi.label.ARMPageTableMap len slot (.PageTable ptr false asid0 v0) buf
      extra ⦃ r => r.2.1 = s ∨ (L.ksb r.2.1 = kb ∧ VsTyR st kb Pp Hr Tb Lv r.2.1 ∧
        (∃ Re' : U64 → Nat, (∀ p ∈ S2Rt st Pp Te Re bits s, Re' p = Re p) ∧
          S2TyR st hPl.ipa Pp Hr (insert ptr Te) Re' bits r.2.1 ∧
          UnmZ st OS Pt (S2Rt st Pp (insert ptr Te) Re' bits r.2.1) bits r.2.1) ∧ UnmU st OS Pp r.2.1) ⦄ := by
  have hsub : insert ptr (S2Rt st Pp Te Re bits s) ⊆ insert ptr Te := Set.insert_subset_insert S2Rt_sub
  refine WP.spec_mono (vspace.decode_page_table.map_s2 hPl hR hO q hk hPp (VsRt_sub.trans hTb)
    ((gran_mono S2Rt_sub).trans hTe) (hH.mono VsRt_sub (hr_rt hH.sub)) h12 (S2OK.sub hS hsub)
    (S2Pl.mono hD hsub VsRt_sub) hU hV hY.sub h2.sub a len slot buf extra hsl hc hx) ?_
  rintro r (e | ⟨hk', hY', ⟨Re', hRe, h2'⟩, hU', hV'⟩)
  · exact Or.inl e
  · exact Or.inr ⟨hk', hY'.toRsub VsRt_sub (hr_rt hH.sub),
      ⟨Re', hRe, h2'.toRsub hsub, UnmZ.anti hU' fun p hp => h2'.reach hp.2⟩, hV'⟩

/-- **ARMPageTableMap into a Stage-1 / `HighVSpace` VSpace over the narrowed typings** (gen 44's `map_s1` at the
reachable parts): `UnmT` is needed only over the **reachable** Stage-1 tables (the new table need only be
unreachable). -/
theorem vspace.decode_page_table.map_s1R (hR : VrOK Ω Sg Scs Z OS Vc Ub kb Pt) (hO : OSOK T Ω Sg OS)
    {X : Set U64} {Q : U64 → U64 → List U64} {Rq : U64 → List U64} {s : S}
    (q : SchedQueuesInvX st T Cs Ω H X s Q Rq) (hk : L.ksb s = kb) (hPp : Pp ⊆ Pt) (hTb : Tb ⊆ Pt)
    (hTe : Gran Te bits ⊆ Pt) (hH : HrOK kb Pp Tb Lv Hr) (hS : S2OK Te bits Hr) (hD : S2Pl kb Pp Tb Te bits)
    {ptr a0 v0 : U64} (hP1 : S1Pl kb Pp (insert ptr Tb)) (hY : VsTyR st kb Pp Hr Tb Lv s)
    (h2 : S2TyR st n Pp Hr Te Re bits s) (hU : UnmZ st OS Pt (S2Rt st Pp Te Re bits s) bits s)
    (hV : UnmU st OS Pp s) (hUT : UnmT st OS (VsRt st Pp Hr Tb Lv s) s) (a : A) (len slot buf : U64)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (hsl : slot ∈ OS)
    (hc : obj.Slot.cap st slot s = ok (.PageTable ptr false a0 v0))
    (hx : ∀ x ∈ extra.val, x ≠ 0#u64 → (∃ p m asid, obj.Slot.cap st x s = ok (.Pml4 p m asid)) ∨
      (∃ p m asid, obj.Slot.cap st x s = ok (.HighVSpace p m asid))) :
    vspace.decode_page_table st ar s a fl4_abi.label.ARMPageTableMap len slot (.PageTable ptr false a0 v0) buf
      extra ⦃ r => r.2.1 = s ∨ (L.ksb r.2.1 = kb ∧
        ∃ Lv' : U64 → Nat, (∀ p ∈ VsRt st Pp Hr Tb Lv s, Lv' p = Lv p) ∧
          VsTyR st kb Pp Hr (insert ptr Tb) Lv' r.2.1 ∧ S2TyR st n Pp Hr Te Re bits r.2.1 ∧
          UnmZ st OS Pt (S2Rt st Pp Te Re bits r.2.1) bits r.2.1 ∧ UnmU st OS Pp r.2.1) ⦄ := by
  have hsub : insert ptr (VsRt st Pp Hr Tb Lv s) ⊆ insert ptr Tb := Set.insert_subset_insert VsRt_sub
  have hHs : Hr ⊆ insert ptr (VsRt st Pp Hr Tb Lv s) := (hr_rt hH.sub).trans (Set.subset_insert _ _)
  refine WP.spec_mono (vspace.decode_page_table.map_s1 hR hO q hk hPp (VsRt_sub.trans hTb)
    ((gran_mono S2Rt_sub).trans hTe) (hH.mono VsRt_sub (hr_rt hH.sub)) (S2OK.sub hS S2Rt_sub)
    (S2Pl.mono hD S2Rt_sub VsRt_sub) (S1Pl.mono hP1 hsub) hY.sub h2.sub hU hV hUT a len slot buf extra hsl hc hx) ?_
  rintro r (e | ⟨hk', Lv', hL, hY', h2', hU', hV'⟩)
  · exact Or.inl e
  · exact Or.inr ⟨hk', Lv', hL, hY'.toRsub hsub hHs, h2'.toRsub S2Rt_sub,
      UnmZ.anti hU' fun p hp => h2'.reach hp.2, hV'⟩

end decR

end ST
end R
end W7

end

end Fl4ProofsA64.P1
