/-
P1 (aarch64, gen 39): **page-table caps in covered slots alongside mapped `HighVSpace` roots** — an instance of the
generic Zombie loop (QueueZombieQ's `FinKT` / `TyK` forms) whose typing keeps a `HighVSpace` root's entry 511.

Gen 38 put page-table caps into the loop only at states whose pools hold Stage-1 roots (`VsS1`): QueuePtTy's `high`
clause ("a tag-2 root's entry 511 is a table descriptor") is not kept by an abstract `VsZ` step. Here the loop runs
over the gen-39 class (`FinKT`: a finalisation keeps the typing itself; `TyK`: the other steps keep every `VsR` word,
QueueVsKeep), and every VSpace finaliser is shown never to write entry 511 of a `HighVSpace` root.

Source (crates/fl4-core/src/arch/aarch64/vspace.rs):
* `init_high_vspace` (276–297): a `HighVSpace` at `base` is 8 KiB; its level-0 entry 511 (`HIGH_L0_INDEX`) is a
  table descriptor (`D_VALID | D_TABLE_OR_PAGE`, `e & 3 = 3`) of its own level-1 table at `base + 4096`.
* `unmap_page_table` (470–517): a `ROOT_HIGH` walk starts at `table_of(root[511])` at level 1 (488–492: "level-0
  entry 511 is never a page table's to take"); a `ROOT_S1` walk at the root (level 0). The found slot is a slot of
  the table the walk is at: never a `HighVSpace` root's word (its level is 0, the high walk's tables have level ≥ 1,
  an S1 root is no `HighVSpace` object).
* `unmap_page` (449–468): writes `lu.slot` only if `lu.shift = page_shift(size)` ∈ {12, 21, 30}: a slot of a table of
  level ≥ 1 (`lookup_pt_slot`, 120–130: shift 39 at level 0), never a root's word.
* `delete_asid` (529–549) writes a pool entry, `delete_asid_pool` an ASID-table word: neither is a table's word.

* **`HrOK kb Pp Tb Lv Hr`** (state-free placement of the ghost set `Hr` of `HighVSpace` roots): `Hr ⊆ Tb`, level 0,
  a word of a table of `Tb` equal to `R + 4088` (`R ∈ Hr`) is a word of `R` itself (4 KiB-aligned tables), no pool
  word and no ASID-table word is `R + 4088`.
* **`HrTy Pp Hr s`**: a nonzero entry of a pool of `Pp` has tag 0 with a root outside `Hr`, or tag 2 with its root
  in `Hr` (no Stage-2 / tag-3 entry); every `R ∈ Hr` has `R[511] & 3 = 3`. `HrTy.ptTy` (with `VsTy`: QueuePtTy's
  `PtTy`), `HrTy.keep` (along a `VsZ` step keeping the `R + 4088` words), `HrTy.of_s1` (gen 38's `VsS1` is `Hr = ∅`).
* Walks: `vspace.lookup_pt_slot_loop.lv` / `lookup_pt_slot.lv` (the slot's table level: `shift + 9·Lv = 39`),
  `vspace.page_shift.v`, **`vspace.unmap_page.hr`**, `vspace.unmap_page_table_loop.hr` (invariant `UpH`: `UpI` and
  the table outside `Hr`), **`vspace.unmap_page_table.hr`**: `Wr0` steps of words of tables outside `Hr` (`TbO`).
* Finalisers: `fin_frame.hr`, `fin_dframe.hr`, `fin_pt.hr`, `fin_pd.hr`, `fin_pdpt.hr`, `fin_pool.hr`; roots by
  QueueVsTy's `fin_root.z` / `fin_hvs.z` over `Pp`.
* Instance: **`finKT_hr`** (`FinKT` of QueuePtTy's class `PtQ` over `VsTy ∧ HrTy`), **`tyk_hr`**; tops
  **`cdt.delete.zqH`**, **`cdt.delete.threadQH`**; decode **`syscall.decode_invocation.del_zqG`** (the generic decode
  over `FinKT` / `TyK`) and **`del_zqH_ent`** (on gen 38's [J] `SlotTyEntP`, no new premise).

Case hypotheses (state-free, or facts of the deletion's / decode's start state): `HrOK (ks) Pp Tb Lv Hr`
(state-free: `HighVSpace` objects are 8 KiB retyped objects, objects.rs `create_new_objects`, disjoint from pools and
other tables; the ASID table is kernel-global, layout.rs), `HrTy st Pp Hr s` at the start state (pool entries are
written only by `assign` with tag 0 / 1 / 2, vspace.rs:1239–1241, so it restricts to states without an assigned
Stage-2 VSpace, as gen 38's `PtTy.tag`; entry 511 as above). No named premise; new definitions and theorems only.
-/
import Fl4ProofsA64.P1.QueueVsK
import Fl4ProofsA64.P1.QueueZombieQDec
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64} {P3Ok : S → Prop} {U : Set U64}

local notation "wa" => core.num.U64.wrapping_add

/-! ## The ghost `HighVSpace` roots -/

/-- **The placement of the `HighVSpace` roots `Hr`** (state-free; module docstring). -/
structure HrOK (kb : U64) (Pp Tb : Set U64) (Lv : U64 → Nat) (Hr : Set U64) : Prop where
  sub : Hr ⊆ Tb
  lv : ∀ R ∈ Hr, Lv R = 0
  tb : ∀ t ∈ Tb, ∀ o : U64, o.val < 4096 → o.val % 8 = 0 → ∀ R ∈ Hr, wa t o = wa R 4088#u64 → t = R
  pp : ∀ p ∈ Pp, ∀ o : U64, o.val < 4096 → o.val % 8 = 0 → ∀ R ∈ Hr, wa p o ≠ wa R 4088#u64
  asw : ∀ R ∈ Hr, ¬ AsW kb (wa R 4088#u64)

/-- **Pool tags and `HighVSpace` entries at `s`** (module docstring). -/
structure HrTy (st : machine.Store S) [L : LawfulStore st] (Pp Hr : Set U64) (s : S) : Prop where
  tag : ∀ p ∈ Pp, ∀ o : U64, o.val < 4096 → o.val % 8 = 0 → L.mem s (wa p o) ≠ 0#u64 →
    ((L.mem s (wa p o) &&& 3#u64) = 0#u64 ∧ L.mem s (wa p o) ∉ Hr) ∨
    ((L.mem s (wa p o) &&& 3#u64) = 2#u64 ∧ (L.mem s (wa p o) &&& ~~~3#u64) ∈ Hr)
  hi : ∀ R ∈ Hr, (L.mem s (wa R 4088#u64) &&& 3#u64) = 3#u64

/-- The `R + 4088` words of `Hr` kept. -/
def HrW (st : machine.Store S) [L : LawfulStore st] (Hr : Set U64) (s s' : S) : Prop :=
  ∀ R ∈ Hr, L.mem s' (wa R 4088#u64) = L.mem s (wa R 4088#u64)

/-- The tables of `Tb` outside `Hr`. -/
def TbO (Tb Hr : Set U64) : Set U64 := {t | t ∈ Tb ∧ t ∉ Hr}

theorem tbo_sub {Tb Hr : Set U64} : TbO Tb Hr ⊆ Tb := fun _ h => h.1

/-- `HrTy` with `VsTy` is QueuePtTy's `PtTy`. -/
theorem HrTy.ptTy {kb : U64} {Pp Tb Hr : Set U64} {Lv : U64 → Nat} {s : S} (hO : HrOK kb Pp Tb Lv Hr)
    (h : VsTy st kb Pp Tb Lv s) (hh : HrTy st Pp Hr s) : PtTy st kb Pp Tb Lv s :=
  ⟨h, fun p hp o ho h8 hne => (hh.tag p hp o ho h8 hne).imp And.left And.left,
    fun p hp o ho h8 hne h2 => by
      rcases hh.tag p hp o ho h8 hne with ⟨e, -⟩ | ⟨-, hR⟩
      · rw [e] at h2; exact absurd h2 (by decide)
      · exact hh.hi _ hR⟩

/-- `HrTy` along a `VsZ` step keeping the `R + 4088` words. -/
theorem HrTy.keep {kb : U64} {Pp Pt Hr : Set U64} {s s' : S} (hPp : Pp ⊆ Pt) (h : HrTy st Pp Hr s)
    (z : VsZ st kb Pt s s') (k : HrW st Hr s s') : HrTy st Pp Hr s' := by
  refine ⟨fun p hp o ho h8 hne => ?_, fun R hR => by rw [k R hR]; exact h.hi R hR⟩
  rcases z _ (Or.inl (ptw_mono hPp ⟨p, hp, o, ho, h8, rfl⟩)) with e | e
  · rw [e] at hne ⊢; exact h.tag p hp o ho h8 hne
  · exact absurd e hne

/-- Gen 38's Stage-1-only pools are `HrTy` with no `HighVSpace` root. -/
theorem HrTy.of_s1 {Pp : Set U64} {s : S} (h : VsS1 st Pp s) : HrTy st Pp ∅ s :=
  ⟨fun p hp o ho h8 hne => Or.inl ⟨h p hp o ho h8 hne, by simp⟩, fun _ h => by simp at h⟩

theorem HrOK.empty {kb : U64} {Pp Tb : Set U64} {Lv : U64 → Nat} : HrOK kb Pp Tb Lv ∅ :=
  ⟨fun _ h => by simp at h, fun _ h => by simp at h, fun _ _ _ _ _ _ h => by simp at h,
    fun _ _ _ _ _ _ h => by simp at h, fun _ h => by simp at h⟩

/-- A word of a table outside `Hr` is no `R + 4088` word. -/
theorem HrOK.tbo {kb : U64} {Pp Tb : Set U64} {Lv : U64 → Nat} {Hr : Set U64} (hO : HrOK kb Pp Tb Lv Hr) {b : U64}
    (hb : PtW (TbO Tb Hr) b) : ∀ R ∈ Hr, b ≠ wa R 4088#u64 := by
  obtain ⟨t, ⟨ht, htH⟩, o, ho, h8, rfl⟩ := hb
  intro R hR e
  exact htH (hO.tb t ht o ho h8 R hR e ▸ hR)

/-- A word of a pool is no `R + 4088` word. -/
theorem HrOK.ppw {kb : U64} {Pp Tb : Set U64} {Lv : U64 → Nat} {Hr : Set U64} (hO : HrOK kb Pp Tb Lv Hr) {b : U64}
    (hb : PtW Pp b) : ∀ R ∈ Hr, b ≠ wa R 4088#u64 := by
  obtain ⟨p, hp, o, ho, h8, rfl⟩ := hb
  exact hO.pp p hp o ho h8

/-- A `Wr0` step on words that are no `R + 4088` word keeps those words. -/
theorem Wr0.hrw {X Hr : Set U64} {s s' : S} (hal : ∀ b, PtW X b → Aligned b)
    (hRal : ∀ R ∈ Hr, Aligned (wa R 4088#u64)) (hne : ∀ b, PtW X b → ∀ R ∈ Hr, b ≠ wa R 4088#u64)
    (h : Wr0 st X s s') : HrW st Hr s s' := by
  rcases h with rfl | ⟨b, hb, rfl⟩
  · exact fun _ _ => rfl
  · exact fun R hR => L.mem_wr_ne (hal b hb) (hRal R hR) fun e => hne b hb R hR (UScalar.eq_of_val_eq e)

/-! ## The walks -/

set_option maxHeartbeats 2000000 in
/-- **The page-table walk with the found table's level**: `shift + 9·Lv = 39`. -/
theorem vspace.lookup_pt_slot_loop.lv {kb : U64} {Pp Tb : Set U64} {Lv : U64 → Nat} {s : S}
    (h : VsTy st kb Pp Tb Lv s) (vaddr shift slot level : U64) (hi : LkI Tb Lv (shift, slot, level)) :
    vspace.lookup_pt_slot_loop st s vaddr shift slot level ⦃ r => ∃ p ∈ Tb, ∃ o : U64, o.val < 4096 ∧
      o.val % 8 = 0 ∧ r.2 = wa p o ∧ r.1.val + 9 * Lv p = 39 ⦄ := by
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
      · exact (WP.spec_ok _).2 ⟨p, hp, o, ho, h8, rfl, by first | omega | (simp only; omega) | (dsimp only; omega)⟩
    · exact (WP.spec_ok _).2 ⟨p, hp, o, ho, h8, rfl, by first | omega | (simp only; omega) | (dsimp only; omega)⟩
  · exact hi

/-- **`lookup_pt_slot` from a level-0 root of `Tb`**: the slot's table and level. -/
theorem vspace.lookup_pt_slot.lv {kb : U64} {Pp Tb : Set U64} {Lv : U64 → Nat} {s : S}
    (h : VsTy st kb Pp Tb Lv s) {root : U64} (hr : root ∈ Tb) (h0 : Lv root = 0) (vaddr : U64) :
    vspace.lookup_pt_slot st s root vaddr ⦃ lu => ∃ p ∈ Tb, ∃ o : U64, o.val < 4096 ∧
      o.val % 8 = 0 ∧ lu.slot = wa p o ∧ lu.shift.val + 9 * Lv p = 39 ⦄ := by
  unfold vspace.lookup_pt_slot
  refine WP.spec_bind (vspace.entry_addr.off root vaddr vspace.TOP_LEVEL_SHIFT) fun sl ⟨o, ho, h8, e⟩ => ?_
  have hi : LkI Tb Lv (vspace.TOP_LEVEL_SHIFT, sl, 3#u64) := by
    unfold LkI; exact ⟨by simp, by simp, root, hr, by simp [h0], o, ho, h8, e⟩
  refine WP.spec_bind (vspace.lookup_pt_slot_loop.lv h vaddr _ sl 3#u64 hi) ?_
  rintro ⟨sh, sl1⟩ hs
  exact (WP.spec_ok _).2 hs

theorem vspace.page_shift.v (size : capability.FrameSize) :
    vspace.page_shift size ⦃ sh => sh.val = 12 ∨ sh.val = 21 ∨ sh.val = 30 ⦄ := by
  unfold vspace.page_shift capability.FrameSize.bits
  cases size <;> exact (WP.spec_ok _).2 (by simp)

set_option maxHeartbeats 2000000 in
/-- **`unmap_page` at a `VsTy` state** (`ks` base `kb`): unchanged, or a word of a table outside `Hr` written `0`. -/
theorem vspace.unmap_page.hr {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {kb : U64}
    {Pp Tb Hr : Set U64} {Lv : U64 → Nat} (hO : HrOK kb Pp Tb Lv Hr) {s : S} (h : VsTy st kb Pp Tb Lv s)
    (hk : L.ksb s = kb) (a : A) (size : capability.FrameSize) (asid vaddr pptr : U64) :
    vspace.unmap_page st ar s a size asid vaddr pptr ⦃ r => Wr0 st (TbO Tb Hr) s r.1 ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold vspace.unmap_page
  refine WP.spec_bind (vspace.unmap_root.ty h hk asid) fun o ho => ?_
  rcases o with _ | ⟨root, high⟩
  · exact (WP.spec_ok _).2 (Wr0.refl _)
  try dsimp only
  obtain ⟨hrT, h0⟩ := ho root high rfl
  refine WP.spec_bind (vspace.lookup_pt_slot.lv h hrT h0 vaddr) fun lu ⟨p, hp, o, ho', h8, el, hlv⟩ => ?_
  refine WP.spec_bind (vspace.page_shift.v size) fun sh hsh => ?_
  split
  · exact (WP.spec_ok _).2 (Wr0.refl _)
  rename_i hne
  have esh : lu.shift = sh := UScalar.eq_of_val_eq (by simpa using hne)
  have hpH : p ∉ Hr := fun hpR => by
    have := hO.lv p hpR
    rw [esh] at hlv
    omega
  step with LawfulStore.read_spec as ⟨e, _⟩
  refine WP.spec_bind (P0.vspace.is_page.p0 e lu.shift) fun b _ => ?_
  split
  · refine WP.spec_bind (P0.vspace.page_base.p0 e lu.shift) fun pb _ => ?_
    refine WP.spec_bind (P0.layout.paddr.p0 pptr) fun pa _ => ?_
    split
    · exact (WP.spec_ok _).2 (Wr0.refl _)
    step with LawfulStore.write_spec as ⟨s1, e1⟩
    have hw : PtW (TbO Tb Hr) lu.slot := ⟨p, ⟨hp, hpH⟩, o, ho', h8, el⟩
    split
    · refine WP.spec_bind (hA.invalidate_high_page a vaddr) fun a1 _ => ?_
      rw [WP.spec_ok, e1]; exact Or.inr ⟨_, hw, rfl⟩
    · refine WP.spec_bind (hA.invalidate_page a asid vaddr) fun a1 _ => ?_
      rw [WP.spec_ok, e1]; exact Or.inr ⟨_, hw, rfl⟩
  · exact (WP.spec_ok _).2 (Wr0.refl _)

/-- The loop invariant of `unmap_page_table_loop` with the table outside `Hr`. -/
abbrev UpH (Tb Hr : Set U64) (Lv : U64 → Nat) (x : U64 × U64 × U64) : Prop :=
  x.2.2.val ≤ 3 ∧ (x.2.2.val < 3 → x.1 ∈ Tb ∧ Lv x.1 = x.2.2.val ∧ x.1 ∉ Hr)

set_option maxHeartbeats 2000000 in
/-- **The `unmap_page_table` walk stays in tables outside `Hr`.** -/
theorem vspace.unmap_page_table_loop.hr {kb : U64} {Pp Tb Hr : Set U64} {Lv : U64 → Nat} {s : S}
    (hO : HrOK kb Pp Tb Lv Hr) (h : VsTy st kb Pp Tb Lv s) (vaddr pt table shift level : U64)
    (hi : UpH Tb Hr Lv (table, shift, level)) :
    vspace.unmap_page_table_loop st s vaddr pt table shift level ⦃ r => ∀ sl, r = some sl →
      PtW (TbO Tb Hr) sl ⦄ := by
  unfold vspace.unmap_page_table_loop
  apply loop.spec_decr_nat (measure := fun x => 3 - x.2.2.val) (inv := UpH Tb Hr Lv)
  · rintro ⟨t, sh, lv⟩ ⟨hl3, hT⟩
    simp only at hl3 hT
    dsimp only
    unfold vspace.unmap_page_table_loop.body
    split
    · rename_i hlt
      have hlt' : lv.val < 3 := by first | simpa using hlt | scalar_tac
      obtain ⟨ht, hlv, htH⟩ := hT hlt'
      refine WP.spec_bind (vspace.entry_addr.off t vaddr sh) fun sl hsl => ?_
      obtain ⟨o, ho, h8, e⟩ := hsl
      subst e
      rw [L.read_eq, bind_ok]
      refine WP.spec_bind (vspace.is_table.tag _ sh) fun b hb => ?_
      split
      · rename_i hbt
        obtain ⟨hT', hL'⟩ := h.desc t ht (by omega) o ho h8 (hb hbt)
        simp only [lift, bind_ok, vspace.table_of, layout.pptr]
        split
        · exact (WP.spec_ok _).2 fun sl e' => by cases e'; exact ⟨t, ⟨ht, htH⟩, o, ho, h8, rfl⟩
        · try simp only [lift, bind_ok]
          step as ⟨lv1, hlv1⟩
          try simp only [lift, bind_ok]
          try rw [WP.spec_ok]
          try dsimp only
          have hne : ∀ y ∈ Hr, Lv y ≠ Lv t + 1 := fun y hy => by rw [hO.lv y hy]; omega
          refine ⟨?_, fun _ => ⟨hT', ?_, fun hR => hne _ hR hL'⟩, ?_⟩
          · omega
          · rw [hL', hlv]; omega
          · omega
      · exact (WP.spec_ok _).2 fun sl e' => by cases e'
    · exact (WP.spec_ok _).2 fun sl e' => by cases e'
  · exact hi

set_option maxHeartbeats 4000000 in
/-- **`unmap_page_table` at a `VsTy ∧ HrTy` state**: unchanged, or a word of a table outside `Hr` written `0`. -/
theorem vspace.unmap_page_table.hr {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {kb : U64}
    {Pp Tb Hr : Set U64} {Lv : U64 → Nat} (hO : HrOK kb Pp Tb Lv Hr) {s : S} (h0 : VsTy st kb Pp Tb Lv s)
    (hh : HrTy st Pp Hr s) (hk : L.ksb s = kb) (a : A) (asid vaddr pt : U64) :
    vspace.unmap_page_table st ar s a asid vaddr pt ⦃ r => Wr0 st (TbO Tb Hr) s r.1 ⦄ := by
  have h : PtTy st kb Pp Tb Lv s := hh.ptTy hO h0
  unfold vspace.unmap_page_table
  refine WP.spec_bind (vspace.find_asid_raw.ty h.ty hk asid) fun r hr => ?_
  rcases r with r1 | e
  · obtain ⟨p, hp, o, ho, h8, er, hr0⟩ := hr r1 rfl
    have hpl := h.ty.pool p hp o ho h8 (by rw [← er]; exact hr0)
    have htg := h.tag p hp o ho h8 (by rw [← er]; exact hr0)
    have hhi := h.high p hp o ho h8 (by rw [← er]; exact hr0)
    have hth := hh.tag p hp o ho h8 (by rw [← er]; exact hr0)
    rw [← er] at hpl htg hhi hth
    simp only [lift, bind_ok, rtag, rs2, rhigh]
    split
    · rename_i h1
      exfalso
      rcases htg with e | e <;> rw [e] at h1 <;> exact absurd h1 (by decide)
    · refine WP.spec_bind (Pₘ := fun x : U64 × U64 × U64 => UpH Tb Hr Lv x) ?_ ?_
      · split
        · rename_i h2
          obtain ⟨hrT, hr0'⟩ := hpl.2 h2
          have he := hhi h2
          step as ⟨i1, hi1⟩
          have e1 : i1 = 4088#u64 := UScalar.eq_of_val_eq (by scalar_tac)
          subst e1
          simp only [lift, bind_ok, L.read_eq, vspace.table_of, layout.pptr]
          obtain ⟨hT1, hL1⟩ := h.ty.desc _ hrT (by omega) 4088#u64 (by simp) (by simp) he
          rw [WP.spec_ok]
          have hne : ∀ y ∈ Hr, Lv y ≠ 1 := fun y hy => by rw [hO.lv y hy]; omega
          refine ⟨by simp, fun _ => ⟨hT1, ?_, fun hR => hne _ hR (hL1.trans (by rw [hr0']))⟩⟩
          simp only; rw [hL1, hr0']; simp
        · rename_i h2
          have h0' : (r1 &&& 3#u64) = 0#u64 := htg.resolve_right h2
          have hnH : r1 ∉ Hr := by
            rcases hth with ⟨-, hn⟩ | ⟨e2, -⟩
            · exact hn
            · exact absurd e2 h2
          rw [WP.spec_ok]
          refine ⟨by simp, fun _ => ?_⟩
          simp only
          rw [and_not_of r1 3#u64 h0']
          obtain ⟨hT0, hL0⟩ := hpl.1 h0'
          exact ⟨hT0, by rw [hL0]; simp, hnH⟩
      · rintro ⟨t, sh, lv⟩ hi
        try dsimp only
        refine WP.spec_bind (vspace.unmap_page_table_loop.hr hO h.ty vaddr pt t sh lv hi) fun found hf => ?_
        rcases found with _ | sl
        · exact (WP.spec_ok _).2 (Wr0.refl _)
        · try dsimp only
          step with LawfulStore.write_spec as ⟨s1, e1⟩
          split
          · refine WP.spec_bind (hA.invalidate_high_vspace a _) fun a1 _ => ?_
            rw [WP.spec_ok, e1]; exact Or.inr ⟨_, hf sl rfl, rfl⟩
          · refine WP.spec_bind (hA.invalidate_asid a asid) fun a1 _ => ?_
            rw [WP.spec_ok, e1]; exact Or.inr ⟨_, hf sl rfl, rfl⟩
  · exact (WP.spec_ok _).2 (Wr0.refl _)

/-! ## The finalisers -/

section fin
variable {A : Type _} {ar : machine.Arch A} {kb : U64} {Pp Tb Hr : Set U64} {Lv : U64 → Nat}

/-- **A non-EPT, non-device frame's finalisation** (QueueVsTy's `fin_frame.z` text over `unmap_page.hr`). -/
theorem fin_frame.hr (hA : P0.ArchTotal ar) (hO : HrOK kb Pp Tb Lv Hr) (s : S) (a : A)
    (ptr : U64) (size : capability.FrameSize) (rights : U64) (mapped : Bool) (asid vaddr : U64) (fin : Bool)
    (h : VsTy st kb Pp Tb Lv s) (hk : L.ksb s = kb) :
    objects.finalise_cap_object st ar s a (.Frame ptr size rights false mapped false asid vaddr) fin ⦃ r =>
      r.1 = (.Null, .Null) ∧ Wr0 st (TbO Tb Hr) s r.2.1 ⦄ := by
  unfold objects.finalise_cap_object
  dsimp only
  refine WP.spec_bind (Pₘ := fun r : S × A => Wr0 st (TbO Tb Hr) s r.1) ?_ ?_
  · split
    · split
      · simp only [Bool.false_eq_true, ↓reduceIte]
        exact vspace.unmap_page.hr hA hO h hk a size asid vaddr ptr
      · exact (WP.spec_ok _).2 (Wr0.refl _)
    · exact (WP.spec_ok _).2 (Wr0.refl _)
  rintro ⟨s1, a1⟩ w1
  try dsimp only
  cases fin <;> (try simp only [Bool.false_eq_true, ↓reduceIte]) <;> exact (WP.spec_ok _).2 ⟨rfl, w1⟩

/-- **A non-EPT device frame's finalisation** (QueuePtTy's `fin_dframe.z` text over `unmap_page.hr`). -/
theorem fin_dframe.hr (hA : P0.ArchTotal ar) (hO : HrOK kb Pp Tb Lv Hr) (s : S) (a : A)
    (ptr : U64) (size : capability.FrameSize) (rights : U64) (mapped : Bool) (asid vaddr : U64) (fin : Bool)
    (h : VsTy st kb Pp Tb Lv s) (hk : L.ksb s = kb) :
    objects.finalise_cap_object st ar s a (.Frame ptr size rights true mapped false asid vaddr) fin ⦃ r =>
      r.1 = (.Null, .Null) ∧ Wr0 st (TbO Tb Hr) s r.2.1 ⦄ := by
  unfold objects.finalise_cap_object
  dsimp only
  refine WP.spec_bind (Pₘ := fun r : S × A => Wr0 st (TbO Tb Hr) s r.1) ?_ ?_
  · split
    · split
      · simp only [Bool.false_eq_true, ↓reduceIte]
        exact vspace.unmap_page.hr hA hO h hk a size asid vaddr ptr
      · exact (WP.spec_ok _).2 (Wr0.refl _)
    · exact (WP.spec_ok _).2 (Wr0.refl _)
  rintro ⟨s1, a1⟩ w1
  try dsimp only
  cases fin
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact (WP.spec_ok _).2 ⟨rfl, w1⟩
  · simp only [↓reduceIte]
    exact WP.spec_bind (P0.objects.retire_dma_frame.p0 st ar s1 a1 ptr size L.total hA) fun a2 _ =>
      (WP.spec_ok _).2 ⟨rfl, w1⟩

/-- **A page-table cap's finalisation** (QueuePtTy's `fin_pt.z` text over `unmap_page_table.hr`). -/
theorem fin_pt.hr (hA : P0.ArchTotal ar) (hO : HrOK kb Pp Tb Lv Hr) (s : S) (a : A)
    (ptr : U64) (mapped : Bool) (asid vaddr : U64) (fin : Bool) (h : VsTy st kb Pp Tb Lv s)
    (hh : HrTy st Pp Hr s) (hk : L.ksb s = kb) :
    objects.finalise_cap_object st ar s a (.PageTable ptr mapped asid vaddr) fin ⦃ r =>
      r.1 = (.Null, .Null) ∧ Wr0 st (TbO Tb Hr) s r.2.1 ⦄ := by
  unfold objects.finalise_cap_object
  dsimp only
  split
  · split
    · refine WP.spec_bind (vspace.unmap_page_table.hr hA hO h hh hk a asid vaddr ptr) ?_
      rintro ⟨s1, a1⟩ w1
      exact (WP.spec_ok _).2 ⟨rfl, w1⟩
    · exact (WP.spec_ok _).2 ⟨rfl, Wr0.refl _⟩
  · exact (WP.spec_ok _).2 ⟨rfl, Wr0.refl _⟩

/-- **A `PageDirectory` cap's finalisation** (as `fin_pt.hr`). -/
theorem fin_pd.hr (hA : P0.ArchTotal ar) (hO : HrOK kb Pp Tb Lv Hr) (s : S) (a : A)
    (ptr : U64) (mapped : Bool) (asid vaddr : U64) (fin : Bool) (h : VsTy st kb Pp Tb Lv s)
    (hh : HrTy st Pp Hr s) (hk : L.ksb s = kb) :
    objects.finalise_cap_object st ar s a (.PageDirectory ptr mapped asid vaddr) fin ⦃ r =>
      r.1 = (.Null, .Null) ∧ Wr0 st (TbO Tb Hr) s r.2.1 ⦄ := by
  unfold objects.finalise_cap_object
  dsimp only
  split
  · split
    · refine WP.spec_bind (Pₘ := fun r : S × A => Wr0 st (TbO Tb Hr) s r.1) ?_ ?_
      · unfold vspace.unmap_page_directory; exact vspace.unmap_page_table.hr hA hO h hh hk a asid vaddr ptr
      rintro ⟨s1, a1⟩ w1
      exact (WP.spec_ok _).2 ⟨rfl, w1⟩
    · exact (WP.spec_ok _).2 ⟨rfl, Wr0.refl _⟩
  · exact (WP.spec_ok _).2 ⟨rfl, Wr0.refl _⟩

/-- **A `Pdpt` cap's finalisation** (as `fin_pt.hr`). -/
theorem fin_pdpt.hr (hA : P0.ArchTotal ar) (hO : HrOK kb Pp Tb Lv Hr) (s : S) (a : A)
    (ptr : U64) (mapped : Bool) (asid vaddr : U64) (fin : Bool) (h : VsTy st kb Pp Tb Lv s)
    (hh : HrTy st Pp Hr s) (hk : L.ksb s = kb) :
    objects.finalise_cap_object st ar s a (.Pdpt ptr mapped asid vaddr) fin ⦃ r =>
      r.1 = (.Null, .Null) ∧ Wr0 st (TbO Tb Hr) s r.2.1 ⦄ := by
  unfold objects.finalise_cap_object
  dsimp only
  split
  · split
    · refine WP.spec_bind (Pₘ := fun r : S × A => Wr0 st (TbO Tb Hr) s r.1) ?_ ?_
      · unfold vspace.unmap_pdpt; exact vspace.unmap_page_table.hr hA hO h hh hk a asid vaddr ptr
      rintro ⟨s1, a1⟩ w1
      exact (WP.spec_ok _).2 ⟨rfl, w1⟩
    · exact (WP.spec_ok _).2 ⟨rfl, Wr0.refl _⟩
  · exact (WP.spec_ok _).2 ⟨rfl, Wr0.refl _⟩

end fin

namespace W7
namespace R
namespace ST

section hrk
variable {OS Vc Ub D Fp : Set U64} {kb : U64} {Pp Tb Pt Hr : Set U64} {Lv : U64 → Nat}
variable {A : Type _} {ar : machine.Arch A}

/-- **An ASID-pool cap's finalisation** (QueueVsK's `fin_pool.z` text): also the `R + 4088` words kept. -/
theorem fin_pool.hr (hA : P0.ArchTotal ar) (hR : VrOK Ω Sg Scs Z OS Vc Ub kb Pt) (hO : HrOK kb Pp Tb Lv Hr)
    (hRal : ∀ R ∈ Hr, Aligned (wa R 4088#u64))
    (s : S) (a : A) (ptr base : U64) (fin : Bool) (hk : L.ksb s = kb) :
    objects.finalise_cap_object st ar s a (.AsidPool ptr base) fin ⦃ r =>
      r.1 = (.Null, .Null) ∧ WritesIn st s r.2.1 (VsR kb Pt) ∧ VsZ st kb Pt s r.2.1 ∧ HrW st Hr s r.2.1 ⦄ := by
  unfold objects.finalise_cap_object
  dsimp only
  have hset : ∀ hi, vspace.set_asid_table st s hi 0#u64 ⦃ s1 =>
      WritesIn st s s1 (VsR kb Pt) ∧ VsZ st kb Pt s s1 ∧ HrW st Hr s s1 ⦄ := fun hi =>
    WP.spec_mono (vspace.set_asid_table.as s hi 0#u64) fun s1 ⟨o, h1, h2, h8, e⟩ => by
      have hA' : AsW kb (wa (L.ksb s) o) := ⟨o, h1, h2, h8, by rw [hk]⟩
      have hb : VsR kb Pt (wa (L.ksb s) o) := Or.inr hA'
      rw [e]
      refine ⟨(writesIn_wr (hR.al _ hb)).mono fun b eb => by rw [eb]; exact hb, VsZ.wr0 hR.al (hR.al _ hb),
        fun R hRm => L.mem_wr_ne (hR.al _ hb) (hRal R hRm) fun ev => hO.asw R hRm ?_⟩
      rw [← UScalar.eq_of_val_eq ev]; exact hA'
  split
  · refine WP.spec_bind (vspace.delete_asid_pool.q hA s a base ptr
      ⟨WritesIn.refl _ _, VsZ.refl _, fun _ _ => rfl⟩ hset) ?_
    rintro ⟨s1, a1⟩ w1
    exact (WP.spec_ok _).2 ⟨rfl, w1⟩
  · exact (WP.spec_ok _).2 ⟨rfl, WritesIn.refl _ _, VsZ.refl _, fun _ _ => rfl⟩

/-- The `R + 4088` words are aligned `VsR` words. -/
theorem hr_vsr (hTb : Tb ⊆ Pt) (hO : HrOK kb Pp Tb Lv Hr) {R : U64} (hRm : R ∈ Hr) :
    VsR kb Pt (wa R 4088#u64) :=
  Or.inl ⟨R, hTb (hO.sub hRm), 4088#u64, by simp, by simp, rfl⟩

/-- **A `Wr0` step of words other than the `R + 4088` words keeps `VsTy ∧ HrTy`** and writes only `VsR` words. -/
theorem ty_wr0 (hR : VrOK Ω Sg Scs Z OS Vc Ub kb Pt) (hPp : Pp ⊆ Pt) (hTb : Tb ⊆ Pt) (hO : HrOK kb Pp Tb Lv Hr)
    {X : Set U64} (hX : X ⊆ Pt) (hne : ∀ b, PtW X b → ∀ R ∈ Hr, b ≠ wa R 4088#u64) {s s' : S}
    (hY : VsTy st kb Pp Tb Lv s ∧ HrTy st Pp Hr s) (z : Wr0 st X s s') :
    WritesIn st s s' (VsR kb Pt) ∧ (VsTy st kb Pp Tb Lv s' ∧ HrTy st Pp Hr s') := by
  have z' := Wr0.mono hX z
  obtain ⟨w, v⟩ := wr0_vs hR z'
  have k : HrW st Hr s s' := Wr0.hrw (fun b hb => hR.al b (Or.inl (ptw_mono hX hb)))
    (fun R hRm => hR.al _ (hr_vsr hTb hO hRm)) hne z
  exact ⟨w, hY.1.keepZ hPp hTb v, hY.2.keep hPp v k⟩

/-- **`FinKT` of QueueVsK's class `PtQ` over `VsTy ∧ HrTy`**: page tables, frames (device or not), VSpace roots and
ASID pools, alongside `HighVSpace` roots. -/
theorem finKT_hr (hP : P0.ArchTotal ar) (hR : VrOK Ω Sg Scs Z OS Vc Ub kb Pt) (hPp : Pp ⊆ Pt) (hTb : Tb ⊆ Pt)
    (hO : HrOK kb Pp Tb Lv Hr) :
    FinKT st ar kb Pt (fun s => VsTy st kb Pp Tb Lv s ∧ HrTy st Pp Hr s) PtQ := by
  intro s a c fin hY hk hc
  have hTO : TbO Tb Hr ⊆ Pt := fun _ h => hTb h.1
  have tT : ∀ r : (capability.Cap × capability.Cap) × S × A,
      r.1 = (.Null, .Null) ∧ Wr0 st (TbO Tb Hr) s r.2.1 → r.1 = (.Null, .Null) ∧
        WritesIn st s r.2.1 (VsR kb Pt) ∧ (VsTy st kb Pp Tb Lv r.2.1 ∧ HrTy st Pp Hr r.2.1) :=
    fun r ⟨e, z⟩ => ⟨e, ty_wr0 hR hPp hTb hO hTO (fun b hb => hO.tbo hb) hY z⟩
  have tP : ∀ r : (capability.Cap × capability.Cap) × S × A,
      r.1 = (.Null, .Null) ∧ Wr0 st Pp s r.2.1 → r.1 = (.Null, .Null) ∧
        WritesIn st s r.2.1 (VsR kb Pt) ∧ (VsTy st kb Pp Tb Lv r.2.1 ∧ HrTy st Pp Hr r.2.1) :=
    fun r ⟨e, z⟩ => ⟨e, ty_wr0 hR hPp hTb hO hPp (fun b hb => hO.ppw hb) hY z⟩
  have hRal : ∀ R ∈ Hr, Aligned (wa R 4088#u64) := fun R hRm => hR.al _ (hr_vsr hTb hO hRm)
  rcases hc with (((⟨ptr, size, rights, mapped, asid, vaddr, rfl⟩ | ⟨p, m, ad, rfl⟩ | ⟨p, m, ad, rfl⟩) |
    ⟨p, b, rfl⟩ | ⟨ptr, size, rights, mapped, asid, vaddr, rfl⟩) | ⟨p, m, ad, v, rfl⟩ | ⟨p, m, ad, v, rfl⟩ |
    ⟨p, m, ad, v, rfl⟩)
  · rw [fin_cap_eq_obj (by simp)]
    exact WP.spec_mono (fin_frame.hr hP hO s a ptr size rights mapped asid vaddr fin hY.1 hk) tT
  · rw [fin_cap_eq_obj (by simp)]
    exact WP.spec_mono (fin_root.z hP s a p m ad fin (VsTy.ptPool (Pt := Pp) (fun _ h => h) hY.1 hk ad)) tP
  · rw [fin_cap_eq_obj (by simp)]
    exact WP.spec_mono (fin_hvs.z hP s a p m ad fin (VsTy.ptPool (Pt := Pp) (fun _ h => h) hY.1 hk ad)) tP
  · rw [fin_cap_eq_obj (by simp)]
    refine WP.spec_mono (fin_pool.hr hP hR hO hRal s a p b fin hk) fun r ⟨e, w, v, k⟩ => ?_
    exact ⟨e, w, hY.1.keepZ hPp hTb v, hY.2.keep hPp v k⟩
  · rw [fin_cap_eq_obj (by simp)]
    exact WP.spec_mono (fin_dframe.hr hP hO s a ptr size rights mapped asid vaddr fin hY.1 hk) tT
  · rw [fin_cap_eq_obj (by simp)]
    exact WP.spec_mono (fin_pt.hr hP hO s a p m ad v fin hY.1 hY.2 hk) tT
  · rw [fin_cap_eq_obj (by simp)]
    exact WP.spec_mono (fin_pd.hr hP hO s a p m ad v fin hY.1 hY.2 hk) tT
  · rw [fin_cap_eq_obj (by simp)]
    exact WP.spec_mono (fin_pdpt.hr hP hO s a p m ad v fin hY.1 hY.2 hk) tT

/-- **`TyK` of `VsTy ∧ HrTy`**: a step keeping every `VsR` word keeps both. -/
theorem tyk_hr (hPp : Pp ⊆ Pt) (hTb : Tb ⊆ Pt) (hO : HrOK kb Pp Tb Lv Hr) :
    TyK st kb Pt (fun s => VsTy st kb Pp Tb Lv s ∧ HrTy st Pp Hr s) :=
  fun _ _ h k => ⟨h.1.keepZ hPp hTb k.vsz, h.2.keep hPp k.vsz fun R hRm => k _ (hr_vsr hTb hO hRm)⟩

/-! ## The tops -/

/-- **The exposed `cdt.delete` of a slot of `OS` whose cap is `ZQ PtQ` over a domain of `ZQ PtQ` caps keeps `JV`,
alongside `HighVSpace` roots** (`VsTy ∧ HrTy` at the start state; gen 38's `cdt.delete.zqT` is `Hr = ∅`). -/
theorem cdt.delete.zqH (hP : P0.ArchTotal ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS) (hDC : DCan D)
    (hPp : Pp ⊆ Pt) (hTb : Tb ⊆ Pt) {s0 s : S} (hR : VrOK Ω Sg Scs Z OS Vc Ub (L.ksb s0) Pt)
    (hH : HrOK (L.ksb s0) Pp Tb Lv Hr)
    (hW : WuApart OS (L.ksb s0)) (hIO : IrqOK OS D (L.ksb s0)) (hap : IrqStApart OS (L.ksb s0))
    {a : A} {x : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hx : x ∈ OS) (hxI : ¬ IslN (L.ksb s0) x)
    (hD : DomQ st PtQ Vc D Scs Fp (L.idleW s) (L.mem s (scA (L.idleW s))) s)
    (hX : XQ st PtQ Vc D Scs Fp (L.idleW s) (L.mem s (scA (L.idleW s))) x s) (hN : IrqN st (L.ksb s0) s)
    (hY : VsTy st (L.ksb s0) Pp Tb Lv s) (hh : HrTy st Pp Hr s) :
    cdt.delete st ar s a x true ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ⦄ :=
  cdt.delete.zqG (Ty := fun s => VsTy st (L.ksb s0) Pp Tb Lv s ∧ HrTy st Pp Hr s) hP hO hA hV hDO hDC hR
    (finKT_hr hP hR hPp hTb hH) (tyk_hr hPp hTb hH) hW hIO hap h hx hxI hD hX hN ⟨hY, hh⟩

/-- **The thread kind over a domain of `ZQ PtQ` caps, alongside `HighVSpace` roots** (a thread whose VSpace is a
`HighVSpace`, with its page tables, frames and IPC buffer at frame positions). -/
theorem cdt.delete.threadQH (hP : P0.ArchTotal ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS) (hDC : DCan D)
    (hPp : Pp ⊆ Pt) (hTb : Tb ⊆ Pt) {s0 s : S} (hR : VrOK Ω Sg Scs Z OS Vc Ub (L.ksb s0) Pt)
    (hH : HrOK (L.ksb s0) Pp Tb Lv Hr)
    (hW : WuApart OS (L.ksb s0)) (hIO : IrqOK OS D (L.ksb s0)) (hap : IrqStApart OS (L.ksb s0))
    {a : A} {x p : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hx : x ∈ OS) (hxI : ¬ IslN (L.ksb s0) x)
    (hD : DomQ st PtQ Vc D Scs Fp (L.idleW s) (L.mem s (scA (L.idleW s))) s) (hN : IrqN st (L.ksb s0) s)
    (hY : VsTy st (L.ksb s0) Pp Tb Lv s) (hh : HrTy st Pp Hr s)
    (hc : obj.Slot.cap st x s = ok (.Thread p)) (hid : p ≠ L.idleW s) (hpF : p ∉ Fp)
    (hcov : ∀ i : U64, i.val < 7 → slotIdx p i ∈ D) :
    cdt.delete st ar s a x true ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ⦄ :=
  cdt.delete.threadQG (Ty := fun s => VsTy st (L.ksb s0) Pp Tb Lv s ∧ HrTy st Pp Hr s) hP hO hA hV hDO hDC hR
    (finKT_hr hP hR hPp hTb hH) (tyk_hr hPp hTb hH) hW hIO hap h hx hxI hD hN ⟨hY, hh⟩ hc hid hpF hcov

end hrk

/-! ## Decode level -/

section deqh
variable {OS Vc Ub : Set U64} {Dm Fp : Set U64}

/-- **The generic `ZQ` loop at decode level over `FinKT` / `TyK`** (QueueZombieQDec's `del_zq` text). -/
theorem syscall.decode_invocation.del_zqG {A : Type _} {ar : machine.Arch A} (hP : P0.ArchTotal ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : Dm ⊆ OS) (hDC : DCan Dm)
    {Pt : Set U64} {K : capability.Cap → Prop} {Ty : S → Prop}
    {s : S} (a : A) (len : U64) (slot : obj.Slot) (cap : capability.Cap) (blk call don fp : Bool) (buf : U64)
    (extra : Aeneas.Std.Array obj.Slot 3#usize)
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) (hT : SlotTy st T Ω Sg H Rp Nt OS s)
    (hv : VcTy st T Cs Ω H Sg Scs Z Vc Ub s) (hR : VrOK Ω Sg Scs Z OS Vc Ub (L.ksb s) Pt)
    (hK : FinKT st ar (L.ksb s) Pt Ty K) (hTy : TyK st (L.ksb s) Pt Ty)
    (hW : WuApart OS (L.ksb s)) (hIO : IrqOK OS Dm (L.ksb s))
    (hap : IrqStApart OS (L.ksb s)) (hN : IrqN st (L.ksb s) s) (hY : Ty s)
    (hD : DomQ st K Vc Dm Scs Fp (L.idleW s) (L.mem s (scA (L.idleW s))) s)
    (hf : capFam cap = .cnode) (hslot : slot ∈ OS) (hcap : obj.Slot.cap st slot s = ok cap)
    (hk : TgtP st (fun x => XQ st K Vc Dm Scs Fp (L.idleW s) (L.mem s (scA (L.idleW s))) x s ∧
      ¬ IslN (L.ksb s) x) s cap buf) :
    syscall.decode_invocation st ar s a fl4_abi.label.CNodeDelete len slot cap blk call don fp buf extra ⦃ r s' _ =>
      DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ∧ SlotTy st T Ω Sg H Rp Nt OS s' ∧
        VcTy st T Cs Ω H Sg Scs Z Vc Ub s' ⦄ :=
  syscall.decode_invocation.del_genS hO hV a len slot cap blk call don fp buf extra D hT hv hf hslot hcap hk
    fun x hx hkx s1 h1 k1 o1 i1 K1 => by
      have q := D.bxi.1.choose_spec.choose_spec
      have hIT : L.idleW s ∈ T := q.idleT
      have hY1 : Ty s1 := hTy _ _ hY fun b hb => o1 b (q.omega _ (hR.om b hb))
      exact cdt.delete.zqIG hP hO hA hV hDO hDC hR hK hTy hW hIO hap h1 hx hkx.2
        (hD.oka hIO.2 hDO (OKA.of_osk k1)) (hkx.1.oka hx hkx.2 (OKA.of_osk k1)) i1 (K1 _ hIT)
        (hN.oka hIO (OKA.of_osk k1)) hY1

/-- **The `ZQ PtQ` decode alongside `HighVSpace` roots on [J] `SlotTyEntP`** (no new premise): the entry fact's
`Pp`, `Tb`, `Lv` are exposed; `HrOK` (state-free) and `HrTy` (decode start) are case hypotheses. Gen 38's
`del_zqT_ent` is `Hr = ∅` (`HrTy.of_s1`, `HrOK.empty`). -/
theorem syscall.decode_invocation.del_zqH_ent {A : Type _} {ar : machine.Arch A} (hP : P0.ArchTotal ar)
    (hJ : SlotTyEntP st T Cs Ω Sg H Rp Scs Nt Z P3Ok) {s : S} (hE : EntAt st P3Ok s) {cap : capability.Cap}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) :
    ∃ OS Vc Ub Pp Tb : Set U64, ∃ Lv : U64 → Nat, OSOK T Ω Sg OS ∧ SlotTy st T Ω Sg H Rp Nt OS s ∧
      VcTy st T Cs Ω H Sg Scs Z Vc Ub s ∧
      ∀ (a : A) (len : U64) (slot : obj.Slot) (blk call don fp : Bool) (buf : U64) (Dm Fp Hr : Set U64),
        HrOK (L.ksb s) Pp Tb Lv Hr → HrTy st Pp Hr s → Dm ⊆ OS → DCan Dm → IrqOK OS Dm (L.ksb s) →
        IrqN st (L.ksb s) s →
        DomQ st PtQ Vc Dm Scs Fp (L.idleW s) (L.mem s (scA (L.idleW s))) s →
        capFam cap = .cnode → slot ∈ OS → obj.Slot.cap st slot s = ok cap →
        TgtP st (fun x => XQ st PtQ Vc Dm Scs Fp (L.idleW s) (L.mem s (scA (L.idleW s))) x s ∧
          ¬ IslN (L.ksb s) x) s cap buf →
        syscall.decode_invocation st ar s a fl4_abi.label.CNodeDelete len slot cap blk call don fp buf extra
          ⦃ r s' _ => DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ∧ SlotTy st T Ω Sg H Rp Nt OS s' ∧
            VcTy st T Cs Ω H Sg Scs Z Vc Ub s' ⦄ := by
  have q := D.bxi.1.choose_spec.choose_spec
  obtain ⟨OS, Vc, Ub, Pp, Tb, Pt, Lv, hO, hT, -, hap, hA, hV, hv, hW, hPp, hTb, hR, hY⟩ := hJ.entAt hE q.tcbs
  exact ⟨OS, Vc, Ub, Pp, Tb, Lv, hO, hT, hv,
    fun a len slot blk call don fp buf Dm Fp Hr hH hh hDO hDC hIO hN hD hf hs hc hk =>
    syscall.decode_invocation.del_zqG (Ty := fun s' => VsTy st (L.ksb s) Pp Tb Lv s' ∧ HrTy st Pp Hr s') hP hO hA
      hV hDO hDC a len slot cap blk call don fp buf extra D hT hv hR (finKT_hr hP hR hPp hTb hH)
      (tyk_hr hPp hTb hH) hW hIO hap hN ⟨hY, hh⟩ hD hf hs hc hk⟩

end deqh

end ST
end R
end W7

end

end Fl4ProofsA64.P1
