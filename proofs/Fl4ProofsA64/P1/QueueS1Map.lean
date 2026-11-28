/-
P1 (aarch64, gen 44): **ARMPageTableMap into a Stage-1 or a `HighVSpace` VSpace at decode level**
(`vspace.decode_page_table`'s other two branches, vspace.rs:1108–1144, and `map_high_page_table`, vspace.rs:1149–1164)
with `VsTy`, `S2Ty`, `ks`, `UnmZ` and `UnmU` — the Stage-1 counterpart of gen 43's
`vspace.decode_page_table.map_s2` (QueueS2Unm), one shared data step for both branches.

* **The descriptor value** (pure): `nat_or59_M`, `s1tab_v` (`make_user_table x`, vspace.rs: `(x & ADDR_MASK) |
  PXN_TABLE | VALID | TABLE` has `e & 3 = 3` and `e & ADDR_MASK = x` for a 4 KiB-aligned `x < 2^48`; QueueS2Map's
  `nat_or3` / `nat_or_M` / `nat_and_M` reused).
* **`VsTy` with a new table** (pure): `VsTy.congrL` (`VsTy` reads `Lv` only on `Tb`), `VsTy.addT` (a table with no
  descriptor-like word joins `Tb`), **`VsTy.map_table`** (the descriptor of `t` written into a word of `p ∈ Tb`; `t`
  joins `Tb` one level below `p`) — the Stage-1 counterpart of gen 41's `S2Ty.map_table`.
* **`S2Ty.wr3`** (pure): gen 41's `S2Ty.wr` with the `R + 4088` side condition weakened to "if the word is some
  `R + 4088`, the value is a table descriptor" (`S2Ty.hi` asks only `e & 3 = 3` there); needed because the
  Stage-1 walk may stop at a root-level slot (shift 39), where `lookup_pt_slot.lv` does not say which level-0
  table it is.
* **[case hypothesis, state-free] `S1Pl kb Pp Tb`**: the Stage-1 tables' physical addresses 4 KiB-aligned below
  `2^48`, their words no pool / ASID-table words, two tables sharing a word equal. Source: page tables / roots are
  `ArmPageTable` / `ArmVSpace` / `ArmHighVSpace` objects of `create_new_objects` (objects.rs:528; arch
  objects.rs:26/48/55), size-aligned, disjoint from each other, from the `ASID_POOL` objects and the ks area
  (the same source as gen 42's `S2Pl`).
* **[case fact] `UnmT st OS Tb s`**: no word of an unmapped `PageTable` / level-0 `Ept` cap's object is a word of a
  `Tb` table — the Stage-1 counterpart of `UnmZ`'s "no word of a `Te` object" clause (QueueS2Map). Source as for
  `UnmZ`: such an object is made zero and unmapped by `create_new_objects`, is never reachable from a pool entry while
  its cap is unmapped (`derive_cap`, objects.rs:207–231, refuses unmapped caps; ARMPageTableUnmap needs a final cap,
  vspace.rs:1097–1107), and `Tb` is read as the live tables reachable from the pools. **Note**: like `UnmZ`'s `Te`
  clause, this reads the ghost set as the *reachable* tables; it is affected by the pending ruling on `Te` /
  reachability (gen 43's finding: ARMPageTableUnmap after VSpace deletion leaves dead tables in the ghost set) — see
  the a64 handoff §48.
* Walks: `vspace.find_asid.ty`, `vspace.find_high_asid.ty`, **`vspace.check_vspace.ty`**,
  **`vspace.check_high_vspace.ty`** (a returned root is a level-0 table of `Tb`, from `VsTy.pool`'s tag-0 / tag-2
  clauses).
* **`s1map_fin`** (the shared data step of both branches): after `set_thread_state`, `set_cap` of the mapped
  `PageTable` cap and the descriptor write into a word of a `Tb` table: `VsTy` over `insert ptr Tb` (level `Lv p + 1`
  at `ptr`), `S2Ty`, `UnmZ` (same `Te`) and `UnmU` (gen 43's `UnmZ.step`).
* **`vspace.map_high_page_table.ty`** (vspace.rs:1149–1164), **`vspace.decode_page_table.map_s1`**
  (`decode_page_table` at `ARMPageTableMap` with an unmapped `PageTable` cap and a `Pml4` or `HighVSpace` cap in the
  extra slot): unchanged, or `ks`, `VsTy` over `insert ptr Tb` (`Lv` extended), `S2Ty`, `UnmZ`, `UnmU`.

No named premise is new; `S1Pl` (state-free) and `UnmT` (a state fact) are case hypotheses, stated as definitions.
-/
import Fl4ProofsA64.P1.QueueS2Frm
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

/-! ## The descriptor value -/

theorem nat_or59_M (y : Nat) : (y ||| 576460752303423488) &&& 281474976706560 = y &&& 281474976706560 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_and, Nat.testBit_or, tb_M i]
  rcases Classical.em (12 ≤ i ∧ i < 48) with h | h
  · have h59 : (576460752303423488 : Nat).testBit i = false := by
      rw [show (576460752303423488 : Nat) = 2 ^ 59 by norm_num, Nat.testBit_two_pow]
      simp only [decide_eq_false_iff_not]; omega
    rw [h59, Bool.or_false]
  · have hf : (decide (12 ≤ i) && decide (i < 48)) = false := by
      simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega
    rw [hf, Bool.and_false, Bool.and_false]

/-- **`make_user_table x`** of a 4 KiB-aligned `x < 2^48`: a table descriptor (`e & 3 = 3`) whose address bits are
`x`. -/
theorem s1tab_v (x : U64) (h1 : x.val % 4096 = 0) (h2 : x.val < 2 ^ 48) :
    vspace.make_user_table x ⦃ v => (v &&& 3#u64) = 3#u64 ∧ (v &&& vspace.ADDR_MASK) = x ⦄ := by
  unfold vspace.make_user_table
  rw [eq_of_spec_fd P0.Consts.vspace.D_PXN_TABLE.spec, eq_of_spec_fd P0.Consts.vspace.D_VALID.spec,
    eq_of_spec_fd P0.Consts.vspace.D_TABLE_OR_PAGE.spec]
  simp only [lift, bind_ok]
  have e1 : ((1#u64 : U64).val) = 1 := rfl
  have e2 : ((2#u64 : U64).val) = 2 := rfl
  have e3 : ((3#u64 : U64).val) = 3 := rfl
  have e59 : ((576460752303423488#u64 : U64).val) = 576460752303423488 := rfl
  refine (WP.spec_ok _).2 ⟨UScalar.eq_of_val_eq ?_, UScalar.eq_of_val_eq ?_⟩
  · simp only [UScalar.val_and, UScalar.val_or, e1, e2, e3, e59]
    exact nat_or3 _
  · simp only [UScalar.val_and, UScalar.val_or, vspace.ADDR_MASK.val_eq, e1, e2, e59]
    rw [nat_or_M, nat_or59_M, nat_and_M h1 h2, nat_and_M h1 h2]

/-! ## The case hypotheses -/

/-- **The Stage-1 tables' placement** (state-free; module docstring). -/
structure S1Pl (kb : U64) (Pp Tb : Set U64) : Prop where
  pa : ∀ p ∈ Tb, (core.num.U64.wrapping_sub p layout.PPTR_BASE).val % 4096 = 0 ∧
    (core.num.U64.wrapping_sub p layout.PPTR_BASE).val < 2 ^ 48
  pp : ∀ b, PtW Tb b → ¬ PtW Pp b
  asw : ∀ b, PtW Tb b → ¬ AsW kb b
  un : ∀ p ∈ Tb, ∀ q ∈ Tb, ∀ o o' : U64, o.val < 4096 → o.val % 8 = 0 → o'.val < 4096 → o'.val % 8 = 0 →
    wa q o' = wa p o → q = p

/-- **[case fact] The unmapped caps' objects lie outside the Stage-1 tables** (module docstring). -/
def UnmT (st : machine.Store S) (OS Tb : Set U64) (s : S) : Prop :=
  ∀ x ∈ OS, ∀ p n, UnmC st x p n s → ∀ o : U64, o.val < n → o.val % 8 = 0 → ¬ PtW Tb (wa p o)

/-! ## `VsTy` with a new table; `S2Ty` after a write -/

section pure
variable {kb n : U64} {Pp Tb Pt Hr Te : Set U64} {Lv Re bits : U64 → Nat}

/-- **`VsTy` reads `Lv` only on `Tb`.** -/
theorem VsTy.congrL {s : S} {Lv' : U64 → Nat} (h : VsTy st kb Pp Tb Lv s) (hL : ∀ p ∈ Tb, Lv' p = Lv p) :
    VsTy st kb Pp Tb Lv' s := by
  refine ⟨h.tbl, fun p hp o ho h8 hne => ?_, fun p hp hl o ho h8 h3 => ?_⟩
  · obtain ⟨a, b⟩ := h.pool p hp o ho h8 hne
    exact ⟨fun h0 => by obtain ⟨c, d⟩ := a h0; exact ⟨c, by rw [hL _ c]; exact d⟩,
      fun h2 => by obtain ⟨c, d⟩ := b h2; exact ⟨c, by rw [hL _ c]; exact d⟩⟩
  · rw [hL p hp] at hl ⊢
    obtain ⟨a, b⟩ := h.desc p hp hl o ho h8 h3
    exact ⟨a, by rw [hL _ a]; exact b⟩

/-- **A new table joins `Tb`** when, at a level below 3, none of its words looks like a descriptor. -/
theorem VsTy.addT {s : S} {t : U64} (h : VsTy st kb Pp Tb Lv s)
    (hz : Lv t < 3 → ∀ o : U64, o.val < 4096 → o.val % 8 = 0 → (L.mem s (wa t o) &&& 3#u64) ≠ 3#u64) :
    VsTy st kb Pp (insert t Tb) Lv s := by
  refine ⟨h.tbl, fun p hp o ho h8 hne => ?_, fun p hp hl o ho h8 h3 => ?_⟩
  · obtain ⟨a, b⟩ := h.pool p hp o ho h8 hne
    exact ⟨fun h0 => by obtain ⟨c, d⟩ := a h0; exact ⟨Set.mem_insert_of_mem _ c, d⟩,
      fun h2 => by obtain ⟨c, d⟩ := b h2; exact ⟨Set.mem_insert_of_mem _ c, d⟩⟩
  · rcases hp with rfl | hp
    · exact absurd h3 (hz hl o ho h8)
    · obtain ⟨a, b⟩ := h.desc p hp hl o ho h8 h3
      exact ⟨Set.mem_insert_of_mem _ a, b⟩

/-- **A Stage-1 table map's descriptor write** (vspace.rs:1129–1142, 1160–1163; the data step): in a table
`p ∈ Tb`, a word written with a table descriptor of a new table `t` whose words look like no descriptor; `t` joins
`Tb` one level below `p`. -/
theorem VsTy.map_table (hal : ∀ w, VsR kb Pt w → Aligned w) (hPp : Pp ⊆ Pt) {t : U64} (hTb : insert t Tb ⊆ Pt)
    (hP1 : S1Pl kb Pp (insert t Tb)) {s : S} (h : VsTy st kb Pp Tb Lv s) (ht : t ∉ Tb) {p o v : U64}
    (hp : p ∈ Tb) (ho : o.val < 4096) (h8 : o.val % 8 = 0)
    (hz : ∀ o : U64, o.val < 4096 → o.val % 8 = 0 → (L.mem s (wa t o) &&& 3#u64) ≠ 3#u64)
    (hvt : wa (v &&& vspace.ADDR_MASK) layout.PPTR_BASE = t) :
    VsTy st kb Pp (insert t Tb) (Function.update Lv t (Lv p + 1)) (L.wr s (wa p o) v) := by
  have hpi : p ∈ insert t Tb := Set.mem_insert_of_mem _ hp
  have hw : PtW (insert t Tb) (wa p o) := ⟨p, hpi, o, ho, h8, rfl⟩
  have hpt : p ≠ t := fun (e : p = t) => ht (e ▸ hp)
  have hL : ∀ q ∈ Tb, Function.update Lv t (Lv p + 1) q = Lv q :=
    fun q hq => Function.update_of_ne (fun (e : q = t) => ht (e ▸ hq)) _ _
  refine VsTy.wr hal hPp hTb (hal _ (Or.inl (ptw_mono hTb hw))) (VsTy.addT (VsTy.congrL h hL) fun _ => hz)
    (fun o' h1 h2 h8' e _ => (hP1.asw _ hw ⟨o', h1, h2, h8', e.symm⟩).elim)
    (fun q hq o' ho' h8' e _ => (hP1.pp _ hw ⟨q, hq, o', ho', h8', e.symm⟩).elim)
    (fun q hq _ o' ho' h8' e _ => ?_)
  have hqp := hP1.un p hpi q hq o o' ho h8 ho' h8' e
  subst hqp
  refine ⟨?_, ?_⟩
  · rw [hvt]; exact Set.mem_insert t Tb
  · rw [hvt, Function.update_self, Function.update_of_ne hpt]

/-- **`S2Ty` after one aligned write** (gen 41's `S2Ty.wr` with a weaker `R + 4088` condition: if the word is some
`R + 4088`, the value is a table descriptor). -/
theorem S2Ty.wr3 (hal : ∀ w, VsR kb Pt w → Aligned w) (hPp : Pp ⊆ Pt) (hTe : Gran Te bits ⊆ Pt)
    (hS : S2OK Te bits Hr) (hRal : ∀ R ∈ Hr, Aligned (wa R 4088#u64)) {s : S} {b v : U64} (hb : Aligned b)
    (h : S2Ty st n Pp Hr Te Re bits s)
    (hp : ∀ p ∈ Pp, ∀ o : U64, o.val < 4096 → o.val % 8 = 0 → wa p o = b → v ≠ 0#u64 → TagC n Hr Te Re bits v)
    (hh : ∀ R ∈ Hr, wa R 4088#u64 = b → (v &&& 3#u64) = 3#u64)
    (hd : ∀ p ∈ Te, 0 < Re p → ∀ o : U64, o.val < 2 ^ bits p → o.val % 8 = 0 → wa p o = b →
      (v &&& 3#u64) = 3#u64 → DescC Te Re v (Re p)) :
    S2Ty st n Pp Hr Te Re bits (L.wr s b v) := by
  refine ⟨fun p hp' o ho h8 hne => ?_, fun R hR => ?_, fun p hp' hr o ho h8 h3 => ?_⟩
  · rcases mem_wr_cases (L := L) (s := s) (v := v) hb (hal _ (Or.inl (ptw_mono hPp ⟨p, hp', o, ho, h8, rfl⟩))) with
      ⟨e, hm⟩ | ⟨-, hm⟩
    · rw [hm] at hne ⊢; exact hp p hp' o ho h8 e hne
    · rw [hm] at hne ⊢; exact h.tag p hp' o ho h8 hne
  · rcases mem_wr_cases (L := L) (s := s) (v := v) hb (hRal R hR) with ⟨e, hm⟩ | ⟨-, hm⟩
    · rw [hm]; exact hh R hR e
    · rw [hm]; exact h.hi R hR
  · rcases mem_wr_cases (L := L) (s := s) (v := v) hb
      (hal _ (Or.inl (ptw_mono hTe (ptwb_gran hS.sz ⟨p, hp', o, ho, h8, rfl⟩)))) with ⟨e, hm⟩ | ⟨-, hm⟩
    · rw [hm] at h3 ⊢; exact hd p hp' hr o ho h8 e h3
    · rw [hm] at h3 ⊢; exact h.desc p hp' hr o ho h8 h3

end pure

/-! ## The roots -/

section roots
variable {kb : U64} {Pp Tb : Set U64} {Lv : U64 → Nat}

set_option maxHeartbeats 2000000 in
/-- **`find_asid`** (vspace.rs:245–251) returns a level-0 root of `Tb` (a tag-0 pool entry). -/
theorem vspace.find_asid.ty {s : S} (h : VsTy st kb Pp Tb Lv s) (hk : L.ksb s = kb) (asid : U64) :
    vspace.find_asid st s asid ⦃ r => ∀ v, r = .Ok v → v ∈ Tb ∧ Lv v = 0 ⦄ := by
  unfold vspace.find_asid
  refine WP.spec_bind (vspace.find_asid_raw.ty h hk asid) fun r hr => ?_
  rcases r with r1 | e
  · obtain ⟨p, hp, o, ho, h8, er, hr0⟩ := hr r1 rfl
    have hpl := h.pool p hp o ho h8 (by rw [← er]; exact hr0)
    rw [← er] at hpl
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, lift, rtag, rs1]
    split
    · exact (WP.spec_ok _).2 fun v e => by cases e
    · rename_i h0
      exact (WP.spec_ok _).2 fun v e => by cases e; exact hpl.1 (by apply UScalar.eq_of_val_eq; simpa using h0)
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok]
    exact (WP.spec_ok _).2 fun v e => by cases e

set_option maxHeartbeats 2000000 in
/-- **`find_high_asid`** (vspace.rs:254–260) returns a level-0 root of `Tb` (a tag-2 pool entry, untagged). -/
theorem vspace.find_high_asid.ty {s : S} (h : VsTy st kb Pp Tb Lv s) (hk : L.ksb s = kb) (asid : U64) :
    vspace.find_high_asid st s asid ⦃ r => ∀ v, r = .Ok v → v ∈ Tb ∧ Lv v = 0 ⦄ := by
  unfold vspace.find_high_asid
  refine WP.spec_bind (vspace.find_asid_raw.ty h hk asid) fun r hr => ?_
  rcases r with r1 | e
  · obtain ⟨p, hp, o, ho, h8, er, hr0⟩ := hr r1 rfl
    have hpl := h.pool p hp o ho h8 (by rw [← er]; exact hr0)
    rw [← er] at hpl
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, lift, rtag, rhigh]
    split
    · exact (WP.spec_ok _).2 fun v e => by cases e
    · rename_i h0
      exact (WP.spec_ok _).2 fun v e => by cases e; exact hpl.2 (by apply UScalar.eq_of_val_eq; simpa using h0)
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok]
    exact (WP.spec_ok _).2 fun v e => by cases e

set_option maxHeartbeats 2000000 in
/-- **`check_vspace`** (vspace.rs:593–608): a mapped `Pml4` cap's root is a level-0 root of `Tb`. -/
theorem vspace.check_vspace.ty {s : S} (h : VsTy st kb Pp Tb Lv s) (hk : L.ksb s = kb) (c : capability.Cap)
    (arg : U64) : vspace.check_vspace st s c arg ⦃ r => ∀ v, r = .Ok v → v.1 ∈ Tb ∧ Lv v.1 = 0 ⦄ := by
  unfold vspace.check_vspace
  split
  all_goals try (simp only [error.invalid_cap]; exact (WP.spec_ok _).2 fun v e => by cases e)
  split
  all_goals try (simp only [error.invalid_cap]; exact (WP.spec_ok _).2 fun v e => by cases e)
  simp only [vspace.find_vspace_for_asid]
  refine WP.spec_bind (vspace.find_asid.ty h hk _) fun r hr => ?_
  rcases r with v | e
  · try dsimp only
    split
    · simp only [error.invalid_cap]; exact (WP.spec_ok _).2 fun w e => by cases e
    · rename_i hne
      first | (simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hne) | simp at hne
      subst hne
      exact (WP.spec_ok _).2 fun w e => by cases e; exact hr _ rfl
  · exact (WP.spec_ok _).2 fun w e => by cases e

set_option maxHeartbeats 2000000 in
/-- **`check_high_vspace`** (vspace.rs:610–625): a mapped `HighVSpace` cap's root is a level-0 root of `Tb`. -/
theorem vspace.check_high_vspace.ty {s : S} (h : VsTy st kb Pp Tb Lv s) (hk : L.ksb s = kb) (c : capability.Cap)
    (arg : U64) : vspace.check_high_vspace st s c arg ⦃ r => ∀ v, r = .Ok v → v.1 ∈ Tb ∧ Lv v.1 = 0 ⦄ := by
  unfold vspace.check_high_vspace
  split
  all_goals try (simp only [error.invalid_cap]; exact (WP.spec_ok _).2 fun v e => by cases e)
  split
  all_goals try (simp only [error.invalid_cap]; exact (WP.spec_ok _).2 fun v e => by cases e)
  refine WP.spec_bind (vspace.find_high_asid.ty h hk _) fun r hr => ?_
  rcases r with v | e
  · try dsimp only
    split
    · simp only [error.invalid_cap]; exact (WP.spec_ok _).2 fun w e => by cases e
    · rename_i hne
      first | (simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hne) | simp at hne
      subst hne
      exact (WP.spec_ok _).2 fun w e => by cases e; exact hr _ rfl
  · exact (WP.spec_ok _).2 fun w e => by cases e

end roots

/-! ## The shared data step and the two branches -/

section maps1
variable {OS Vc Ub : Set U64} {kb n : U64} {Pp Tb Pt Hr Te : Set U64} {Lv Re bits : U64 → Nat}
variable {A : Type _} {ar : machine.Arch A}

/-- **The Stage-1 table map's data step** (both branches): from `s`, a state `s2` keeping every `VsR` word and every
other `OS` cap, the slot holding the mapped `PageTable` cap of `ptr`; then the descriptor of `ptr` written into a
word of `p ∈ Tb`. -/
theorem s1map_fin (hR : VrOK Ω Sg Scs Z OS Vc Ub kb Pt) (hO : OSOK T Ω Sg OS) (hPp : Pp ⊆ Pt) (hTb : Tb ⊆ Pt)
    (hTe : Gran Te bits ⊆ Pt) (hH : HrOK kb Pp Tb Lv Hr) (hS : S2OK Te bits Hr) (hD : S2Pl kb Pp Tb Te bits)
    {ptr : U64} (hP1 : S1Pl kb Pp (insert ptr Tb)) {s s2 : S} (hY : VsTy st kb Pp Tb Lv s)
    (h2 : S2Ty st n Pp Hr Te Re bits s) (hU : UnmZ st OS Pt Te bits s) (hV : UnmU st OS Pp s)
    (hUT : UnmT st OS Tb s) {slot a0 v0 : U64} (hsl : slot ∈ OS)
    (hc : obj.Slot.cap st slot s = ok (.PageTable ptr false a0 v0)) {p o v : U64} (hp : p ∈ Tb)
    (ho : o.val < 4096) (h8 : o.val % 8 = 0) (k2 : VsKeep st kb Pt s s2)
    (c2o : ∀ y ∈ OS, y ≠ slot → obj.Slot.cap st y s2 = obj.Slot.cap st y s)
    (c2x : ∃ a' v', obj.Slot.cap st slot s2 = ok (.PageTable ptr true a' v'))
    (hv3 : (v &&& 3#u64) = 3#u64) (hvt : wa (v &&& vspace.ADDR_MASK) layout.PPTR_BASE = ptr) :
    (∀ q ∈ Tb, Function.update Lv ptr (Lv p + 1) q = Lv q) ∧
      VsTy st kb Pp (insert ptr Tb) (Function.update Lv ptr (Lv p + 1)) (L.wr s2 (wa p o) v) ∧
      S2Ty st n Pp Hr Te Re bits (L.wr s2 (wa p o) v) ∧ UnmZ st OS Pt Te bits (L.wr s2 (wa p o) v) ∧
      UnmU st OS Pp (L.wr s2 (wa p o) v) := by
  obtain ⟨hpP, hf⟩ := hU.pt slot hsl ptr a0 v0 hc
  have hu0 : UnmC st slot ptr 4096 s := Or.inl ⟨rfl, a0, v0, hc⟩
  have ht : ptr ∉ Tb := fun h =>
    hUT slot hsl ptr 4096 hu0 0#u64 (by simp) (by simp) ⟨ptr, h, 0#u64, by simp, by simp, rfl⟩
  have hTb' : insert ptr Tb ⊆ Pt := Set.insert_subset_iff.2 ⟨hpP, hTb⟩
  have hz : ∀ o : U64, o.val < 4096 → o.val % 8 = 0 → (L.mem s2 (wa ptr o) &&& 3#u64) ≠ 3#u64 := by
    intro o' ho' h8'
    rw [k2 _ (Or.inl ⟨ptr, hpP, o', ho', h8', rfl⟩), (hf o' ho' h8').2]
    decide
  have hw : PtW Tb (wa p o) := ⟨p, hp, o, ho, h8, rfl⟩
  have hvr : VsR kb Pt (wa p o) := Or.inl (ptw_mono hTb hw)
  have hY2 : VsTy st kb Pp Tb Lv s2 := hY.keepZ hPp hTb (VsKeep.vsz k2)
  have h22 : S2Ty st n Pp Hr Te Re bits s2 :=
    h2.keep hPp hTe hS (VsKeep.vsz k2) fun R hR' => k2 _ (hr_vsr hTb hH hR')
  obtain ⟨a', v', c2x'⟩ := c2x
  have cs3 : obj.Slot.cap st slot (L.wr s2 (wa p o) v) = ok (.PageTable ptr true a' v') := by
    rw [wrv_cap hR hO hvr slot hsl]; exact c2x'
  obtain ⟨hU', hV'⟩ := UnmZ.step (kb := kb) (W := fun b => b = wa p o) (Te' := Te)
    (s' := L.wr s2 (wa p o) v) hsl hU hV
    (fun x hx hne => by rw [wrv_cap hR hO hvr x hx, c2o x hx hne])
    (by rintro p' n' (⟨-, a1, v1, e⟩ | ⟨-, a1, v1, e⟩) <;> rw [cs3] at e <;> cases okinj e)
    (by
      rintro p' (⟨m, a1, v1, e⟩ | ⟨l, m, a1, v1, e⟩) <;> rw [cs3] at e
      · cases okinj e; exact Or.inl ⟨false, a0, v0, hc⟩
      · cases okinj e)
    (by
      rintro p' n' (⟨rfl, m, a1, v1, e⟩ | ⟨rfl, m, a1, v1, e⟩) <;> rw [cs3] at e
      · cases okinj e; exact Or.inl ⟨rfl, false, a0, v0, hc⟩
      · cases okinj e)
    (fun b hb hn => by
      rw [L.mem_wr_ne (hR.al _ hvr) (hR.al b hb) (fun h => hn (UScalar.eq_of_val_eq h).symm), k2 b hb])
    (fun x hx p' n' hu o' ho' h8' e => hUT x hx p' n' hu o' ho' h8' (by rw [e]; exact hw))
    (fun b hb => Or.inl hb)
  refine ⟨fun q hq => Function.update_of_ne (fun (e : q = ptr) => ht (e ▸ hq)) _ _,
    VsTy.map_table hR.al hPp hTb' hP1 hY2 ht hp ho h8 hz hvt, ?_, hU', hV'⟩
  exact S2Ty.wr3 hR.al hPp hTe hS (fun R hR' => hR.al _ (hr_vsr hTb hH hR')) (hR.al _ hvr) h22
    (fun q hq o' ho' h8' e _ => (hP1.pp _ (ptw_mono (Set.subset_insert _ _) hw) ⟨q, hq, o', ho', h8', e.symm⟩).elim)
    (fun _ _ _ => hv3) (fun q hq _ o' ho' h8' e _ => (hD.tb _ ⟨q, hq, o', ho', h8', e.symm⟩ hw).elim)

set_option hygiene false in
/-- The two branches' common tail, from the slot `lookup_pt_slot` found (`hp`, `ho`, `h8`, `hsl'`): the
`D_VALID` check, `set_thread_state`, the cap write, `make_user_table`, the descriptor write, `s1map_fin`. -/
local macro "s1Tail" : tactic => `(tactic| (
  refine spec_ite (fun _ => by asErr) (fun _ => ?_)
  refine WP.spec_bind (LawfulStore.read_spec s lu.slot) fun _ _ => ?_
  refine WP.spec_bind P0.vspace.D_VALID.p0 fun _ _ => ?_
  try simp only [lift, bind_ok]
  refine spec_ite (fun _ => by asErr) (fun _ => ?_)
  refine WP.spec_bind (shl_and63u _) fun _ _ => ?_
  try simp only [lift, bind_ok]
  refine WP.spec_bind (stt_vk hR q hct) fun s1 ⟨w1, k1⟩ => ?_
  have c1 := stt_capk hO q hct w1
  refine WP.spec_bind (WP.spec_and (set_cap_pt hR hO hsl hpc s1 _ _)
    (W7.obj.Slot.set_cap.capw (s := s1) (osw hO hsl))) fun s2 ⟨⟨k2, c2o, c2x⟩, w2⟩ => ?_
  refine WP.spec_bind (show layout.paddr ptr ⦃ x => x = core.num.U64.wrapping_sub ptr layout.PPTR_BASE ⦄ by
    unfold layout.paddr; exact (WP.spec_ok _).2 rfl) fun x ex => ?_
  subst ex
  have hpa := hP1.pa ptr (Set.mem_insert _ _)
  refine WP.spec_bind (s1tab_v _ hpa.1 hpa.2) fun v ⟨hv3, hvm⟩ => ?_
  refine WP.spec_bind (LawfulStore.write_spec s2 lu.slot v) fun s3 e3 => ?_
  subst e3
  rw [hsl']
  obtain ⟨fL, f1, f2, f3, f4⟩ := s1map_fin hR hO hPp hTb hTe hH hS hD hP1 hY h2 hU hV hUT hsl hc hp ho h8
    (k1.trans k2) (fun y hy hne => by rw [c2o y hy hne, c1 y hy]) c2x hv3
    (by rw [hvm]; exact wa_ws ptr layout.PPTR_BASE)
  exact (WP.spec_ok _).2 (Or.inr ⟨by rw [L.ksb_wr, w2.1, w1.1, hk], _, fL, f1, f2, f3, f4⟩)))

set_option maxHeartbeats 4000000 in
/-- **`map_high_page_table`** (vspace.rs:1149–1164; ARMPageTableMap into a `HighVSpace`): the state unchanged, or
`ks`, `VsTy` over `insert ptr Tb` (`Lv` extended), `S2Ty`, `UnmZ`, `UnmU`. -/
theorem vspace.map_high_page_table.ty (hR : VrOK Ω Sg Scs Z OS Vc Ub kb Pt) (hO : OSOK T Ω Sg OS)
    {X : Set U64} {Q : U64 → U64 → List U64} {Rq : U64 → List U64} {s : S}
    (q : SchedQueuesInvX st T Cs Ω H X s Q Rq) (hk : L.ksb s = kb) (hPp : Pp ⊆ Pt) (hTb : Tb ⊆ Pt)
    (hTe : Gran Te bits ⊆ Pt) (hH : HrOK kb Pp Tb Lv Hr) (hS : S2OK Te bits Hr) (hD : S2Pl kb Pp Tb Te bits)
    {ptr a0 v0 : U64} (hP1 : S1Pl kb Pp (insert ptr Tb)) (hY : VsTy st kb Pp Tb Lv s)
    (h2 : S2Ty st n Pp Hr Te Re bits s) (hU : UnmZ st OS Pt Te bits s) (hV : UnmU st OS Pp s)
    (hUT : UnmT st OS Tb s) {slot : U64} (hsl : slot ∈ OS)
    (hc : obj.Slot.cap st slot s = ok (.PageTable ptr false a0 v0)) (vcap : capability.Cap) (vaddr : U64) :
    vspace.map_high_page_table st s slot ptr vcap vaddr ⦃ r => r.2 = s ∨ (L.ksb r.2 = kb ∧
      ∃ Lv' : U64 → Nat, (∀ p ∈ Tb, Lv' p = Lv p) ∧ VsTy st kb Pp (insert ptr Tb) Lv' r.2 ∧
        S2Ty st n Pp Hr Te Re bits r.2 ∧ UnmZ st OS Pt Te bits r.2 ∧ UnmU st OS Pp r.2) ⦄ := by
  have hpc := canon_pt hc
  unfold vspace.map_high_page_table
  refine WP.spec_bind (sched.cur_thread.spec s) fun ct ect => ?_
  have hct : ct ∈ T := by rw [ect]; exact q.curT
  refine WP.spec_bind (vspace.check_high_vspace.ty hY hk vcap 1#u64) fun r hr => ?_
  rcases r with ⟨root, asid1⟩ | e
  swap
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok]
    exact (WP.spec_ok _).2 (Or.inl rfl)
  obtain ⟨hrT, h0⟩ := hr _ rfl
  simp only [irq_branch_ok, bind_ok]
  refine spec_ite (fun _ => by asErr) (fun _ => ?_)
  refine spec_ite (fun _ => by asErr) (fun _ => ?_)
  refine WP.spec_bind (vspace.lookup_pt_slot.lv hY hrT h0 vaddr) fun lu ⟨p, hp, o, ho, h8, hsl', _⟩ => ?_
  refine spec_ite (fun _ => by asErr) (fun _ => ?_)
  s1Tail

set_option maxHeartbeats 4000000 in
/-- **ARMPageTableMap into a Stage-1 or a `HighVSpace` VSpace at decode level** (vspace.rs:1108–1144,
`decode_page_table` at `ARMPageTableMap` with an unmapped `PageTable` cap and a `Pml4` or `HighVSpace` cap in the
extra slot): the state unchanged, or `ks`, `VsTy` over `insert ptr Tb` (`Lv` extended), `S2Ty`, `UnmZ`, `UnmU`. -/
theorem vspace.decode_page_table.map_s1 (hR : VrOK Ω Sg Scs Z OS Vc Ub kb Pt) (hO : OSOK T Ω Sg OS)
    {X : Set U64} {Q : U64 → U64 → List U64} {Rq : U64 → List U64} {s : S}
    (q : SchedQueuesInvX st T Cs Ω H X s Q Rq) (hk : L.ksb s = kb) (hPp : Pp ⊆ Pt) (hTb : Tb ⊆ Pt)
    (hTe : Gran Te bits ⊆ Pt) (hH : HrOK kb Pp Tb Lv Hr) (hS : S2OK Te bits Hr) (hD : S2Pl kb Pp Tb Te bits)
    {ptr a0 v0 : U64} (hP1 : S1Pl kb Pp (insert ptr Tb)) (hY : VsTy st kb Pp Tb Lv s)
    (h2 : S2Ty st n Pp Hr Te Re bits s) (hU : UnmZ st OS Pt Te bits s) (hV : UnmU st OS Pp s)
    (hUT : UnmT st OS Tb s) (a : A) (len slot buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize)
    (hsl : slot ∈ OS) (hc : obj.Slot.cap st slot s = ok (.PageTable ptr false a0 v0))
    (hx : ∀ x ∈ extra.val, x ≠ 0#u64 → (∃ p m asid, obj.Slot.cap st x s = ok (.Pml4 p m asid)) ∨
      (∃ p m asid, obj.Slot.cap st x s = ok (.HighVSpace p m asid))) :
    vspace.decode_page_table st ar s a fl4_abi.label.ARMPageTableMap len slot (.PageTable ptr false a0 v0) buf
      extra ⦃ r => r.2.1 = s ∨ (L.ksb r.2.1 = kb ∧
        ∃ Lv' : U64 → Nat, (∀ p ∈ Tb, Lv' p = Lv p) ∧ VsTy st kb Pp (insert ptr Tb) Lv' r.2.1 ∧
          S2Ty st n Pp Hr Te Re bits r.2.1 ∧ UnmZ st OS Pt Te bits r.2.1 ∧ UnmU st OS Pp r.2.1) ⦄ := by
  have hS' : P0.StoreTotal st := L.total
  have hpc := canon_pt hc
  unfold vspace.decode_page_table
  refine WP.spec_bind (sched.cur_thread.spec s) fun ct ect => ?_
  have hct : ct ∈ T := by rw [ect]; exact q.curT
  try dsimp only
  refine spec_ite (fun h => absurd h (by first | decide | simp [fl4_abi.label.ARMPageTableMap,
    fl4_abi.label.ARMPageTableUnmap])) (fun _ => ?_)
  refine spec_ite (fun _ => by asErr) (fun _ => ?_)
  refine WP.spec_bind (vspace.extra.memA extra 0#usize) fun o ho => ?_
  rcases o with _ | x
  · asErr
  obtain ⟨hxm, hx0⟩ := ho x rfl
  try dsimp only
  refine spec_ite (fun _ => ?_) (fun _ => by asErr)
  refine spec_ite (fun _ => by asErr) (fun _ => ?_)
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS') fun vaddr1 _ => ?_
  rcases hx x hxm hx0 with ⟨p0, m0, as0, hxc⟩ | ⟨p0, m0, as0, hxc⟩
  · refine WP.spec_bind (show obj.Slot.cap st x s ⦃ c => c = .Pml4 p0 m0 as0 ⦄ by
      rw [hxc]; exact (WP.spec_ok _).2 rfl) fun vcap hv => ?_
    subst hv
    refine WP.spec_bind (Pₘ := fun b => b = false) ((WP.spec_ok _).2 rfl) fun b hb => ?_
    refine spec_ite (fun h => by rw [hb] at h; cases h) (fun _ => ?_)
    refine WP.spec_bind (P0.vspace.is_valid_vtable_root.p0 _) fun b1 _ => ?_
    refine spec_ite (fun _ => ?_) (fun _ => by asErr)
    refine WP.spec_bind (Pₘ := fun b => b = false) ((WP.spec_ok _).2 rfl) fun b2 hb2 => ?_
    refine spec_ite (fun h => by rw [hb2] at h; cases h) (fun _ => ?_)
    refine spec_ite (fun _ => by asErr) (fun _ => ?_)
    refine WP.spec_bind (vspace.check_vspace.ty hY hk _ 1#u64) fun r hr => ?_
    rcases r with ⟨root, asid1⟩ | e
    swap
    · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
        bind_tc_ok]
      exact (WP.spec_ok _).2 (Or.inl rfl)
    obtain ⟨hrT, h0⟩ := hr _ rfl
    simp only [irq_branch_ok, bind_ok]
    refine WP.spec_bind (vspace.lookup_pt_slot.lv hY hrT h0 vaddr1) fun lu ⟨p, hp, o, ho, h8, hsl', _⟩ => ?_
    s1Tail
  · refine WP.spec_bind (show obj.Slot.cap st x s ⦃ c => c = .HighVSpace p0 m0 as0 ⦄ by
      rw [hxc]; exact (WP.spec_ok _).2 rfl) fun vcap hv => ?_
    subst hv
    refine WP.spec_bind (Pₘ := fun b => b = true) ((WP.spec_ok _).2 rfl) fun b hb => ?_
    refine spec_ite (fun _ => ?_) (fun h => absurd hb h)
    refine WP.spec_bind (vspace.map_high_page_table.ty hR hO q hk hPp hTb hTe hH hS hD hP1 hY h2 hU hV hUT hsl hc
      _ vaddr1) ?_
    rintro ⟨r, s1⟩ h
    try simp only [uncurry_apply_pair]
    try dsimp only
    exact (WP.spec_ok _).2 h

end maps1

end ST
end R
end W7

end

end Fl4ProofsA64.P1
