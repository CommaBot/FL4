/-
P3 (issue #16, F1 stage 2; F1-PLAN §1.6–1.7, KENTRY-PLAN f1 / f2): **the
ref-carrying ASID walk and the VSpace naming invariant** (l4v `vs_lookup` with
`vs_refs`, `valid_vs_lookup`, `unique_table_refs`, `unique_table_caps`,
`valid_table_caps`, and "a live pool cap's pool is in the ASID table").

* `VsPath m ksb k q a v`: the walk from the ASID table to the table `q` of
  level `k` (5 pools, 4 PML4s, 3 PDPTs, 2 PDs, 1 PTs), with its ref: the ASID
  (pool base for a pool) `a` and the vaddr prefix `v` (as `Nat`, no wrap).
  Unlike `VsReach` (VsDrop) it has no extra roots.
* `VKey` / `VRefOf` / `VRef`: a cap's VSpace key (level, object) and the ref it
  carries (mapped flag, ASID or pool base, vaddr; l4v `vs_cap_ref`).
* `VsNamed th m ksb`:
  - `named`: every walk node is named by a slot's cap with the walk's ref;
  - `uref`: the caps of one object carry one ref;
  - `uun`: an unmapped table / PML4 cap is the only cap of its object;
  - `empty`: an unmapped cap's table has no present entry (a PML4: its user
    half, `i < 256`; `copy_global_mappings` writes 256..511);
  - `poolT`: a pool cap's pool is the ASID table's word at its base.
* `VsReach.split`: with the F1 roots (`NeedR`: unmapped caps' tables and pool
  caps' pools), every reached table is a root or a walk node (a pool root is a
  walk node by `poolT`; nothing is reached through an unmapped root by `empty`).
* `VsReach.frame`, `VsPath.frame`, `VsNamed.frame`: the same walk words (the
  ASID table, the sets' tables and pools) give the same walks; with the slots'
  caps kept, `VsNamed` is kept (`walk_of_vobj`: from the `VObj` words kept).
* **`JAtZ.vsReachMiss`**: at a `JAtZ` state with `VsNamed`, every table reached
  from the `NeedR` roots misses a childless untyped cap's region (RAM or device):
  a root or a walk node is the object of a slot's table / PML4 / pool cap
  (`named`), which `JAtZ.tabOff` puts off the region. `JAtZ.vsReachMissR` is the
  form at the caller's restart state (C17 / C23 / C24 vsReach premise shape),
  `JAtZ.vsReachAsidC` the `JAsidCPath.vsReach` shape.

Not yet wired: `VsNamed` is a hypothesis here (F1 stage 5 adds it to `JCarry`).
-/
import Fl4Proofs.P3.UtDropJ2
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3

open fl4_core

theorem physF_pml4 (q : U64) (mp : Bool) (a : U64) : physF (.Pml4 q mp a) = true := ok_inj (phys_eq _).symm
theorem ptrF_pml4 (q : U64) (mp : Bool) (a : U64) : ptrF (.Pml4 q mp a) = q := ok_inj (ptr_eq _).symm
theorem sizeF_pml4 (q : U64) (mp : Bool) (a : U64) : sizeF (.Pml4 q mp a) = 12#u64 := ok_inj (size_eq _).symm
theorem physF_pool (q b : U64) : physF (.AsidPool q b) = true := ok_inj (phys_eq _).symm
theorem ptrF_pool (q b : U64) : ptrF (.AsidPool q b) = q := ok_inj (ptr_eq _).symm
theorem sizeF_pool (q b : U64) : sizeF (.AsidPool q b) = 12#u64 := by
  have h : sizeF (.AsidPool q b) = fl4_abi.consts.bits.ASID_POOL := ok_inj (size_eq _).symm
  rw [h]; unfold fl4_abi.consts.bits.ASID_POOL; rfl

namespace Vs
open Fl4Proofs.P1

noncomputable section

/-! ## Definitions -/

/-- (F1) **The ASID-table walk with its ref** (l4v `vs_lookup` with `vs_refs`):
level `k` (5 pools, 4 PML4s, 3 PDPTs, 2 PDs, 1 PTs), table `q`, ASID (pool
base) `a`, vaddr prefix `v`. -/
inductive VsPath (m : U64 → U64) (ksb : U64) : Nat → U64 → Nat → Nat → Prop
  | tbl {hi : U64} : hi.val < 2048 → m (atA ksb hi) ≠ 0#u64 → VsPath m ksb 5 (m (atA ksb hi)) (hi.val * 512) 0
  | pool {p : U64} {b : Nat} {lo : U64} : VsPath m ksb 5 p b 0 → lo.val < 512 → m (peA p lo) ≠ 0#u64 →
      m (peA p lo) &&& 1#u64 = 0#u64 → VsPath m ksb 4 (m (peA p lo)) (b + lo.val) 0
  | l4 {p : U64} {a : Nat} {i : U64} : VsPath m ksb 4 p a 0 → i.val < 256 → eP (m (peA p i)) →
      VsPath m ksb 3 (eT (m (peA p i))) a (i.val * 2 ^ 39)
  | l3 {p : U64} {a v : Nat} {i : U64} : VsPath m ksb 3 p a v → i.val < 512 → eP (m (peA p i)) →
      ¬ eS (m (peA p i)) → VsPath m ksb 2 (eT (m (peA p i))) a (v + i.val * 2 ^ 30)
  | l2 {p : U64} {a v : Nat} {i : U64} : VsPath m ksb 2 p a v → i.val < 512 → eP (m (peA p i)) →
      ¬ eS (m (peA p i)) → VsPath m ksb 1 (eT (m (peA p i))) a (v + i.val * 2 ^ 21)

/-- The VSpace key of a cap: level and object (PT 1 … PML4 4, pool 5). -/
def VKey : capability.Cap → Option (Nat × U64)
  | .PageTable q _ _ _ => some (1, q)
  | .PageDirectory q _ _ _ => some (2, q)
  | .Pdpt q _ _ _ => some (3, q)
  | .Pml4 q _ _ => some (4, q)
  | .AsidPool q _ => some (5, q)
  | _ => none

/-- The ref a cap carries (l4v `vs_cap_ref`): mapped flag, ASID / pool base,
vaddr. -/
def VRefOf : capability.Cap → Option (Bool × Nat × Nat)
  | .PageTable _ mp a v => some (mp, a.val, v.val)
  | .PageDirectory _ mp a v => some (mp, a.val, v.val)
  | .Pdpt _ mp a v => some (mp, a.val, v.val)
  | .Pml4 _ mp a => some (mp, a.val, 0)
  | .AsidPool _ b => some (true, b.val, 0)
  | _ => none

/-- A cap names the walk node `(k, q, a, v)`. -/
def VRef (c : capability.Cap) (k : Nat) (q : U64) (a v : Nat) : Prop :=
  VKey c = some (k, q) ∧ VRefOf c = some (true, a, v)

/-- (F1) **The VSpace naming invariant** (module docstring; l4v
`valid_vs_lookup` + `unique_table_refs` + `unique_table_caps` +
`valid_table_caps` + the ASID table's pools named). -/
structure VsNamed (th : TypedHeap) (m : U64 → U64) (ksb : U64) : Prop where
  named : ∀ k q a v, VsPath m ksb k q a v → ∃ y, IsSlot th y ∧ VRef (capV m y) k q a v
  uref : ∀ y y', IsSlot th y → IsSlot th y' → VKey (capV m y) = VKey (capV m y') → VKey (capV m y) ≠ none →
    VRefOf (capV m y) = VRefOf (capV m y')
  uun : ∀ y y', IsSlot th y → IsSlot th y' → VKey (capV m y) = VKey (capV m y') → TabUn (capV m y) → y = y'
  empty : ∀ y, IsSlot th y → TabUn (capV m y) → ∀ k q, VKey (capV m y) = some (k, q) →
    ∀ i : U64, i.val < (if k = 4 then 256 else 512) → ¬ eP (m (peA q i))
  poolT : ∀ y, IsSlot th y → ∀ q b, capV m y = .AsidPool q b → ∀ hi : U64, hi.val * 512 = b.val →
    m (atA ksb hi) = q

/-! ## Cap facts -/

/-- A keyed cap is a page-sized physical non-untyped cap at its key's object. -/
theorem vkey_tab {c : capability.Cap} {k : Nat} {q : U64} (h : VKey c = some (k, q)) :
    ptrF c = q ∧ sizeF c = 12#u64 ∧ physF c = true ∧ isUt c = false := by
  cases c <;> simp only [VKey, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at h
  all_goals obtain ⟨-, h2⟩ := h; subst h2
  all_goals first
    | exact ⟨ptrF_pt _ _ _ _, sizeF_pt _ _ _ _, physF_pt _ _ _ _, rfl⟩
    | exact ⟨ptrF_pd _ _ _ _, sizeF_pd _ _ _ _, physF_pd _ _ _ _, rfl⟩
    | exact ⟨ptrF_pdpt _ _ _ _, sizeF_pdpt _ _ _ _, physF_pdpt _ _ _ _, rfl⟩
    | exact ⟨ptrF_pml4 _ _ _, sizeF_pml4 _ _ _, physF_pml4 _ _ _, rfl⟩
    | exact ⟨ptrF_pool _ _, sizeF_pool _ _, physF_pool _ _, rfl⟩

/-- A root's key, and its kind: an unmapped table / PML4 cap or a pool cap. -/
theorem vkey_vneed {c : capability.Cap} {k : Nat} {q : U64} (h : VNeed c k q) :
    VKey c = some (k, q) ∧ (TabUn c ∨ ∃ b, c = .AsidPool q b) := by
  cases h
  · exact ⟨rfl, .inl rfl⟩
  · exact ⟨rfl, .inl rfl⟩
  · exact ⟨rfl, .inl rfl⟩
  · exact ⟨rfl, .inl rfl⟩
  · exact ⟨rfl, .inr ⟨_, rfl⟩⟩

/-- An unmapped keyed cap is a root. -/
theorem vneed_of_un {c : capability.Cap} {k : Nat} {q : U64} (hu : TabUn c) (hk : VKey c = some (k, q)) :
    VNeed c k q := by
  cases c <;> simp only [TabUn, VKey, Option.some.injEq, Prod.mk.injEq] at hu hk
  all_goals obtain ⟨h1, h2⟩ := hk; subst h1; subst h2; subst hu
  · exact .pt
  · exact .pd
  · exact .pdpt
  · exact .pml4

theorem lvl_mem {P L4 L3 L2 L1 : Set U64} {k : Nat} {q : U64} (h : q ∈ lvlSet P L4 L3 L2 L1 k) :
    q ∈ P ∨ q ∈ L4 ∨ q ∈ L3 ∨ q ∈ L2 ∨ q ∈ L1 := by
  unfold lvlSet at h
  split at h
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr (.inl h))
  · exact .inr (.inr (.inr (.inl h)))
  · exact .inr (.inr (.inr (.inr h)))
  · simp at h

/-! ## Walks -/

section
variable {m m' : U64 → U64} {ksb : U64}

theorem VsPath.v5 {q : U64} {a v : Nat} (h : VsPath m ksb 5 q a v) : v = 0 := by cases h; rfl
theorem VsPath.v4 {q : U64} {a v : Nat} (h : VsPath m ksb 4 q a v) : v = 0 := by cases h; rfl

/-- A walk node is reached (from any roots). -/
theorem VsPath.reach {XP X4 X3 X2 X1 : Set U64} {k : Nat} {q : U64} {a v : Nat} (h : VsPath m ksb k q a v) :
    VsReach m ksb XP X4 X3 X2 X1 k q := by
  induction h with
  | tbl hh h0 => exact .tbl hh h0
  | pool _ hl h0 ht ih => exact .pool ih hl h0 ht
  | l4 _ hi hp ih => exact .l4 ih hi hp
  | l3 _ hi hp hs ih => exact .l3 ih hi hp hs
  | l2 _ hi hp hs ih => exact .l2 ih hi hp hs

/-- **A walk node is in its set** (`VsReach.mem` without roots). -/
theorem VsPath.mem {P L4 L3 L2 L1 : Set U64} {σ : Fl4Spec.State Unit} (hR : VsRel P m ksb σ)
    (hPt : PtRel L4 L3 L2 L1 m σ) (hPI : PoolsIn P L4 m) {k : Nat} {q : U64} {a v : Nat}
    (h : VsPath m ksb k q a v) : q ∈ lvlSet P L4 L3 L2 L1 k :=
  (h.reach (XP := ∅) (X4 := ∅) (X3 := ∅) (X2 := ∅) (X1 := ∅)).mem hR hPt hPI (Set.empty_subset _)
    (Set.empty_subset _) (Set.empty_subset _) (Set.empty_subset _) (Set.empty_subset _)

/-- An unmapped root has no present entry (`empty`); a pool is no table. -/
theorem VsNamed.noEnt {th : TypedHeap} (hN : VsNamed th m ksb) {y : U64} (hy : IsSlot th y) {k : Nat} {q : U64}
    (hn : VNeed (capV m y) k q) (hk : k ≠ 5) {i : U64} (hi : i.val < (if k = 4 then 256 else 512)) :
    ¬ eP (m (peA q i)) := by
  obtain ⟨hK, hU⟩ := vkey_vneed hn
  rcases hU with hU | ⟨b, hb⟩
  · exact hN.empty y hy hU k q hK i hi
  · exfalso; rw [hb] at hn; cases hn; exact hk rfl

/-- **A pool root is a walk node** (`poolT`, with the pool cap's base below
`2^20` and a multiple of 512, `VCapOK`). -/
theorem VsNamed.poolPath {th : TypedHeap} {P L4 L3 L2 L1 : Set U64} (hN : VsNamed th m ksb)
    (hS : VsSlotsW th P L4 L3 L2 L1 m) {y q : U64} (hy : IsSlot th y) (hn : VNeed (capV m y) 5 q) :
    ∃ a, VsPath m ksb 5 q a 0 := by
  have hc := hS y hy
  have hpt := hN.poolT y hy
  generalize capV m y = c at hc hn hpt
  cases hn with
  | pool =>
    rename_i b
    simp only [VCapW, VCapOK] at hc
    obtain ⟨⟨-, hq0⟩, hb5, hb20⟩ := hc
    obtain ⟨hi, hiv⟩ : ∃ hi : U64, hi.val = b.val / 512 := by
      refine ⟨⟨BitVec.ofNat 64 (b.val / 512)⟩, ?_⟩
      show (BitVec.ofNat 64 (b.val / 512)).toNat = _
      rw [BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_le_self _ _) b.bv.isLt)
    have he := hpt q b rfl hi (by omega)
    have hp := VsPath.tbl (m := m) (ksb := ksb) (hi := hi) (by omega) (by rw [he]; exact hq0)
    rw [he] at hp
    exact ⟨_, hp⟩

/-- **(F1) With the narrowed roots, every reached table is a root or a walk
node** (F1-PLAN §1.7). -/
theorem VsReach.split {th : TypedHeap} {P L4 L3 L2 L1 : Set U64} (hN : VsNamed th m ksb)
    (hS : VsSlotsW th P L4 L3 L2 L1 m) {k : Nat} {q : U64}
    (h : VsReach m ksb (NeedR th m 5) (NeedR th m 4) (NeedR th m 3) (NeedR th m 2) (NeedR th m 1) k q) :
    (∃ y, IsSlot th y ∧ VNeed (capV m y) k q) ∨ ∃ a v, VsPath m ksb k q a v := by
  induction h with
  | tbl hh h0 => exact .inr ⟨_, _, .tbl hh h0⟩
  | xp hq => exact .inl hq
  | x4 hq => exact .inl hq
  | x3 hq => exact .inl hq
  | x2 hq => exact .inl hq
  | x1 hq => exact .inl hq
  | pool _ hl h0 ht ih =>
    rcases ih with ⟨y, hy, hn⟩ | ⟨a, v, hw⟩
    · obtain ⟨a, hp⟩ := hN.poolPath hS hy hn
      exact .inr ⟨_, _, .pool hp hl h0 ht⟩
    · cases hw.v5; exact .inr ⟨_, _, .pool hw hl h0 ht⟩
  | l4 _ hi hp ih =>
    rcases ih with ⟨y, hy, hn⟩ | ⟨a, v, hw⟩
    · exact absurd hp (hN.noEnt hy hn (by decide) (by split_ifs <;> omega))
    · cases hw.v4; exact .inr ⟨_, _, .l4 hw hi hp⟩
  | l3 _ hi hp hs ih =>
    rcases ih with ⟨y, hy, hn⟩ | ⟨a, v, hw⟩
    · exact absurd hp (hN.noEnt hy hn (by decide) (by split_ifs <;> omega))
    · exact .inr ⟨_, _, .l3 hw hi hp hs⟩
  | l2 _ hi hp hs ih =>
    rcases ih with ⟨y, hy, hn⟩ | ⟨a, v, hw⟩
    · exact absurd hp (hN.noEnt hy hn (by decide) (by split_ifs <;> omega))
    · exact .inr ⟨_, _, .l2 hw hi hp hs⟩

/-! ## Frames -/

/-- The ASID table's words kept. -/
def TblSame (ksb : U64) (m m' : U64 → U64) : Prop :=
  ∀ hi : U64, hi.val < 2048 → m' (atA ksb hi) = m (atA ksb hi)

/-- The sets' table and pool words kept. -/
def SetWSame (P L4 L3 L2 L1 : Set U64) (m m' : U64 → U64) : Prop :=
  ∀ q, (q ∈ P ∨ q ∈ L4 ∨ q ∈ L3 ∨ q ∈ L2 ∨ q ∈ L1) → ∀ i : U64, i.val < 512 → m' (peA q i) = m (peA q i)

/-- **The walk words from the `VObj` words kept** (every frame step's `hout`
form, e.g. `restart_top`). -/
theorem walk_of_vobj {th : TypedHeap} {P L4 L3 L2 L1 : Set U64} (hV : VsPlaced P ksb)
    (hPP : PtPlaced L4 L3 L2 L1) (h : ∀ b, Aligned b → VObj th P L4 L3 L2 L1 ksb b → m' b = m b) :
    TblSame ksb m m' ∧ SetWSame P L4 L3 L2 L1 m m' := by
  refine ⟨fun hi hh => ?_, fun q hq i hi => ?_⟩
  · have hv := atA_val hV.ksb_fit hh
    have := hV.ksb_al
    exact h _ (by unfold Aligned; rw [hv]; omega) (Or.inr (Or.inr (Or.inr (by rw [hv]; omega))))
  · have hqa : q.val % 4096 = 0 := by
      rcases hq with hq | hq
      · exact (hV.pal q hq).1
      · exact hPP q hq
    have hv := peA_val (tbl_fit hqa) hi
    exact h _ (by unfold Aligned; rw [hv]; omega) (Or.inr (Or.inr (Or.inl ⟨q, hq, by rw [hv]; omega,
      by rw [hv]; omega⟩)))

section Fr
variable {P L4 L3 L2 L1 : Set U64} {σ : Fl4Spec.State Unit}
  (hR : VsRel P m ksb σ) (hPt : PtRel L4 L3 L2 L1 m σ) (hPI : PoolsIn P L4 m)
  (hWt : TblSame ksb m m') (hWp : SetWSame P L4 L3 L2 L1 m m')
include hR hPt hPI hWt hWp

/-- **A walk at `m'` is one at `m`** when the walk words are kept (the sets'
relations at `m`). -/
theorem VsPath.frame {k : Nat} {q : U64} {a v : Nat} (h : VsPath m' ksb k q a v) : VsPath m ksb k q a v := by
  induction h with
  | tbl hh h0 => rw [hWt _ hh] at h0 ⊢; exact .tbl hh h0
  | pool _ hl h0 ht ih =>
    have hp := lvl_mem (ih.mem hR hPt hPI)
    rw [hWp _ hp _ hl] at h0 ht ⊢; exact .pool ih hl h0 ht
  | l4 _ hi hp ih =>
    have hq := lvl_mem (ih.mem hR hPt hPI)
    rw [hWp _ hq _ (by omega)] at hp ⊢; exact .l4 ih hi hp
  | l3 _ hi hp hs ih =>
    have hq := lvl_mem (ih.mem hR hPt hPI)
    rw [hWp _ hq _ hi] at hp hs ⊢; exact .l3 ih hi hp hs
  | l2 _ hi hp hs ih =>
    have hq := lvl_mem (ih.mem hR hPt hPI)
    rw [hWp _ hq _ hi] at hp hs ⊢; exact .l2 ih hi hp hs

/-- **A reach at `m'` is one at `m`** when the walk words are kept (roots in
the sets). -/
theorem VsReach.frame {XP X4 X3 X2 X1 : Set U64} (hXP : XP ⊆ P) (hX4 : X4 ⊆ L4) (hX3 : X3 ⊆ L3)
    (hX2 : X2 ⊆ L2) (hX1 : X1 ⊆ L1) {k : Nat} {q : U64} (h : VsReach m' ksb XP X4 X3 X2 X1 k q) :
    VsReach m ksb XP X4 X3 X2 X1 k q := by
  have hm := fun {k q} (h : VsReach m ksb XP X4 X3 X2 X1 k q) => lvl_mem (h.mem hR hPt hPI hXP hX4 hX3 hX2 hX1)
  induction h with
  | tbl hh h0 => rw [hWt _ hh] at h0 ⊢; exact .tbl hh h0
  | xp hq => exact .xp hq
  | x4 hq => exact .x4 hq
  | x3 hq => exact .x3 hq
  | x2 hq => exact .x2 hq
  | x1 hq => exact .x1 hq
  | pool _ hl h0 ht ih =>
    rw [hWp _ (hm ih) _ hl] at h0 ht ⊢; exact .pool ih hl h0 ht
  | l4 _ hi hp ih =>
    rw [hWp _ (hm ih) _ (by omega)] at hp ⊢; exact .l4 ih hi hp
  | l3 _ hi hp hs ih =>
    rw [hWp _ (hm ih) _ hi] at hp hs ⊢; exact .l3 ih hi hp hs
  | l2 _ hi hp hs ih =>
    rw [hWp _ (hm ih) _ hi] at hp hs ⊢; exact .l2 ih hi hp hs

/-- **`VsNamed` across a frame step**: the slots' caps and the walk words
kept (the sets' relations and `VsSlotsW` at `m`). -/
theorem VsNamed.frame {th : TypedHeap} (hN : VsNamed th m ksb) (hS : VsSlotsW th P L4 L3 L2 L1 m)
    (hc : ∀ y, IsSlot th y → capV m' y = capV m y) : VsNamed th m' ksb where
  named k q a v h := by
    obtain ⟨y, hy, hr⟩ := hN.named k q a v (h.frame hR hPt hPI hWt hWp)
    exact ⟨y, hy, by rw [hc y hy]; exact hr⟩
  uref y y' hy hy' := by rw [hc y hy, hc y' hy']; exact hN.uref y y' hy hy'
  uun y y' hy hy' := by rw [hc y hy, hc y' hy']; exact hN.uun y y' hy hy'
  empty y hy hu k q hk i hi := by
    rw [hc y hy] at hu hk
    have hq := lvl_mem (hS.need hy (vneed_of_un hu hk))
    rw [hWp _ hq _ (by split_ifs at hi <;> omega)]
    exact hN.empty y hy hu k q hk i hi
  poolT y hy q b hb hi hib := by
    rw [hc y hy] at hb
    have hcw := hS y hy
    rw [hb] at hcw
    simp only [VCapW, VCapOK] at hcw
    rw [hWt _ (by omega)]
    exact hN.poolT y hy q b hb hi hib

end Fr

/-- The roots at caps kept. -/
theorem NeedR.congr {th : TypedHeap} (hc : ∀ y, IsSlot th y → capV m' y = capV m y) (k : Nat) :
    NeedR th m' k = NeedR th m k := by
  ext q
  constructor
  · rintro ⟨y, hy, hn⟩; exact ⟨y, hy, by rw [← hc y hy]; exact hn⟩
  · rintro ⟨y, hy, hn⟩; exact ⟨y, hy, by rw [hc y hy]; exact hn⟩

end

end

end Vs

/-! ## The discharge at `JAtZ` -/

section
open Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

/-- **(F1) C17 / C23 / C24 vsReach at a `JAtZ` state with `VsNamed`**: every
table reached from the `NeedR` roots misses a childless untyped cap's region
(module docstring). -/
theorem JAtZ.vsReachMiss (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (hN : Vs.VsNamed Z.th (L.mem s) (L.ksb s)) {x p sb fi : U64} {dv : Bool} (hx : x ∈ Z.G.chains.flatten)
    (hcx : capV (L.mem s) x = .Untyped p sb fi dv) (hnd : ∀ y, ¬ Mdb.Desc Z.G.par y x) :
    Vs.VsReachMiss p.val (p.val + 2 ^ sb.val) (L.mem s) (L.ksb s)
      (Vs.NeedR Z.th (L.mem s) 5) (Vs.NeedR Z.th (L.mem s) 4) (Vs.NeedR Z.th (L.mem s) 3)
      (Vs.NeedR Z.th (L.mem s) 2) (Vs.NeedR Z.th (L.mem s) 1) := by
  have hca : capAt (L.mem s) x = ok (.Untyped p sb fi dv) := by rw [capAt_capV, hcx]
  have hsb : sb.val < 64 := capAt_untyped_inv hca
  have hrx := J.ut.reg x hx (by rw [hcx]; exact physF_ut _ _ _ _)
  rw [hcx] at hrx
  obtain ⟨-, -, hfit⟩ := ut_range hsb hrx
  intro k q hR
  have hy : ∃ y, IsSlot Z.th y ∧ Vs.VKey (capV (L.mem s) y) = some (k, q) := by
    rcases hR.split hN J.vsc with ⟨y, hy, hn⟩ | ⟨a, v, hw⟩
    · exact ⟨y, hy, (Vs.vkey_vneed hn).1⟩
    · obtain ⟨y, hy, hk, -⟩ := hN.named _ _ _ _ hw
      exact ⟨y, hy, hk⟩
  obtain ⟨y, hy, hk⟩ := hy
  obtain ⟨hp, hs, hph, hnu⟩ := Vs.vkey_tab hk
  exact J.tabOff hsb hfit hx hcx hnd hy hp hs hph hnu

/-- **(F1) The premise shape: C17 / C23 / C24 vsReach at the caller's restart
state** (`JUtPath.vsReach`, `JUtPathM(U16).vsReach`, `JDevPath.vsReach` with
`x = cslotAddr sl`): `set_thread_state Restart` keeps the slots and the `VObj`
words (`restart_top`), so a reach at `s1` is one at `s` (`VsReach.frame`). -/
theorem JAtZ.vsReachMissR (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (hN : Vs.VsNamed Z.th (L.mem s) (L.ksb s)) (hni : Entered σ) {ct : U64}
    (hct : sched.cur_thread st s = ok ct) {x p sb fi : U64} {dv : Bool} (hx : x ∈ Z.G.chains.flatten)
    (hcx : capV (L.mem s) x = .Untyped p sb fi dv) (hnd : ∀ y, ¬ Mdb.Desc Z.G.par y x) :
    ∀ s1, sched.set_thread_state st s ct sched.TS_RESTART = ok s1 →
      Vs.VsReachMiss p.val (p.val + 2 ^ sb.val) (L.mem s1) (L.ksb s1)
        (Vs.NeedR Z.th (L.mem s1) 5) (Vs.NeedR Z.th (L.mem s1) 4) (Vs.NeedR Z.th (L.mem s1) 3)
        (Vs.NeedR Z.th (L.mem s1) 2) (Vs.NeedR Z.th (L.mem s1) 1) := by
  intro s1 hs1
  obtain ⟨hcur, x0, hk, hrun⟩ := J.curRunnable hni hct
  have hF := J.xtop.fin
  have h := Vs.restart_top s a σ ct x0 hF.1 hF.2.1 hcur.symm hk hrun
  rw [hs1, WP.spec_ok] at h
  obtain ⟨-, -, -, hks, hmV⟩ := h
  have hSS : SlotsSame Z.th (L.mem s) (L.mem s1) := slotsSame_of_vobj J.xtop.rel.1 hmV
  have hc : ∀ y, IsSlot Z.th y → capV (L.mem s1) y = capV (L.mem s) y := fun y hy => hSS.capV hy
  obtain ⟨hWt, hWp⟩ := Vs.walk_of_vobj hF.1.2.vs hF.1.2.pt hmV
  intro k q hR
  rw [hks] at hR
  simp only [Vs.NeedR.congr hc] at hR
  have hN' := J.vsc.needR
  exact J.vsReachMiss hN hx hcx hnd k q
    (hR.frame hF.2.1 hF.2.2.1 hF.2.2.2.1 hWt hWp hN'.1 hN'.2.1 hN'.2.2.1 hN'.2.2.2.1 hN'.2.2.2.2)

/-- **(F1) The `JAsidCPath.vsReach` shape** (C17). -/
theorem JAtZ.vsReachAsidC (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (hN : Vs.VsNamed Z.th (L.mem s) (L.ksb s)) (hni : Entered σ) {ct : U64}
    (hct : sched.cur_thread st s = ok ct) :
    ∀ (x p fi : U64) (s1 : S), x ∈ Z.G.chains.flatten →
      capV (L.mem s) x = .Untyped p fl4_abi.consts.bits.ASID_POOL fi false → (∀ y, ¬ Mdb.Desc Z.G.par y x) →
      sched.set_thread_state st s ct sched.TS_RESTART = ok s1 →
      Vs.VsReachMiss p.val (p.val + 2 ^ (fl4_abi.consts.bits.ASID_POOL).val) (L.mem s1) (L.ksb s1)
        (Vs.NeedR Z.th (L.mem s1) 5) (Vs.NeedR Z.th (L.mem s1) 4) (Vs.NeedR Z.th (L.mem s1) 3)
        (Vs.NeedR Z.th (L.mem s1) 2) (Vs.NeedR Z.th (L.mem s1) 1) :=
  fun _ _ _ s1 hx hc hnd hs1 => J.vsReachMissR hN hni hct hx hc hnd s1 hs1

end

end Fl4Proofs.P3
