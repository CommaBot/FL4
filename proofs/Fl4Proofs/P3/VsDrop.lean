/-
P3 (issue #16, VSpace): **the VSpace relation across a detype** (`vsDropOK`,
the VSpace part of the untyped reset's drop step and of MakePool's dirty
case).

l4v's `valid_vspace_objs` constrains only the tables `vs_lookup` reaches
from the ASID table; an unreachable live table may hold an entry to a dead
table (FL4 = seL4 here: `unmap_page_table` returns when the ASID walk fails,
the live page directory keeps its entry). FL4's relation is over ghost sets
(`PtRel`: every table of `L4`..`L2` has its present entries' targets in the
next set; `PoolsIn`: the native pool entries in `L4`; `VsRel`: the pools of
`P`), so after a detype of a region `[rl, rh)` the sets are pruned:

* `VsDrop`: the detype's frame (FL4's words and the spec's objects off the
  region kept, the ASID table and the arch state kept);
* `pr1` .. `pr4`, `prP`: the tables of each set whose frame misses the
  region and whose present entries' targets are in the pruned next set
  (the greatest such subsets level by level);
* `VsReach`: the tables `vs_lookup` reaches from the ASID table, and from
  extra roots `XP X4 X3 X2 X1` of the sets (the caller's choice, e.g. the
  tables of unmapped table caps, which l4v's `valid_table_caps` keeps
  empty);
* `VsReachMiss`: every reached table's frame misses the region — what the
  drop step must provide [J] (l4v: `valid_vs_lookup`, a reachable table is
  named by a cap with its lookup reference, and a childless untyped's
  region holds only dead objects, `dead_childless`: no cap names them);
* `vsDropOK`: `VsRel`, `PtRel` and `PoolsIn` at the pruned sets after the
  detype; the pruned sets are subsets whose members miss the region, and
  hold every reached table.
-/
import Fl4Proofs.P3.VsPtUnmapRel
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Vs
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3

noncomputable section

/-- A 4 KiB frame at `q` misses the region `[rl, rh)`. -/
def FrMiss (rl rh : Nat) (q : U64) : Prop := q.val + 4096 ≤ rl ∨ rh ≤ q.val

/-- **The detype's frame**: FL4's words off the region, the ASID table words
and the spec's objects off the region kept, the arch state kept (l4v
`detype` removes the region's objects; FL4 zeroes the region). -/
structure VsDrop (rl rh : Nat) (ksb : U64) (m m' : U64 → U64) (σ σ' : Fl4Spec.State Unit) : Prop where
  mem : ∀ b : U64, b.val < rl ∨ rh ≤ b.val → m' b = m b
  tbl : ∀ h : U64, h.val < 2048 → m' (atA ksb h) = m (atA ksb h)
  kh : ∀ q : U64, q.val < rl ∨ rh ≤ q.val → σ'.kheap q.bv = σ.kheap q.bv
  arch : σ'.archState = σ.archState

section Prune
variable (rl rh : Nat) (m : U64 → U64)

/-- The page tables kept: off the region. -/
def pr1 (L1 : Set U64) : Set U64 := {q | q ∈ L1 ∧ FrMiss rl rh q}

/-- The page directories kept: off the region, present table entries in `pr1`. -/
def pr2 (L2 L1 : Set U64) : Set U64 :=
  {q | q ∈ L2 ∧ FrMiss rl rh q ∧ ∀ i : U64, i.val < 512 → eP (m (peA q i)) → ¬ eS (m (peA q i)) →
    eT (m (peA q i)) ∈ pr1 rl rh L1}

/-- The PDPTs kept: off the region, present table entries in `pr2`. -/
def pr3 (L3 L2 L1 : Set U64) : Set U64 :=
  {q | q ∈ L3 ∧ FrMiss rl rh q ∧ ∀ i : U64, i.val < 512 → eP (m (peA q i)) → ¬ eS (m (peA q i)) →
    eT (m (peA q i)) ∈ pr2 rl rh m L2 L1}

/-- The PML4s kept: off the region, present entries in `pr3`. -/
def pr4 (L4 L3 L2 L1 : Set U64) : Set U64 :=
  {q | q ∈ L4 ∧ FrMiss rl rh q ∧ ∀ i : U64, i.val < 512 → eP (m (peA q i)) →
    eT (m (peA q i)) ∈ pr3 rl rh m L3 L2 L1}

/-- The ASID pools kept: off the region, native entries in `pr4`. -/
def prP (P L4 L3 L2 L1 : Set U64) : Set U64 :=
  {q | q ∈ P ∧ FrMiss rl rh q ∧ ∀ lo : U64, lo.val < 512 → m (peA q lo) ≠ 0#u64 →
    m (peA q lo) &&& 1#u64 = 0#u64 → m (peA q lo) ∈ pr4 rl rh m L4 L3 L2 L1}

end Prune

/-- **The tables reached** (l4v `vs_lookup`, level 5 the pools, 4 .. 1 the
PML4s .. page tables) from the ASID table and the extra roots. -/
inductive VsReach (m : U64 → U64) (ksb : U64) (XP X4 X3 X2 X1 : Set U64) : Nat → U64 → Prop
  | tbl {h : U64} : h.val < 2048 → m (atA ksb h) ≠ 0#u64 → VsReach m ksb XP X4 X3 X2 X1 5 (m (atA ksb h))
  | xp {q : U64} : q ∈ XP → VsReach m ksb XP X4 X3 X2 X1 5 q
  | x4 {q : U64} : q ∈ X4 → VsReach m ksb XP X4 X3 X2 X1 4 q
  | x3 {q : U64} : q ∈ X3 → VsReach m ksb XP X4 X3 X2 X1 3 q
  | x2 {q : U64} : q ∈ X2 → VsReach m ksb XP X4 X3 X2 X1 2 q
  | x1 {q : U64} : q ∈ X1 → VsReach m ksb XP X4 X3 X2 X1 1 q
  | pool {p lo : U64} : VsReach m ksb XP X4 X3 X2 X1 5 p → lo.val < 512 → m (peA p lo) ≠ 0#u64 →
      m (peA p lo) &&& 1#u64 = 0#u64 → VsReach m ksb XP X4 X3 X2 X1 4 (m (peA p lo))
  | l4 {p i : U64} : VsReach m ksb XP X4 X3 X2 X1 4 p → i.val < 512 → eP (m (peA p i)) →
      VsReach m ksb XP X4 X3 X2 X1 3 (eT (m (peA p i)))
  | l3 {p i : U64} : VsReach m ksb XP X4 X3 X2 X1 3 p → i.val < 512 → eP (m (peA p i)) → ¬ eS (m (peA p i)) →
      VsReach m ksb XP X4 X3 X2 X1 2 (eT (m (peA p i)))
  | l2 {p i : U64} : VsReach m ksb XP X4 X3 X2 X1 2 p → i.val < 512 → eP (m (peA p i)) → ¬ eS (m (peA p i)) →
      VsReach m ksb XP X4 X3 X2 X1 1 (eT (m (peA p i)))

/-- **Every reached table misses the region** [J] (what the drop step
provides: l4v `valid_vs_lookup` with `dead_childless`, see the module
docstring). -/
def VsReachMiss (rl rh : Nat) (m : U64 → U64) (ksb : U64) (XP X4 X3 X2 X1 : Set U64) : Prop :=
  ∀ k q, VsReach m ksb XP X4 X3 X2 X1 k q → FrMiss rl rh q

/-- The set of level `k`. -/
def lvlSet (P L4 L3 L2 L1 : Set U64) : Nat → Set U64
  | 5 => P
  | 4 => L4
  | 3 => L3
  | 2 => L2
  | 1 => L1
  | _ => ∅

section
variable {P L4 L3 L2 L1 XP X4 X3 X2 X1 : Set U64} {m m' : U64 → U64} {ksb : U64}
  {σ σ' : Fl4Spec.State Unit} {rl rh : Nat}

theorem pml4e_tgt {w : U64} {e : Fl4Spec.PML4E} (h : PML4ERel L3 w e) (hp : eP w) : eT w ∈ L3 := by
  cases e with
  | invalidPML4E => exact absurd hp h
  | pdPointerTablePML4E _ _ _ => exact h.2.2

theorem pdpte_tgt {w : U64} {e : Fl4Spec.PDPTE} (h : PDPTERel L2 w e) (hp : eP w) (hs : ¬ eS w) : eT w ∈ L2 := by
  cases e with
  | invalidPDPTE => exact absurd hp h
  | pageDirectoryPDPTE _ _ _ => exact h.2.2.2
  | hugePagePDPTE _ _ _ => exact absurd h.2.1 hs

theorem pde_tgt {w : U64} {e : Fl4Spec.PDE} (h : PDERel L1 w e) (hp : eP w) (hs : ¬ eS w) : eT w ∈ L1 := by
  cases e with
  | invalidPDE => exact absurd hp h
  | pageTablePDE _ _ _ => exact h.2.2.2
  | largePagePDE _ _ _ => exact absurd h.2.1 hs

theorem pml4e_mono {L3' : Set U64} {w : U64} {e : Fl4Spec.PML4E} (h : PML4ERel L3 w e)
    (ht : eP w → eT w ∈ L3') : PML4ERel L3' w e := by
  cases e with
  | invalidPML4E => exact h
  | pdPointerTablePML4E _ _ _ => exact ⟨h.1, h.2.1, ht h.1⟩

theorem pdpte_mono {L2' : Set U64} {w : U64} {e : Fl4Spec.PDPTE} (h : PDPTERel L2 w e)
    (ht : eP w → ¬ eS w → eT w ∈ L2') : PDPTERel L2' w e := by
  cases e with
  | invalidPDPTE => exact h
  | pageDirectoryPDPTE _ _ _ => exact ⟨h.1, h.2.1, h.2.2.1, ht h.1 h.2.1⟩
  | hugePagePDPTE _ _ _ => exact h

theorem pde_mono {L1' : Set U64} {w : U64} {e : Fl4Spec.PDE} (h : PDERel L1 w e)
    (ht : eP w → ¬ eS w → eT w ∈ L1') : PDERel L1' w e := by
  cases e with
  | invalidPDE => exact h
  | pageTablePDE _ _ _ => exact ⟨h.1, h.2.1, h.2.2.1, ht h.1 h.2.1⟩
  | largePagePDE _ _ _ => exact h

/-- **Every reached table is one of its set's** (the closure of `PtRel`,
`PoolsIn` and `VsRel.tmem` from the roots). -/
theorem VsReach.mem (hR : VsRel P m ksb σ) (hPt : PtRel L4 L3 L2 L1 m σ) (hPI : PoolsIn P L4 m)
    (hXP : XP ⊆ P) (hX4 : X4 ⊆ L4) (hX3 : X3 ⊆ L3) (hX2 : X2 ⊆ L2) (hX1 : X1 ⊆ L1)
    {k : Nat} {q : U64} (h : VsReach m ksb XP X4 X3 X2 X1 k q) : q ∈ lvlSet P L4 L3 L2 L1 k := by
  induction h with
  | tbl hh h0 => exact hR.tmem _ hh h0
  | xp hq => exact hXP hq
  | x4 hq => exact hX4 hq
  | x3 hq => exact hX3 hq
  | x2 hq => exact hX2 hq
  | x1 hq => exact hX1 hq
  | pool _ hl h0 ht ih => exact hPI _ ih _ hl h0 ht
  | l4 _ hi hp ih =>
    obtain ⟨f, -, hf⟩ := hPt.l4 _ ih
    exact pml4e_tgt (hf _ hi) hp
  | l3 _ hi hp hs ih =>
    obtain ⟨f, -, hf⟩ := hPt.l3 _ ih
    exact pdpte_tgt (hf _ hi) hp hs
  | l2 _ hi hp hs ih =>
    obtain ⟨f, -, hf⟩ := hPt.l2 _ ih
    exact pde_tgt (hf _ hi) hp hs

/-- **Every reached table is kept by the pruning**, when the reached tables
miss the region. -/
theorem VsReach.pr (hR : VsRel P m ksb σ) (hPt : PtRel L4 L3 L2 L1 m σ) (hPI : PoolsIn P L4 m)
    (hXP : XP ⊆ P) (hX4 : X4 ⊆ L4) (hX3 : X3 ⊆ L3) (hX2 : X2 ⊆ L2) (hX1 : X1 ⊆ L1)
    (hM : VsReachMiss rl rh m ksb XP X4 X3 X2 X1) :
    (∀ q, VsReach m ksb XP X4 X3 X2 X1 1 q → q ∈ pr1 rl rh L1) ∧
    (∀ q, VsReach m ksb XP X4 X3 X2 X1 2 q → q ∈ pr2 rl rh m L2 L1) ∧
    (∀ q, VsReach m ksb XP X4 X3 X2 X1 3 q → q ∈ pr3 rl rh m L3 L2 L1) ∧
    (∀ q, VsReach m ksb XP X4 X3 X2 X1 4 q → q ∈ pr4 rl rh m L4 L3 L2 L1) ∧
    (∀ q, VsReach m ksb XP X4 X3 X2 X1 5 q → q ∈ prP rl rh m P L4 L3 L2 L1) := by
  have hm := fun {k q} (h : VsReach m ksb XP X4 X3 X2 X1 k q) => h.mem hR hPt hPI hXP hX4 hX3 hX2 hX1
  have h1 : ∀ q, VsReach m ksb XP X4 X3 X2 X1 1 q → q ∈ pr1 rl rh L1 := fun q h => ⟨hm h, hM _ _ h⟩
  have h2 : ∀ q, VsReach m ksb XP X4 X3 X2 X1 2 q → q ∈ pr2 rl rh m L2 L1 :=
    fun q h => ⟨hm h, hM _ _ h, fun i hi hp hs => h1 _ (.l2 h hi hp hs)⟩
  have h3 : ∀ q, VsReach m ksb XP X4 X3 X2 X1 3 q → q ∈ pr3 rl rh m L3 L2 L1 :=
    fun q h => ⟨hm h, hM _ _ h, fun i hi hp hs => h2 _ (.l3 h hi hp hs)⟩
  have h4 : ∀ q, VsReach m ksb XP X4 X3 X2 X1 4 q → q ∈ pr4 rl rh m L4 L3 L2 L1 :=
    fun q h => ⟨hm h, hM _ _ h, fun i hi hp => h3 _ (.l4 h hi hp)⟩
  exact ⟨h1, h2, h3, h4, fun q h => ⟨hm h, hM _ _ h, fun lo hl h0 ht => h4 _ (.pool h hl h0 ht)⟩⟩

/-- A frame missing the region: its words and its address off the region. -/
theorem FrMiss.word {q i : U64} (hq : FrMiss rl rh q) (hf : q.val + 4096 ≤ 2 ^ 64) (hi : i.val < 512) :
    (peA q i).val < rl ∨ rh ≤ (peA q i).val := by
  rw [peA_val hf hi]; unfold FrMiss at hq; omega

theorem FrMiss.self {q : U64} (hq : FrMiss rl rh q) : q.val < rl ∨ rh ≤ q.val := by
  unfold FrMiss at hq; omega

/-- **`vsDropOK`: the VSpace relation across a detype** (module docstring):
after a detype whose reached tables miss the region (`VsReachMiss` [J],
the drop step's), `VsRel`, `PtRel` and `PoolsIn` hold at the pruned sets;
they are subsets of the old ones, their members miss the region, and they
hold every reached table. -/
theorem vsDropOK (hR : VsRel P m ksb σ) (hPt : PtRel L4 L3 L2 L1 m σ) (hPI : PoolsIn P L4 m)
    (hPP : PtPlaced L4 L3 L2 L1) (hVP : VsPlaced P ksb) (hD : VsDrop rl rh ksb m m' σ σ')
    (hXP : XP ⊆ P) (hX4 : X4 ⊆ L4) (hX3 : X3 ⊆ L3) (hX2 : X2 ⊆ L2) (hX1 : X1 ⊆ L1)
    (hM : VsReachMiss rl rh m ksb XP X4 X3 X2 X1) :
    let P' := prP rl rh m P L4 L3 L2 L1
    let L4' := pr4 rl rh m L4 L3 L2 L1
    let L3' := pr3 rl rh m L3 L2 L1
    let L2' := pr2 rl rh m L2 L1
    let L1' := pr1 rl rh L1
    VsRel P' m' ksb σ' ∧ PtRel L4' L3' L2' L1' m' σ' ∧ PoolsIn P' L4' m' ∧
      (P' ⊆ P ∧ L4' ⊆ L4 ∧ L3' ⊆ L3 ∧ L2' ⊆ L2 ∧ L1' ⊆ L1) ∧
      (∀ q, q ∈ P' ∨ q ∈ L4' ∨ q ∈ L3' ∨ q ∈ L2' ∨ q ∈ L1' → FrMiss rl rh q) ∧
      (∀ k q, VsReach m ksb XP X4 X3 X2 X1 k q → q ∈ lvlSet P' L4' L3' L2' L1' k) := by
  intro P' L4' L3' L2' L1'
  obtain ⟨r1, r2, r3, r4, r5⟩ := VsReach.pr hR hPt hPI hXP hX4 hX3 hX2 hX1 hM
  have fitT : ∀ q, (q ∈ L4 ∨ q ∈ L3 ∨ q ∈ L2 ∨ q ∈ L1) → q.val + 4096 ≤ 2 ^ 64 :=
    fun q hq => tbl_fit (hPP q hq)
  -- the entries of a kept table are FL4's words before
  have wd : ∀ q i, q.val + 4096 ≤ 2 ^ 64 → FrMiss rl rh q → i.val < 512 → m' (peA q i) = m (peA q i) :=
    fun q i hf hq hi => hD.mem _ (hq.word hf hi)
  refine ⟨⟨fun h hh => ?_, fun h hh hne => ?_, fun q hq => ?_⟩, ⟨fun q hq => ?_, fun q hq => ?_,
    fun q hq => ?_, fun q hq => ?_⟩, fun q hq lo hl hne ht => ?_, ⟨fun _ h => h.1, fun _ h => h.1,
    fun _ h => h.1, fun _ h => h.1, fun _ h => h.1⟩, fun q hq => ?_, fun k q h => ?_⟩
  · rw [hD.arch, hD.tbl h hh]; exact hR.table h hh
  · rw [hD.tbl h hh] at hne ⊢; exact r5 _ (.tbl hh hne)
  · obtain ⟨hqP, hqM, -⟩ := hq
    obtain ⟨f, hk, hf⟩ := hR.pool q hqP
    have hfit := (hVP.pal q hqP).2
    refine ⟨f, by rw [hD.kh q hqM.self]; exact hk, fun lo hl => ?_⟩
    rw [wd q lo hfit hqM hl]; exact hf lo hl
  · obtain ⟨hq4, hqM, hqT⟩ := hq
    obtain ⟨f, hk, hf⟩ := hPt.l4 q hq4
    have hfit := fitT q (Or.inl hq4)
    refine ⟨f, by rw [hD.kh q hqM.self]; exact hk, fun i hi => ?_⟩
    rw [wd q i hfit hqM hi]; exact pml4e_mono (hf i hi) (hqT i hi)
  · obtain ⟨hq3, hqM, hqT⟩ := hq
    obtain ⟨f, hk, hf⟩ := hPt.l3 q hq3
    have hfit := fitT q (Or.inr (Or.inl hq3))
    refine ⟨f, by rw [hD.kh q hqM.self]; exact hk, fun i hi => ?_⟩
    rw [wd q i hfit hqM hi]; exact pdpte_mono (hf i hi) (hqT i hi)
  · obtain ⟨hq2, hqM, hqT⟩ := hq
    obtain ⟨f, hk, hf⟩ := hPt.l2 q hq2
    have hfit := fitT q (Or.inr (Or.inr (Or.inl hq2)))
    refine ⟨f, by rw [hD.kh q hqM.self]; exact hk, fun i hi => ?_⟩
    rw [wd q i hfit hqM hi]; exact pde_mono (hf i hi) (hqT i hi)
  · obtain ⟨hq1, hqM⟩ := hq
    obtain ⟨f, hk, hf⟩ := hPt.l1 q hq1
    have hfit := fitT q (Or.inr (Or.inr (Or.inr hq1)))
    refine ⟨f, by rw [hD.kh q hqM.self]; exact hk, fun i hi => ?_⟩
    rw [wd q i hfit hqM hi]; exact hf i hi
  · obtain ⟨hqP, hqM, hqT⟩ := hq
    have hfit := (hVP.pal q hqP).2
    rw [wd q lo hfit hqM hl] at hne ht ⊢
    exact hqT lo hl hne ht
  · rcases hq with h | h | h | h | h
    · exact h.2.1
    · exact h.2.1
    · exact h.2.1
    · exact h.2.1
    · exact h.2
  · rcases k with _ | _ | _ | _ | _ | _ | k
    · exact False.elim (h.mem hR hPt hPI hXP hX4 hX3 hX2 hX1)
    · exact r1 q h
    · exact r2 q h
    · exact r3 q h
    · exact r4 q h
    · exact r5 q h
    · exact False.elim (h.mem hR hPt hPI hXP hX4 hX3 hX2 hX1)

/-- The pruned sets stay placed. -/
theorem PtPlaced.pr (hPP : PtPlaced L4 L3 L2 L1) :
    PtPlaced (pr4 rl rh m L4 L3 L2 L1) (pr3 rl rh m L3 L2 L1) (pr2 rl rh m L2 L1) (pr1 rl rh L1) := by
  rintro q (h | h | h | h)
  · exact hPP q (Or.inl h.1)
  · exact hPP q (Or.inr (Or.inl h.1))
  · exact hPP q (Or.inr (Or.inr (Or.inl h.1)))
  · exact hPP q (Or.inr (Or.inr (Or.inr h.1)))

theorem VsPlaced.pr (hVP : VsPlaced P ksb) : VsPlaced (prP rl rh m P L4 L3 L2 L1) ksb :=
  ⟨hVP.ksb_al, hVP.ksb_fit, fun q hq => hVP.pal q hq.1, fun q hq => hVP.ptab q hq.1⟩

end

end

end Fl4Proofs.P3.Vs
