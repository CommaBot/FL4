/-
P3 (DESIGN.md §9), VSpace: **the weakened VSpace cap invariant** `VsCapsW`,
the form of `VsCapsIn` meant to be carried at the relation's own sets (a
`JAtZ` field) and to survive a detype (VsDrop's pruning).

`VCapW P L4 L3 L2 L1 c` is `VCapOK` but for the page-table, page-directory
and PDPT caps, whose table must be in its set only while the cap is
**unmapped**: a mapped table may be pruned from the sets by a detype (its
entries may name a dead table of the region; vsreach.md G1), an unmapped one
is empty (l4v `valid_table_caps`: a table cap without an ASID names an empty
table), so it is never pruned. (F1) PML4 caps likewise: a mapped PML4's
table need be in `L4` only while the ASID table reaches it, which `VsRel` +
`PoolsIn` give at each use (`mem_L4_of_find`); deleting a pool's last cap
clears its ASID-table word and leaves an orphaned mapped PML4 behind
(KENTRY-PLAN jc4). ASID pool caps and frame caps keep `VCapOK`.
l4v counterpart: `valid_cap` for the arch caps (`valid_arch_cap`'s
placement part: `cap_aligned`, the ASID facts) with `valid_table_caps`.

Primitives (as VsCapInv's): `of_caps`, `recap`, `remove`, `rename`,
`insert`/`insert_copy`/`insert_fresh` (retype: the sets grown), `at`; from
the strong form `VsCapsIn.toW`; back to `VCapOK` for an unmapped table or
PML4 cap or a pool/frame cap (`VCapW.ok_of`).

`VCapW.transfer` is the step lemma the MDB steps need: a cap whose
`VCapOK` follows from its source's at **every** set (`MdbStep`'s `hv`
facts) is `VCapW` when the source is, provided it is an unmapped table cap
only if its source is one (`TabUn`; FL4's `derive_cap` of a table cap is the
cap itself and errs on an unmapped one, a move keeps the cap).
-/
import Fl4Proofs.P3.VsMdbInv
import Fl4Proofs.P3.VsCapWBase
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Vs
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3

noncomputable section
/-- **The weakened invariant for given ghost sets.** -/
def VsCapsW (P L4 L3 L2 L1 : Set U64) (mem : U64 → U64) (G : MdbGhost) : Prop :=
  ∀ x ∈ G.chains.flatten, VCapW P L4 L3 L2 L1 (capV mem x)

section
variable {P L4 L3 L2 L1 : Set U64}

/-- A non-physical cap is placed (`vcap_nonphys`). -/
theorem vcapW_nonphys {c : capability.Cap} (h : physF c = false) : VCapW P L4 L3 L2 L1 c :=
  (vcap_nonphys h).toW

end


section
variable {P L4 L3 L2 L1 : Set U64} {mem mem' : U64 → U64} {G : MdbGhost}

/-- The strong form gives the weakened one. -/
theorem VsCapsIn.toW (h : VsCapsIn P L4 L3 L2 L1 mem G) : VsCapsW P L4 L3 L2 L1 mem G :=
  fun x hx => (h x hx).toW

/-- The ghost sets grown (retype of a table or pool). -/
theorem VsCapsW.mono {P' L4' L3' L2' L1' : Set U64} (h : VsCapsW P L4 L3 L2 L1 mem G) (hP : P ⊆ P')
    (h4 : L4 ⊆ L4') (h3 : L3 ⊆ L3') (h2 : L2 ⊆ L2') (h1 : L1 ⊆ L1') : VsCapsW P' L4' L3' L2' L1' mem G :=
  fun x hx => (h x hx).mono hP h4 h3 h2 h1

/-- The MDB's caps kept. -/
theorem VsCapsW.of_caps (h : VsCapsW P L4 L3 L2 L1 mem G)
    (hc : ∀ z ∈ G.chains.flatten, capV mem' z = capV mem z) : VsCapsW P L4 L3 L2 L1 mem' G :=
  fun x hx => by rw [hc x hx]; exact h x hx

/-- One slot's cap replaced, placed when the old one is (a remap, an unmap
with the table in its set, a free index). -/
theorem VsCapsW.recap (h : VsCapsW P L4 L3 L2 L1 mem G) (x0 : U64)
    (hv : VCapW P L4 L3 L2 L1 (capV mem x0) → VCapW P L4 L3 L2 L1 (capV mem' x0))
    (hc : ∀ z ∈ G.chains.flatten, z ≠ x0 → capV mem' z = capV mem z) : VsCapsW P L4 L3 L2 L1 mem' G := by
  intro x hx
  by_cases e : x = x0
  · subst e; exact hv (h x hx)
  · rw [hc x hx e]; exact h x hx

/-- A slot removed from its chain (delete): one obligation less. -/
theorem VsCapsW.remove {th : TypedHeap} (hM : MdbLinks th mem G) (h : VsCapsW P L4 L3 L2 L1 mem G) (x0 : U64)
    (hc : ∀ z ∈ G.chains.flatten, z ≠ x0 → capV mem' z = capV mem z) :
    VsCapsW P L4 L3 L2 L1 mem' (remG G x0) := by
  intro x hx
  obtain ⟨hx0, hxn⟩ := (Mdb.mem_removeChains hM.tree.nodup).1 hx
  rw [hc x hx0 hxn]; exact h x hx0

/-- The slots renamed along `e` (move, swap), each cap placed when its
source is. -/
theorem VsCapsW.rename (h : VsCapsW P L4 L3 L2 L1 mem G) (e : U64 ≃ U64)
    (hc : ∀ z ∈ G.chains.flatten, VCapW P L4 L3 L2 L1 (capV mem z) → VCapW P L4 L3 L2 L1 (capV mem' (e z))) :
    VsCapsW P L4 L3 L2 L1 mem' (renG G e) := by
  intro x hx
  have hx0 := (mem_renG e x).1 hx
  have := hc _ hx0 (h _ hx0)
  rwa [Equiv.apply_symm_apply] at this

/-- **A placed cap inserted after `src`** (copy, mint, mutate, retype), the
other caps kept or placed. -/
theorem VsCapsW.insert (h : VsCapsW P L4 L3 L2 L1 mem G) {src dest : U64} (hsrc : src ∈ G.chains.flatten)
    (b : Bool) (hcd : VCapW P L4 L3 L2 L1 (capV mem' dest))
    (hcap : ∀ z ∈ G.chains.flatten, z ≠ dest → VCapW P L4 L3 L2 L1 (capV mem z) →
      VCapW P L4 L3 L2 L1 (capV mem' z)) :
    VsCapsW P L4 L3 L2 L1 mem' (insG G src dest b) := by
  intro x hx
  rcases (mem_flatten_ins hsrc).1 hx with rfl | hx0
  · exact hcd
  · by_cases e : x = dest
    · subst e; exact hcd
    · exact hcap x hx0 e (h x hx0)

/-- A copy: the new cap derived from `src`'s (`VCapW.transfer`), `src`'s
cap kept alike, the others unchanged. -/
theorem VsCapsW.insert_copy (h : VsCapsW P L4 L3 L2 L1 mem G) {src dest : U64} (hsrc : src ∈ G.chains.flatten)
    (b : Bool) (hcd : VCapW P L4 L3 L2 L1 (capV mem src) → VCapW P L4 L3 L2 L1 (capV mem' dest))
    (hcs : VCapW P L4 L3 L2 L1 (capV mem src) → VCapW P L4 L3 L2 L1 (capV mem' src))
    (hcap : ∀ z ∈ G.chains.flatten, z ≠ src → z ≠ dest → capV mem' z = capV mem z) :
    VsCapsW P L4 L3 L2 L1 mem' (insG G src dest b) :=
  h.insert hsrc b (hcd (h src hsrc)) fun z hz hzd hok => by
    by_cases e : z = src
    · subst e; exact hcs hok
    · rw [hcap z hz e hzd]; exact hok

/-- **Retype**: a cap to a fresh object inserted, the sets grown to take it;
the new cap placed in the grown sets. -/
theorem VsCapsW.insert_fresh {P' L4' L3' L2' L1' : Set U64} (h : VsCapsW P L4 L3 L2 L1 mem G)
    (hP : P ⊆ P') (h4 : L4 ⊆ L4') (h3 : L3 ⊆ L3') (h2 : L2 ⊆ L2') (h1 : L1 ⊆ L1')
    {src dest : U64} (hsrc : src ∈ G.chains.flatten) (b : Bool)
    (hcd : VCapW P' L4' L3' L2' L1' (capV mem' dest))
    (hcs : VCapW P L4 L3 L2 L1 (capV mem src) → VCapW P L4 L3 L2 L1 (capV mem' src))
    (hcap : ∀ z ∈ G.chains.flatten, z ≠ src → z ≠ dest → capV mem' z = capV mem z) :
    VsCapsW P' L4' L3' L2' L1' mem' (insG G src dest b) := by
  refine (h.mono hP h4 h3 h2 h1).insert hsrc b hcd fun z hz hzd hok => ?_
  by_cases e : z = src
  · subst e; exact (hcs (h z hz)).mono hP h4 h3 h2 h1
  · rw [hcap z hz e hzd]; exact hok

/-- **Per slot** (the shape the step posts give): every slot holding a cap
after keeps its old cap or holds a placed one, the MDB trees before and
after linking the slots (`MdbLinks`). -/
theorem VsCapsW.of_slots {th : TypedHeap} {G' : MdbGhost} (hM : MdbLinks th mem G) (hM' : MdbLinks th mem' G')
    (h : VsCapsW P L4 L3 L2 L1 mem G)
    (hc : ∀ y, IsSlot th y → capV mem' y ≠ .Null → capV mem' y = capV mem y ∨ VCapW P L4 L3 L2 L1 (capV mem' y)) :
    VsCapsW P L4 L3 L2 L1 mem' G' := by
  intro x hx
  obtain ⟨hs, c, hca, hn⟩ := (hM'.members x).1 hx
  have e : capV mem' x = c := capV_of_capAt hca
  rcases hc x hs (by rw [e]; exact hn) with h1 | h1
  · rw [h1]
    refine h x ((hM.members x).2 ⟨hs, _, capAt_capV mem x, ?_⟩)
    rw [← h1, e]; exact hn
  · exact h1

/-- The slots' caps kept (`SlotsSame`-style), the MDB tree after any. -/
theorem VsCapsW.of_slotsEq {th : TypedHeap} {G' : MdbGhost} (hM : MdbLinks th mem G) (hM' : MdbLinks th mem' G')
    (h : VsCapsW P L4 L3 L2 L1 mem G) (hc : ∀ y, IsSlot th y → capV mem' y = capV mem y) :
    VsCapsW P L4 L3 L2 L1 mem' G' :=
  h.of_slots hM hM' fun y hy _ => Or.inl (hc y hy)

/-- The invariant at a slot of the MDB. -/
theorem VsCapsW.at {th : TypedHeap} (h : VsCapsW P L4 L3 L2 L1 mem G) (hM : MdbLinks th mem G) {x : U64}
    (hx : IsSlot th x) {c : capability.Cap} (hc : capAt mem x = ok c) (hn : c ≠ .Null) :
    VCapW P L4 L3 L2 L1 c := by
  have := h x ((hM.members x).2 ⟨hx, c, hc, hn⟩)
  rwa [capV_of_capAt hc] at this

/-- The strong form at a slot for an unmapped table or PML4 cap, or a pool or
frame cap (`VCapW.ok_of`). -/
theorem VsCapsW.atOK {th : TypedHeap} (h : VsCapsW P L4 L3 L2 L1 mem G) (hM : MdbLinks th mem G) {x : U64}
    (hx : IsSlot th x) {c : capability.Cap} (hc : capAt mem x = ok c) (hn : c ≠ .Null)
    (hm : ∀ p a v, c ≠ .PageTable p true a v ∧ c ≠ .PageDirectory p true a v ∧ c ≠ .Pdpt p true a v ∧
      c ≠ .Pml4 p true a) :
    VCapOK P L4 L3 L2 L1 c :=
  (h.at hM hx hc hn).ok_of hm

end

section
variable {th : TypedHeap} {P L4 L3 L2 L1 : Set U64} {m : U64 → U64}

/-- The MDB form at a tree linking the slots. -/
theorem VsSlotsW.caps {G : MdbGhost} (h : VsSlotsW th P L4 L3 L2 L1 m) (hM : MdbLinks th m G) :
    VsCapsW P L4 L3 L2 L1 m G := fun x hx => h x ((hM.members x).1 hx).1

/-- From the MDB form: a slot outside the tree holds the null cap. -/
theorem VsCapsW.slots {G : MdbGhost} (h : VsCapsW P L4 L3 L2 L1 m G) (hM : MdbLinks th m G) :
    VsSlotsW th P L4 L3 L2 L1 m := by
  intro y hy
  by_cases hn : capV m y = .Null
  · rw [hn]; trivial
  · exact h y ((hM.members y).2 ⟨hy, _, capAt_capV m y, hn⟩)
end

end

end Fl4Proofs.P3.Vs
