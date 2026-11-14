/-
P3 (DESIGN.md §9), VSpace: **the VSpace cap-placement invariant**
(`VsCapInv`): every page-table, page-directory, PDPT, PML4 and ASID pool cap
of the MDB names an object of its ghost set (`L1`, `L2`, `L3`, `L4`, `P`),
with the facts the decode wrappers need: the table's physical address in the
entry mask (`hpa`), a mapped table cap's ASID non-zero and a mapped page
table's address 2 MiB aligned (`hm0`), a mapped PML4 cap's ASID non-zero and
below 2^20 and its pointer non-zero (the extra cap's shape), a mapped frame
cap's ASID non-zero (`hfm`) and its physical address in its size's mask
(`hpaS`/`hpaL`/`hpaH`), and an ASID pool cap's base 512-aligned (`hb`).

`VsCapsIn P L4 L3 L2 L1 mem G` is the invariant for given ghost sets;
`VsCapInv mem G` puts the sets in an existential, so retype can grow them
(`VsCapsIn.mono`).

Per primitive (as `FrameInv`'s): `of_caps`, `recap`, `remove` (delete),
`rename` (move, swap), `insert` (copy, mint and retype: the new cap
`VCapOK`; `insert_fresh` with the sets grown for a new table or pool).
-/
import Fl4Proofs.P3.VsFrameInv
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Vs
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3

noncomputable section

/-- The physical address of `p` in mask `m` (`paddr p & m = paddr p`). -/
def PaM (p m : U64) : Prop :=
  (core.num.U64.wrapping_sub p layout.PPTR_BASE &&& m) = core.num.U64.wrapping_sub p layout.PPTR_BASE

/-- A frame size's address mask. -/
def frameMaskOf : capability.FrameSize → U64
  | .Small => 4503599627366400#u64
  | .Large => 4503599625273344#u64
  | .Huge => 4503598553628672#u64

/-- **A VSpace cap well placed** in the ghost sets (see the module
docstring); the other caps impose nothing. -/
def VCapOK (P L4 L3 L2 L1 : Set U64) : capability.Cap → Prop
  | .PageTable p mp a v => p ∈ L1 ∧ PaM p 4503599627366400#u64 ∧
      (mp = true → a ≠ 0#u64 ∧ v.bv &&& Fl4Spec.mask (Fl4Spec.ptTranslationBits + Fl4Spec.pageBits) = 0)
  | .PageDirectory p mp a _ => p ∈ L2 ∧ PaM p 4503599627366400#u64 ∧ (mp = true → a ≠ 0#u64)
  | .Pdpt p mp a _ => p ∈ L3 ∧ PaM p 4503599627366400#u64 ∧ (mp = true → a ≠ 0#u64)
  | .Pml4 p mp a => p ∈ L4 ∧ p ≠ 0#u64 ∧ (mp = true → a ≠ 0#u64 ∧ a.val < 2 ^ 20)
  | .Frame p sz _ _ m a _ => (m = true → a ≠ 0#u64) ∧ PaM p (frameMaskOf sz)
  | .AsidPool p b => p ∈ P ∧ b.val % 512 = 0
  | _ => True

/-- **The invariant for given ghost sets.** -/
def VsCapsIn (P L4 L3 L2 L1 : Set U64) (mem : U64 → U64) (G : MdbGhost) : Prop :=
  ∀ x ∈ G.chains.flatten, VCapOK P L4 L3 L2 L1 (capV mem x)

/-- **The invariant**, the ghost sets existential. -/
def VsCapInv (mem : U64 → U64) (G : MdbGhost) : Prop :=
  ∃ P L4 L3 L2 L1 : Set U64, VsCapsIn P L4 L3 L2 L1 mem G

theorem VCapOK.mono {P L4 L3 L2 L1 P' L4' L3' L2' L1' : Set U64} (hP : P ⊆ P') (h4 : L4 ⊆ L4') (h3 : L3 ⊆ L3')
    (h2 : L2 ⊆ L2') (h1 : L1 ⊆ L1') {c : capability.Cap} (h : VCapOK P L4 L3 L2 L1 c) :
    VCapOK P' L4' L3' L2' L1' c := by
  cases c <;> simp only [VCapOK] at h ⊢
  all_goals first
    | exact ⟨h1 h.1, h.2⟩
    | exact ⟨h2 h.1, h.2⟩
    | exact ⟨h3 h.1, h.2⟩
    | exact ⟨h4 h.1, h.2⟩
    | exact ⟨hP h.1, h.2⟩
    | exact h

section
variable {P L4 L3 L2 L1 : Set U64} {mem mem' : U64 → U64} {G : MdbGhost}

/-- The ghost sets grown (retype of a table or pool). -/
theorem VsCapsIn.mono {P' L4' L3' L2' L1' : Set U64} (h : VsCapsIn P L4 L3 L2 L1 mem G) (hP : P ⊆ P')
    (h4 : L4 ⊆ L4') (h3 : L3 ⊆ L3') (h2 : L2 ⊆ L2') (h1 : L1 ⊆ L1') : VsCapsIn P' L4' L3' L2' L1' mem G :=
  fun x hx => (h x hx).mono hP h4 h3 h2 h1

theorem VsCapsIn.inv (h : VsCapsIn P L4 L3 L2 L1 mem G) : VsCapInv mem G := ⟨P, L4, L3, L2, L1, h⟩

/-- The MDB's caps kept. -/
theorem VsCapsIn.of_caps (h : VsCapsIn P L4 L3 L2 L1 mem G)
    (hc : ∀ z ∈ G.chains.flatten, capV mem' z = capV mem z) : VsCapsIn P L4 L3 L2 L1 mem' G :=
  fun x hx => by rw [hc x hx]; exact h x hx

/-- One slot's cap replaced by a well-placed one (a remap, an unmap, a free
index). -/
theorem VsCapsIn.recap (h : VsCapsIn P L4 L3 L2 L1 mem G) (x0 : U64)
    (hx : VCapOK P L4 L3 L2 L1 (capV mem' x0))
    (hc : ∀ z ∈ G.chains.flatten, z ≠ x0 → capV mem' z = capV mem z) : VsCapsIn P L4 L3 L2 L1 mem' G := by
  intro x hxm
  by_cases e : x = x0
  · subst e; exact hx
  · rw [hc x hxm e]; exact h x hxm

/-- A slot removed from its chain (delete). -/
theorem VsCapsIn.remove {th : TypedHeap} (hM : MdbLinks th mem G) (h : VsCapsIn P L4 L3 L2 L1 mem G) (x0 : U64)
    (hc : ∀ z ∈ G.chains.flatten, z ≠ x0 → capV mem' z = capV mem z) :
    VsCapsIn P L4 L3 L2 L1 mem' (remG G x0) := by
  intro x hx
  obtain ⟨hx0, hxn⟩ := (Mdb.mem_removeChains hM.tree.nodup).1 hx
  rw [hc x hx0 hxn]; exact h x hx0

/-- The slots renamed along `e` (move, swap), the caps moved with them. -/
theorem VsCapsIn.rename (h : VsCapsIn P L4 L3 L2 L1 mem G) (e : U64 ≃ U64)
    (hc : ∀ z ∈ G.chains.flatten, capV mem' (e z) = capV mem z) : VsCapsIn P L4 L3 L2 L1 mem' (renG G e) := by
  intro x hx
  have hx0 := (mem_renG e x).1 hx
  have := hc _ hx0
  rw [Equiv.apply_symm_apply] at this
  rw [this]; exact h _ hx0

/-- **A well-placed cap inserted after `src`** (copy, mint, mutate, retype),
the other caps kept or well placed. -/
theorem VsCapsIn.insert (h : VsCapsIn P L4 L3 L2 L1 mem G) {src dest : U64} (hsrc : src ∈ G.chains.flatten)
    (b : Bool) (hcd : VCapOK P L4 L3 L2 L1 (capV mem' dest))
    (hcap : ∀ z ∈ G.chains.flatten, z ≠ dest → VCapOK P L4 L3 L2 L1 (capV mem z) →
      VCapOK P L4 L3 L2 L1 (capV mem' z)) :
    VsCapsIn P L4 L3 L2 L1 mem' (insG G src dest b) := by
  intro x hx
  rcases (mem_flatten_ins hsrc).1 hx with rfl | hx0
  · exact hcd
  · by_cases e : x = dest
    · subst e; exact hcd
    · exact hcap x hx0 e (h x hx0)

/-- A copy (`insert` with the other caps unchanged but `src`'s, kept alike). -/
theorem VsCapsIn.insert_copy (h : VsCapsIn P L4 L3 L2 L1 mem G) {src dest : U64} (hsrc : src ∈ G.chains.flatten)
    (b : Bool) (hcd : VCapOK P L4 L3 L2 L1 (capV mem' dest))
    (hcs : VCapOK P L4 L3 L2 L1 (capV mem src) → VCapOK P L4 L3 L2 L1 (capV mem' src))
    (hcap : ∀ z ∈ G.chains.flatten, z ≠ src → z ≠ dest → capV mem' z = capV mem z) :
    VsCapsIn P L4 L3 L2 L1 mem' (insG G src dest b) :=
  h.insert hsrc b hcd fun z hz hzd hok => by
    by_cases e : z = src
    · subst e; exact hcs hok
    · rw [hcap z hz e hzd]; exact hok

/-- **Retype**: a cap to a fresh object inserted, the ghost sets grown to
take the object (`P ⊆ P'`, …); the new cap well placed in the grown sets. -/
theorem VsCapsIn.insert_fresh {P' L4' L3' L2' L1' : Set U64} (h : VsCapsIn P L4 L3 L2 L1 mem G)
    (hP : P ⊆ P') (h4 : L4 ⊆ L4') (h3 : L3 ⊆ L3') (h2 : L2 ⊆ L2') (h1 : L1 ⊆ L1')
    {src dest : U64} (hsrc : src ∈ G.chains.flatten) (b : Bool)
    (hcd : VCapOK P' L4' L3' L2' L1' (capV mem' dest))
    (hcs : VCapOK P L4 L3 L2 L1 (capV mem src) → VCapOK P L4 L3 L2 L1 (capV mem' src))
    (hcap : ∀ z ∈ G.chains.flatten, z ≠ src → z ≠ dest → capV mem' z = capV mem z) :
    VsCapsIn P' L4' L3' L2' L1' mem' (insG G src dest b) := by
  refine (h.mono hP h4 h3 h2 h1).insert hsrc b hcd fun z hz hzd hok => ?_
  by_cases e : z = src
  · subst e; exact (hcs (h z hz)).mono hP h4 h3 h2 h1
  · rw [hcap z hz e hzd]; exact hok

/-- The invariant at a slot of the MDB. -/
theorem VsCapsIn.at {th : TypedHeap} (h : VsCapsIn P L4 L3 L2 L1 mem G) (hM : MdbLinks th mem G) {x : U64}
    (hx : IsSlot th x) {c : capability.Cap} (hc : capAt mem x = ok c) (hn : c ≠ .Null) :
    VCapOK P L4 L3 L2 L1 c := by
  have := h x ((hM.members x).2 ⟨hx, c, hc, hn⟩)
  rwa [capV_of_capAt hc] at this

end

end

end Fl4Proofs.P3.Vs
