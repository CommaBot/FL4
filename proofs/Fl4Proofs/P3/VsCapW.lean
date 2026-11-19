/-
P3 (DESIGN.md §9), VSpace: **the weakened VSpace cap invariant** `VsCapsW`,
the form of `VsCapsIn` meant to be carried at the relation's own sets (a
`JAtZ` field) and to survive a detype (VsDrop's pruning).

`VCapW P L4 L3 L2 L1 c` is `VCapOK` but for the page-table, page-directory
and PDPT caps, whose table must be in its set only while the cap is
**unmapped**: a mapped table may be pruned from the sets by a detype (its
entries may name a dead table of the region; vsreach.md G1), an unmapped one
is empty (l4v `valid_table_caps`: a table cap without an ASID names an empty
table), so it is never pruned. PML4 caps, ASID pool caps and frame caps keep
`VCapOK`: an assigned PML4 and every live pool stay `vs_lookup`-reachable
(deleting a pool's last cap clears its ASID-table word, deleting a PML4's
last cap clears its pool entry), an unassigned PML4 is empty.
l4v counterpart: `valid_cap` for the arch caps (`valid_arch_cap`'s
placement part: `cap_aligned`, the ASID facts) with `valid_table_caps`.

Primitives (as VsCapInv's): `of_caps`, `recap`, `remove`, `rename`,
`insert`/`insert_copy`/`insert_fresh` (retype: the sets grown), `at`; from
the strong form `VsCapsIn.toW`; back to `VCapOK` for an unmapped table cap
or a PML4/pool/frame cap (`VCapW.ok_of`).

`VCapW.transfer` is the step lemma the MDB steps need: a cap whose
`VCapOK` follows from its source's at **every** set (`MdbStep`'s `hv`
facts) is `VCapW` when the source is, provided it is an unmapped table cap
only if its source is one (`TabUn`; FL4's `derive_cap` of a table cap is the
cap itself and errs on an unmapped one, a move keeps the cap).
-/
import Fl4Proofs.P3.VsMdbInv
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Vs
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3

noncomputable section

/-- **A VSpace cap placed, weakened** (module docstring). -/
def VCapW (P L4 L3 L2 L1 : Set U64) : capability.Cap → Prop
  | .PageTable p mp a v => (mp = false → p ∈ L1) ∧ PaM p 4503599627366400#u64 ∧
      (mp = true → a ≠ 0#u64 ∧ v.bv &&& Fl4Spec.mask (Fl4Spec.ptTranslationBits + Fl4Spec.pageBits) = 0)
  | .PageDirectory p mp a _ => (mp = false → p ∈ L2) ∧ PaM p 4503599627366400#u64 ∧ (mp = true → a ≠ 0#u64)
  | .Pdpt p mp a _ => (mp = false → p ∈ L3) ∧ PaM p 4503599627366400#u64 ∧ (mp = true → a ≠ 0#u64)
  | c => VCapOK P L4 L3 L2 L1 c

/-- An unmapped page-table, page-directory or PDPT cap. -/
def TabUn : capability.Cap → Prop
  | .PageTable _ mp _ _ => mp = false
  | .PageDirectory _ mp _ _ => mp = false
  | .Pdpt _ mp _ _ => mp = false
  | _ => False

/-- **The weakened invariant for given ghost sets.** -/
def VsCapsW (P L4 L3 L2 L1 : Set U64) (mem : U64 → U64) (G : MdbGhost) : Prop :=
  ∀ x ∈ G.chains.flatten, VCapW P L4 L3 L2 L1 (capV mem x)

section
variable {P L4 L3 L2 L1 : Set U64}

/-- `VCapOK` is the strong form. -/
theorem VCapOK.toW {c : capability.Cap} (h : VCapOK P L4 L3 L2 L1 c) : VCapW P L4 L3 L2 L1 c := by
  cases c <;> simp only [VCapOK, VCapW] at h ⊢
  all_goals first
    | exact ⟨fun _ => h.1, h.2⟩
    | exact h

/-- **Back to `VCapOK`**: an unmapped table cap, or any cap but a mapped
table cap. -/
theorem VCapW.ok_of {c : capability.Cap} (h : VCapW P L4 L3 L2 L1 c)
    (hm : ∀ p a v, c ≠ .PageTable p true a v ∧ c ≠ .PageDirectory p true a v ∧ c ≠ .Pdpt p true a v) :
    VCapOK P L4 L3 L2 L1 c := by
  cases c with
  | PageTable p mp a v =>
    have := (hm p a v).1; simp only [VCapW] at h; simp only [VCapOK]
    cases mp
    · exact ⟨h.1 rfl, h.2⟩
    · exact absurd rfl this
  | PageDirectory p mp a v =>
    have := (hm p a v).2.1; simp only [VCapW] at h; simp only [VCapOK]
    cases mp
    · exact ⟨h.1 rfl, h.2⟩
    · exact absurd rfl this
  | Pdpt p mp a v =>
    have := (hm p a v).2.2; simp only [VCapW] at h; simp only [VCapOK]
    cases mp
    · exact ⟨h.1 rfl, h.2⟩
    · exact absurd rfl this
  | _ => exact h

/-- A mapped table cap's or an unmapped one's placement: the table in its set
when unmapped. -/
theorem VCapW.mono {P' L4' L3' L2' L1' : Set U64} (hP : P ⊆ P') (h4 : L4 ⊆ L4') (h3 : L3 ⊆ L3')
    (h2 : L2 ⊆ L2') (h1 : L1 ⊆ L1') {c : capability.Cap} (h : VCapW P L4 L3 L2 L1 c) :
    VCapW P' L4' L3' L2' L1' c := by
  cases c <;> simp only [VCapW] at h ⊢
  all_goals first
    | exact ⟨fun e => h1 (h.1 e), h.2⟩
    | exact ⟨fun e => h2 (h.1 e), h.2⟩
    | exact ⟨fun e => h3 (h.1 e), h.2⟩
    | exact VCapOK.mono hP h4 h3 h2 h1 h

/-- **The step lemma** (module docstring): `VCapOK` carried from `c0` to `c`
at every set, `c` an unmapped table cap only if `c0` is one. -/
theorem VCapW.transfer {c0 c : capability.Cap} (h : VCapW P L4 L3 L2 L1 c0)
    (hv : ∀ P L4 L3 L2 L1 : Set U64, VCapOK P L4 L3 L2 L1 c0 → VCapOK P L4 L3 L2 L1 c)
    (hu : TabUn c → TabUn c0) : VCapW P L4 L3 L2 L1 c := by
  -- the target's placement from `VCapOK` at sets differing from these in
  -- `L3`, `L2` or `L1` only, when the target is no unmapped table cap
  have back : ∀ L3' L2' L1' : Set U64, VCapOK P L4 L3' L2' L1' c → ¬ TabUn c → VCapW P L4 L3 L2 L1 c := by
    intro L3' L2' L1' hc hn
    cases c with
    | PageTable p mp a v =>
      cases mp
      · exact absurd rfl hn
      · exact ⟨fun e => absurd e (by decide), hc.2⟩
    | PageDirectory p mp a v =>
      cases mp
      · exact absurd rfl hn
      · exact ⟨fun e => absurd e (by decide), hc.2⟩
    | Pdpt p mp a v =>
      cases mp
      · exact absurd rfl hn
      · exact ⟨fun e => absurd e (by decide), hc.2⟩
    | _ => exact hc
  cases c0 with
  | PageTable p mp a v =>
    cases mp
    · exact (hv _ _ _ _ _ (VCapW.ok_of h fun _ _ _ => ⟨by simp, by simp, by simp⟩)).toW
    · exact back _ _ (insert p L1) (hv P L4 L3 L2 (insert p L1) ⟨Set.mem_insert _ _, h.2.1, fun _ => h.2.2 rfl⟩)
        fun ht => by have := hu ht; simp [TabUn] at this
  | PageDirectory p mp a v =>
    cases mp
    · exact (hv _ _ _ _ _ (VCapW.ok_of h fun _ _ _ => ⟨by simp, by simp, by simp⟩)).toW
    · exact back _ (insert p L2) _ (hv P L4 L3 (insert p L2) L1 ⟨Set.mem_insert _ _, h.2.1, fun _ => h.2.2 rfl⟩)
        fun ht => by have := hu ht; simp [TabUn] at this
  | Pdpt p mp a v =>
    cases mp
    · exact (hv _ _ _ _ _ (VCapW.ok_of h fun _ _ _ => ⟨by simp, by simp, by simp⟩)).toW
    · exact back (insert p L3) _ _ (hv P L4 (insert p L3) L2 L1 ⟨Set.mem_insert _ _, h.2.1, fun _ => h.2.2 rfl⟩)
        fun ht => by have := hu ht; simp [TabUn] at this
  | _ => exact (hv _ _ _ _ _ (VCapW.ok_of h fun _ _ _ => ⟨by simp, by simp, by simp⟩)).toW

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

/-- The invariant at a slot of the MDB. -/
theorem VsCapsW.at {th : TypedHeap} (h : VsCapsW P L4 L3 L2 L1 mem G) (hM : MdbLinks th mem G) {x : U64}
    (hx : IsSlot th x) {c : capability.Cap} (hc : capAt mem x = ok c) (hn : c ≠ .Null) :
    VCapW P L4 L3 L2 L1 c := by
  have := h x ((hM.members x).2 ⟨hx, c, hc, hn⟩)
  rwa [capV_of_capAt hc] at this

/-- The strong form at a slot for an unmapped table cap, or a PML4, pool or
frame cap (`VCapW.ok_of`). -/
theorem VsCapsW.atOK {th : TypedHeap} (h : VsCapsW P L4 L3 L2 L1 mem G) (hM : MdbLinks th mem G) {x : U64}
    (hx : IsSlot th x) {c : capability.Cap} (hc : capAt mem x = ok c) (hn : c ≠ .Null)
    (hm : ∀ p a v, c ≠ .PageTable p true a v ∧ c ≠ .PageDirectory p true a v ∧ c ≠ .Pdpt p true a v) :
    VCapOK P L4 L3 L2 L1 c :=
  (h.at hM hx hc hn).ok_of hm

end

end

end Fl4Proofs.P3.Vs
