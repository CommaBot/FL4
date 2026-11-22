/-
P3 (issue #16, F1 stage 4; KENTRY-PLAN f3): **the walk words read through the
relations** — the bridges from the VSpace refinements' spec-level posts to
VsNamedOps' word-level hypotheses.

The VSpace posts give `VsRel` / `PtRel` at the same sets before and after and
the spec's outcome, not FL4's words. A walk step and a present bit of a set
table's entry are fixed by its spec entry (`PML4ERel` / `PDPTERel` / `PDERel` /
`PTERel`: present bit, page-size bit and table target), a pool word and an
ASID-table word exactly (`optRef`). So:

* `e4_same` … `e1_same`: two words related to one spec entry step alike.
* `esame_of_kheap`, `pool_same_of_kheap`, `tbl_same_of_asid`: a set table /
  pool whose spec object is unchanged, an ASID table unchanged.
* **`wstep_keep`** (VsNamedOps' `hW` off the changed tables), **`unEmpty_keep`**
  (`hE`: an unmapped cap's table, empty before, stays so when its spec object
  is unchanged), `lvl_disj` (one object is a table of one level only).
* `e4_upd` / `e3_upd` / `e2_upd` / `pool_upd`: the other entries of a table
  with one spec entry written; `wstep4_tab` … : the written table entry's step.
* **`VsPath.of_find`**: a successful l4v `find_vspace_for_asid` is a level-4
  walk node at the ASID (the parent of a PDPT map; with `lookupPml4Slot`).
-/
import Fl4Proofs.P3.VsNamedOps
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Vs
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Classical

noncomputable section

/-! ## Entry words -/

theorem wstep_one (w : U64) : wstep 1 w = none := by unfold wstep; simp

theorem wstep_none_S {k : Nat} (hk : k = 3 ∨ k = 2) {w : U64} (h : eS w) : wstep k w = none := by
  cases h' : wstep k w with
  | none => rfl
  | some q => exact absurd h ((wstep32 hk).1 h').1.2

theorem eT_congr {w w' : U64} (h : (eA w).bv = (eA w').bv) : eT w = eT w' := by
  have : eA w = eA w' := (UScalar.eq_equiv_bv_eq _ _).mpr h
  unfold eT; rw [this]

/-- Two words related to one PML4 entry step alike. -/
theorem e4_same {L3 L3' : Set U64} {w w' : U64} {e : Fl4Spec.PML4E} (h : PML4ERel L3 w e)
    (h' : PML4ERel L3' w' e) : (eP w' ↔ eP w) ∧ wstep 4 w' = wstep 4 w := by
  cases e with
  | invalidPML4E =>
    exact ⟨⟨fun x => absurd x (show ¬ eP w' from h'), fun x => absurd x (show ¬ eP w from h)⟩, by
      rw [wstep_none (by decide) (show ¬ eP w from h), wstep_none (by decide) (show ¬ eP w' from h')]⟩
  | pdPointerTablePML4E tab _ _ =>
    obtain ⟨p, a, -⟩ := h
    obtain ⟨p', a', -⟩ := h'
    refine ⟨⟨fun _ => p, fun _ => p'⟩, ?_⟩
    rw [wstep4.2 ⟨p, rfl⟩, wstep4.2 ⟨p', rfl⟩, eT_congr (a'.trans a.symm)]

theorem e3_same {L2 L2' : Set U64} {w w' : U64} {e : Fl4Spec.PDPTE} (h : PDPTERel L2 w e)
    (h' : PDPTERel L2' w' e) : (eP w' ↔ eP w) ∧ wstep 3 w' = wstep 3 w := by
  cases e with
  | invalidPDPTE =>
    exact ⟨⟨fun x => absurd x (show ¬ eP w' from h'), fun x => absurd x (show ¬ eP w from h)⟩, by
      rw [wstep_none (by decide) (show ¬ eP w from h), wstep_none (by decide) (show ¬ eP w' from h')]⟩
  | pageDirectoryPDPTE tab _ _ =>
    obtain ⟨p, s, a, -⟩ := h
    obtain ⟨p', s', a', -⟩ := h'
    refine ⟨⟨fun _ => p, fun _ => p'⟩, ?_⟩
    rw [(wstep32 (.inl rfl)).2 ⟨⟨p, s⟩, rfl⟩, (wstep32 (.inl rfl)).2 ⟨⟨p', s'⟩, rfl⟩, eT_congr (a'.trans a.symm)]
  | hugePagePDPTE _ _ _ =>
    obtain ⟨p, s, -⟩ := h
    obtain ⟨p', s', -⟩ := h'
    exact ⟨⟨fun _ => p, fun _ => p'⟩, by rw [wstep_none_S (.inl rfl) s, wstep_none_S (.inl rfl) s']⟩

theorem e2_same {L1 L1' : Set U64} {w w' : U64} {e : Fl4Spec.PDE} (h : PDERel L1 w e)
    (h' : PDERel L1' w' e) : (eP w' ↔ eP w) ∧ wstep 2 w' = wstep 2 w := by
  cases e with
  | invalidPDE =>
    exact ⟨⟨fun x => absurd x (show ¬ eP w' from h'), fun x => absurd x (show ¬ eP w from h)⟩, by
      rw [wstep_none (by decide) (show ¬ eP w from h), wstep_none (by decide) (show ¬ eP w' from h')]⟩
  | pageTablePDE tab _ _ =>
    obtain ⟨p, s, a, -⟩ := h
    obtain ⟨p', s', a', -⟩ := h'
    refine ⟨⟨fun _ => p, fun _ => p'⟩, ?_⟩
    rw [(wstep32 (.inr rfl)).2 ⟨⟨p, s⟩, rfl⟩, (wstep32 (.inr rfl)).2 ⟨⟨p', s'⟩, rfl⟩, eT_congr (a'.trans a.symm)]
  | largePagePDE _ _ _ =>
    obtain ⟨p, s, -⟩ := h
    obtain ⟨p', s', -⟩ := h'
    exact ⟨⟨fun _ => p, fun _ => p'⟩, by rw [wstep_none_S (.inr rfl) s, wstep_none_S (.inr rfl) s']⟩

theorem e1_same {w w' : U64} {e : Fl4Spec.PTE} (h : PTERel w e) (h' : PTERel w' e) :
    (eP w' ↔ eP w) ∧ wstep 1 w' = wstep 1 w := by
  refine ⟨?_, by rw [wstep_one, wstep_one]⟩
  cases e with
  | invalidPTE => exact ⟨fun x => absurd x (show ¬ eP w' from h'), fun x => absurd x (show ¬ eP w from h)⟩
  | smallPagePTE _ _ _ => exact ⟨fun _ => h.1, fun _ => h'.1⟩

theorem un_lvl {c : capability.Cap} {k : Nat} {q : U64} (hu : TabUn c) (hk : VKey c = some (k, q)) :
    1 ≤ k ∧ k ≤ 4 := by
  cases c <;> simp only [TabUn, VKey, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at hu hk
  all_goals first | exact hu.elim | (obtain ⟨rfl, -⟩ := hk; decide)

/-! ## Frames from the spec -/

section Fr
variable {P P' L4 L3 L2 L1 : Set U64} {m m' : U64 → U64} {ksb : U64} {σ σ' : Fl4Spec.State Unit}
  (hR : VsRel P m ksb σ) (hPt : PtRel L4 L3 L2 L1 m σ)
  (hR' : VsRel P' m' ksb σ') (hPt' : PtRel L4 L3 L2 L1 m' σ')

include hPt hPt' in
/-- **A set table whose spec object is unchanged steps alike.** -/
theorem esame_of_kheap {k : Nat} (hk1 : 1 ≤ k) (hk4 : k ≤ 4) {q : U64} (hq : q ∈ lvlSet P L4 L3 L2 L1 k)
    (hk : σ'.kheap q.bv = σ.kheap q.bv) {i : U64} (hi : i.val < bnd k) :
    (eP (m' (peA q i)) ↔ eP (m (peA q i))) ∧ wstep k (m' (peA q i)) = wstep k (m (peA q i)) := by
  obtain rfl | rfl | rfl | rfl : k = 4 ∨ k = 3 ∨ k = 2 ∨ k = 1 := by omega
  · obtain ⟨f, hf, hr⟩ := hPt.l4 q hq
    obtain ⟨f', hf', hr'⟩ := hPt'.l4 q hq
    rw [hk, hf] at hf'; cases hf'
    have hi' : i.val < 256 := by simpa [bnd] using hi
    exact e4_same (hr i hi') (hr' i hi')
  · obtain ⟨f, hf, hr⟩ := hPt.l3 q hq
    obtain ⟨f', hf', hr'⟩ := hPt'.l3 q hq
    rw [hk, hf] at hf'; cases hf'
    have hi' : i.val < 512 := by simpa [bnd] using hi
    exact e3_same (hr i hi') (hr' i hi')
  · obtain ⟨f, hf, hr⟩ := hPt.l2 q hq
    obtain ⟨f', hf', hr'⟩ := hPt'.l2 q hq
    rw [hk, hf] at hf'; cases hf'
    have hi' : i.val < 512 := by simpa [bnd] using hi
    exact e2_same (hr i hi') (hr' i hi')
  · obtain ⟨f, hf, hr⟩ := hPt.l1 q hq
    obtain ⟨f', hf', hr'⟩ := hPt'.l1 q hq
    rw [hk, hf] at hf'; cases hf'
    have hi' : i.val < 512 := by simpa [bnd] using hi
    exact e1_same (hr i hi') (hr' i hi')

include hR hR' in
/-- A pool whose spec object is unchanged keeps its words. -/
theorem pool_same_of_kheap {q : U64} (hq : q ∈ P) (hq' : q ∈ P') (hk : σ'.kheap q.bv = σ.kheap q.bv) {i : U64}
    (hi : i.val < 512) : m' (peA q i) = m (peA q i) := by
  obtain ⟨f, hf, hr⟩ := hR.pool q hq
  obtain ⟨f', hf', hr'⟩ := hR'.pool q hq'
  rw [hk, hf] at hf'; cases hf'
  exact optRef_inj ((hr' i hi).symm.trans (hr i hi))

include hR hR' in
/-- An unchanged ASID table keeps its words. -/
theorem tbl_same_of_asid (h : σ'.archState.x64AsidTable = σ.archState.x64AsidTable) : TblSame ksb m m' :=
  fun hi hh => optRef_inj ((hR'.table hi hh).symm.trans (by rw [h]; exact hR.table hi hh))

include hR hPt in
/-- **One object is a table / pool of one level only** (the spec's kinds). -/
theorem lvl_disj {k k' : Nat} (hk : 1 ≤ k ∧ k ≤ 5) (hk' : 1 ≤ k' ∧ k' ≤ 5) {q : U64}
    (h : q ∈ lvlSet P L4 L3 L2 L1 k) (h' : q ∈ lvlSet P L4 L3 L2 L1 k') : k = k' := by
  have kind : ∀ j, 1 ≤ j ∧ j ≤ 5 → q ∈ lvlSet P L4 L3 L2 L1 j →
      ∃ ao, σ.kheap q.bv = some (.archObj ao) ∧ (j = 5 ↔ ∃ f, ao = .asidPool f) ∧
        (j = 4 ↔ ∃ f, ao = .pageMapL4 f) ∧ (j = 3 ↔ ∃ f, ao = .pdPointerTable f) ∧
        (j = 2 ↔ ∃ f, ao = .pageDirectory f) := by
    intro j hj hq
    obtain ⟨hj1, hj2⟩ := hj
    obtain rfl | rfl | rfl | rfl | rfl : j = 5 ∨ j = 4 ∨ j = 3 ∨ j = 2 ∨ j = 1 := by omega
    · obtain ⟨f, hf, -⟩ := hR.pool q hq; exact ⟨_, hf, by simp, by simp, by simp, by simp⟩
    · obtain ⟨f, hf, -⟩ := hPt.l4 q hq; exact ⟨_, hf, by simp, by simp, by simp, by simp⟩
    · obtain ⟨f, hf, -⟩ := hPt.l3 q hq; exact ⟨_, hf, by simp, by simp, by simp, by simp⟩
    · obtain ⟨f, hf, -⟩ := hPt.l2 q hq; exact ⟨_, hf, by simp, by simp, by simp, by simp⟩
    · obtain ⟨f, hf, -⟩ := hPt.l1 q hq; exact ⟨_, hf, by simp, by simp, by simp, by simp⟩
  obtain ⟨ao, ha, a5, a4, a3, a2⟩ := kind k hk h
  obtain ⟨ao', ha', b5, b4, b3, b2⟩ := kind k' hk' h'
  obtain ⟨hk1, hk2⟩ := hk
  obtain ⟨hk1', hk2'⟩ := hk'
  rw [ha] at ha'; cases ha'
  by_cases e5 : k = 5
  · exact e5.trans (b5.2 (a5.1 e5)).symm
  by_cases e4 : k = 4
  · exact e4.trans (b4.2 (a4.1 e4)).symm
  by_cases e3 : k = 3
  · exact e3.trans (b3.2 (a3.1 e3)).symm
  by_cases e2 : k = 2
  · exact e2.trans (b2.2 (a2.1 e2)).symm
  have : k' ≠ 5 := fun e => e5 (a5.2 (b5.1 e))
  have : k' ≠ 4 := fun e => e4 (a4.2 (b4.1 e))
  have : k' ≠ 3 := fun e => e3 (a3.2 (b3.1 e))
  have : k' ≠ 2 := fun e => e2 (a2.2 (b2.1 e))
  omega

include hR hPt hR' hPt' in
/-- **VsNamedOps' `hW` off the changed tables**: a walk node whose spec object
is unchanged steps alike after. -/
theorem wstep_keep (hPI : PoolsIn P L4 m) (hPP : ∀ q ∈ P, q ∈ P') {X : U64 → Prop}
    (hk : ∀ q, (q ∈ P ∨ q ∈ L4 ∨ q ∈ L3 ∨ q ∈ L2 ∨ q ∈ L1) → ¬ X q → σ'.kheap q.bv = σ.kheap q.bv) :
    ∀ (k : Nat) (p : U64) (a v : Nat) (i : U64), VsPath m ksb k p a v → 2 ≤ k → k ≤ 5 → i.val < bnd k →
      ¬ X p → wstep k (m' (peA p i)) = wstep k (m (peA p i)) := by
  intro k p a v i hp h2 h5 hi hx
  have hm := hp.mem hR hPt hPI
  have hko := hk p (lvl_mem hm) hx
  by_cases e5 : k = 5
  · subst e5
    rw [pool_same_of_kheap hR hR' hm (hPP _ hm) hko (by simpa [bnd] using hi)]
  · exact (esame_of_kheap hPt hPt' (by omega) (by omega) hm hko hi).2

include hPt hPt' in
/-- **VsNamedOps' `hE` off the changed tables**: an unmapped cap's table,
empty before, stays empty when its spec object is unchanged. -/
theorem unEmpty_keep {th : TypedHeap} (hN : VsNamed th m ksb) (hS : VsSlotsW th P L4 L3 L2 L1 m)
    {X : U64 → Prop} (hk : ∀ q, (q ∈ L4 ∨ q ∈ L3 ∨ q ∈ L2 ∨ q ∈ L1) → ¬ X q → σ'.kheap q.bv = σ.kheap q.bv) :
    ∀ y, IsSlot th y → TabUn (capV m y) → ∀ k q, VKey (capV m y) = some (k, q) → ¬ X q →
      ∀ i : U64, i.val < bnd k → ¬ eP (m' (peA q i)) := by
  intro y hy hu k q hkey hx i hi
  have hq := hS.need hy (vneed_of_un hu hkey)
  have hk14 : 1 ≤ k ∧ k ≤ 4 := un_lvl hu hkey
  have hq' : q ∈ L4 ∨ q ∈ L3 ∨ q ∈ L2 ∨ q ∈ L1 := by
    obtain ⟨a, b⟩ := hk14
    obtain rfl | rfl | rfl | rfl : k = 4 ∨ k = 3 ∨ k = 2 ∨ k = 1 := by omega
    · exact .inl hq
    · exact .inr (.inl hq)
    · exact .inr (.inr (.inl hq))
    · exact .inr (.inr (.inr hq))
  rw [(esame_of_kheap hPt hPt' hk14.1 hk14.2 hq (hk q hq' hx) hi).1]
  exact hN.empty y hy hu k q hkey i hi

end Fr

/-! ## One spec entry written -/

section Upd
variable {L4 L3 L2 L1 : Set U64} {m m' : U64 → U64} {σ σ' : Fl4Spec.State Unit}
  (hPt : PtRel L4 L3 L2 L1 m σ) (hPt' : PtRel L4 L3 L2 L1 m' σ')

include hPt hPt' in
/-- The other entries of a PML4 with entry `j` written step alike. -/
theorem e4_upd {p : U64} (hp : p ∈ L4) {f : BitVec 9 → Fl4Spec.PML4E} {j : U64} {e : Fl4Spec.PML4E}
    (hj : j.val < 512) (hk : σ.kheap p.bv = some (.archObj (.pageMapL4 f)))
    (hk' : σ'.kheap p.bv = some (.archObj (.pageMapL4 (Function.update f (Fl4Spec.ucast 9 j.bv) e))))
    {i : U64} (hi : i.val < 256) (hij : i ≠ j) :
    (eP (m' (peA p i)) ↔ eP (m (peA p i))) ∧ wstep 4 (m' (peA p i)) = wstep 4 (m (peA p i)) := by
  obtain ⟨g, hg, hr⟩ := hPt.l4 p hp
  obtain ⟨g', hg', hr'⟩ := hPt'.l4 p hp
  rw [hk] at hg; cases hg
  rw [hk'] at hg'; cases hg'
  have h := hr' i hi
  rw [Function.update_of_ne (fun h => hij (ucast9_inj (by omega) hj h))] at h
  exact e4_same (hr i hi) h

include hPt hPt' in
theorem e3_upd {p : U64} (hp : p ∈ L3) {f : BitVec 9 → Fl4Spec.PDPTE} {j : U64} {e : Fl4Spec.PDPTE}
    (hj : j.val < 512) (hk : σ.kheap p.bv = some (.archObj (.pdPointerTable f)))
    (hk' : σ'.kheap p.bv = some (.archObj (.pdPointerTable (Function.update f (Fl4Spec.ucast 9 j.bv) e))))
    {i : U64} (hi : i.val < 512) (hij : i ≠ j) :
    (eP (m' (peA p i)) ↔ eP (m (peA p i))) ∧ wstep 3 (m' (peA p i)) = wstep 3 (m (peA p i)) := by
  obtain ⟨g, hg, hr⟩ := hPt.l3 p hp
  obtain ⟨g', hg', hr'⟩ := hPt'.l3 p hp
  rw [hk] at hg; cases hg
  rw [hk'] at hg'; cases hg'
  have h := hr' i hi
  rw [Function.update_of_ne (fun h => hij (ucast9_inj hi hj h))] at h
  exact e3_same (hr i hi) h

include hPt hPt' in
theorem e2_upd {p : U64} (hp : p ∈ L2) {f : BitVec 9 → Fl4Spec.PDE} {j : U64} {e : Fl4Spec.PDE}
    (hj : j.val < 512) (hk : σ.kheap p.bv = some (.archObj (.pageDirectory f)))
    (hk' : σ'.kheap p.bv = some (.archObj (.pageDirectory (Function.update f (Fl4Spec.ucast 9 j.bv) e))))
    {i : U64} (hi : i.val < 512) (hij : i ≠ j) :
    (eP (m' (peA p i)) ↔ eP (m (peA p i))) ∧ wstep 2 (m' (peA p i)) = wstep 2 (m (peA p i)) := by
  obtain ⟨g, hg, hr⟩ := hPt.l2 p hp
  obtain ⟨g', hg', hr'⟩ := hPt'.l2 p hp
  rw [hk] at hg; cases hg
  rw [hk'] at hg'; cases hg'
  have h := hr' i hi
  rw [Function.update_of_ne (fun h => hij (ucast9_inj hi hj h))] at h
  exact e2_same (hr i hi) h

include hPt' in
/-- **The written PML4 entry's step**: a table entry steps to its table. -/
theorem wstep4_tab {p : U64} (hp : p ∈ L4) {f : BitVec 9 → Fl4Spec.PML4E} {j : U64} (hj : j.val < 256)
    (hk' : σ'.kheap p.bv = some (.archObj (.pageMapL4 f))) {tab : Fl4Spec.ObjRef} {a r : _} (he : f (Fl4Spec.ucast 9 j.bv) = .pdPointerTablePML4E tab a r) {q : U64}
    (hq : ∀ w, (eA w).bv = tab → eT w = q) : wstep 4 (m' (peA p j)) = some q := by
  obtain ⟨g, hg, hr⟩ := hPt'.l4 p hp
  rw [hk'] at hg; cases hg
  have h := hr j hj
  rw [he] at h
  obtain ⟨hpr, ha, -⟩ := h
  exact wstep4.2 ⟨hpr, hq _ ha⟩

include hPt' in
theorem wstep3_tab {p : U64} (hp : p ∈ L3) {f : BitVec 9 → Fl4Spec.PDPTE} {j : U64} (hj : j.val < 512)
    (hk' : σ'.kheap p.bv = some (.archObj (.pdPointerTable f))) {tab : Fl4Spec.ObjRef} {a r : _} (he : f (Fl4Spec.ucast 9 j.bv) = .pageDirectoryPDPTE tab a r) {q : U64}
    (hq : ∀ w, (eA w).bv = tab → eT w = q) : wstep 3 (m' (peA p j)) = some q := by
  obtain ⟨g, hg, hr⟩ := hPt'.l3 p hp
  rw [hk'] at hg; cases hg
  have h := hr j hj
  rw [he] at h
  obtain ⟨hpr, hs, ha, -⟩ := h
  exact (wstep32 (.inl rfl)).2 ⟨⟨hpr, hs⟩, hq _ ha⟩

include hPt' in
theorem wstep2_tab {p : U64} (hp : p ∈ L2) {f : BitVec 9 → Fl4Spec.PDE} {j : U64} (hj : j.val < 512)
    (hk' : σ'.kheap p.bv = some (.archObj (.pageDirectory f))) {tab : Fl4Spec.ObjRef} {a r : _} (he : f (Fl4Spec.ucast 9 j.bv) = .pageTablePDE tab a r) {q : U64}
    (hq : ∀ w, (eA w).bv = tab → eT w = q) : wstep 2 (m' (peA p j)) = some q := by
  obtain ⟨g, hg, hr⟩ := hPt'.l2 p hp
  rw [hk'] at hg; cases hg
  have h := hr j hj
  rw [he] at h
  obtain ⟨hpr, hs, ha, -⟩ := h
  exact (wstep32 (.inr rfl)).2 ⟨⟨hpr, hs⟩, hq _ ha⟩

end Upd

/-! ## The ASID lookup as a walk -/

theorem and_val (x : U64) (k : Nat) (K : U64) (hK : K.val = 2 ^ k - 1) : (x &&& K).val = x.val % 2 ^ k := by
  show (x &&& K).bv.toNat = _
  rw [UScalar.bv_and, BitVec.toNat_and, show K.bv.toNat = 2 ^ k - 1 from hK, Nat.and_two_pow_sub_one_eq_mod]; rfl

/-- **A successful l4v `find_vspace_for_asid` is a level-4 walk node at the
ASID** (as `mem_L4_of_find`). -/
theorem VsPath.of_find {P : Set U64} {m : U64 → U64} {ksb : U64} {σ : Fl4Spec.State Unit}
    (hR : VsRel P m ksb σ) {asid p : U64} (h0 : asid ≠ 0#u64) (h20 : asid.val < 2 ^ 20)
    (hf : ExceptT.run (Fl4Spec.findVspaceForAsid (Z := Unit) asid.bv) σ = ({(.ok p.bv, σ)}, False)) :
    VsPath m ksb 4 p asid.val 0 := by
  have key : ∀ {a b : Except Fl4Spec.LookupFailure Fl4Spec.ObjRef},
      ((({(a, σ)} : Set _), False) : Set (Except Fl4Spec.LookupFailure Fl4Spec.ObjRef × Fl4Spec.State Unit) × Prop) =
        ({(b, σ)}, False) → a = b :=
    fun h => congrArg Prod.fst (Set.singleton_eq_singleton_iff.mp (congrArg Prod.fst h))
  have hpos : asid.bv > 0 := by
    have : asid.val ≠ 0 := fun h => h0 (UScalar.eq_of_val_eq (by simpa using h))
    show 0 < asid.bv.toNat
    exact Nat.pos_of_ne_zero this
  obtain ⟨i, hiv⟩ : ∃ i : U64, i.val = asid.val >>> 9 := by
    refine ⟨⟨BitVec.ofNat 64 (asid.val >>> 9)⟩, ?_⟩
    show (BitVec.ofNat 64 (asid.val >>> 9)).toNat = _
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.shiftRight_le _ _) asid.bv.isLt)
  have hlt := and_lt i 11 2047#u64 rfl (by decide)
  have htab := hR.table _ hlt
  rw [hi_bv asid i hiv] at htab
  by_cases hp : m (atA ksb (i &&& 2047#u64)) = 0#u64
  · rw [hp, optRef_eq_none.mpr rfl] at htab
    rw [findVspaceForAsid_none hpos htab] at hf
    cases key hf
  · have hq := hR.tmem _ hlt hp
    obtain ⟨f, hkf, hfp⟩ := hR.pool _ hq
    rw [Notif.optRef, if_neg hp] at htab
    have hsp := findVspaceForAsid_some hpos htab hkf
    have hlo := and_lt asid 9 511#u64 rfl (by decide)
    have hfe := hfp _ hlo
    rw [lo_bv] at hfe
    rw [hsp, hfe, nativeAsidRoot_optRef] at hf
    have he := key hf
    have hT := VsPath.tbl (m := m) (ksb := ksb) hlt hp
    have hv1 : (i &&& 2047#u64).val = i.val % 2 ^ 11 := and_val i 11 2047#u64 rfl
    have hv2 : (asid &&& 511#u64).val = asid.val % 2 ^ 9 := and_val asid 9 511#u64 rfl
    have hasid : (i &&& 2047#u64).val * 512 + (asid &&& 511#u64).val = asid.val := by
      rw [hv1, hv2, hiv, Nat.shiftRight_eq_div_pow]
      have : asid.val / 2 ^ 9 < 2 ^ 11 := by omega
      rw [Nat.mod_eq_of_lt this]
      omega
    generalize hw : m (peA (m (atA ksb (i &&& 2047#u64))) (asid &&& 511#u64)) = w at he
    unfold nativeRef at he
    by_cases ht : w &&& 1#u64 = 0#u64
    · rw [if_pos ht] at he
      by_cases hw0 : w = 0#u64
      · rw [Notif.optRef, if_pos hw0] at he; cases he
      · rw [Notif.optRef, if_neg hw0] at he
        have hb : w.bv = p.bv := Except.ok.inj he
        have hwp : w = p := (UScalar.eq_equiv_bv_eq _ _).mpr hb
        subst hwp
        have := VsPath.pool hT hlo (by rw [hw]; exact hw0) (by rw [hw]; exact ht)
        rw [hw, hasid] at this
        exact this
    · rw [if_neg ht] at he; cases he

end

end Fl4Proofs.P3.Vs
