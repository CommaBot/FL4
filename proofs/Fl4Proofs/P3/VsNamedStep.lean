/-
P3 (issue #16, F1 stage 4; KENTRY-PLAN f3): **`VsNamed` across each VSpace
operation, in the spec's terms** (VsNamedOps' generic lemmas with their word
hypotheses discharged through the relations before and after, VsNamedSpec).

Each lemma takes `VsNamed`, `VsSlotsW` and the relations at the pre-state, the
relations after at the same table sets, the invoked slot's cap before and after
(FL4), the other keyed caps kept, and the spec's change: the arch objects of
the sets unchanged except the one written, the ASID table unchanged (or, for
MakePool, written at one free index). These are what the decode (the checks
l4v makes: unmapped cap, `find_vspace_for_asid`, the old entry invalid) and
the perform (`storePml4e` …) of each refinement give; the lemmas do not unfold
the decode (KENTRY-PLAN f3 (0): the J-layer post must keep it).

* **`VsNamed.mapTabS`** (any level) and **`pdptMapS`**, **`pdMapS`**,
  **`ptMapS`**, **`assignS`** (ASID assign: the pool entry).
* **`VsNamed.makePoolS`**.
* **`VsNamed.leafS`**: the frame class (frame map / remap / unmap, PML4 flush):
  the tables written are walk nodes whose steps are kept (a PT, or large / huge
  page entries).
* Table Unmap / finalise / `emptySlot`: VsNamedOps' `unmapTab` / `delSlot`
  with **`VsNamed.own`** (a final cap's table is walked only at its ref) and
  **`VsNamed.gone`** (no walk to it once the step at its ref is cleared), and
  `wstep4_inv` … (a cleared spec entry is no step).
-/
import Fl4Proofs.P3.VsNamedSpec
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Vs
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Classical

noncomputable section

theorem ucast11_inj {a b : U64} (ha : a.val < 2 ^ 11) (hb : b.val < 2 ^ 11)
    (h : (Fl4Spec.ucast 11 a.bv : BitVec 11) = Fl4Spec.ucast 11 b.bv) : a = b := by
  apply UScalar.eq_of_val_eq
  have := congrArg BitVec.toNat h
  simp only [Fl4Spec.ucast, BitVec.toNat_setWidth] at this
  show a.bv.toNat = b.bv.toNat
  have e1 : a.bv.toNat % 2 ^ 11 = a.bv.toNat := Nat.mod_eq_of_lt (by show a.val < _; omega)
  have e2 : b.bv.toNat % 2 ^ 11 = b.bv.toNat := Nat.mod_eq_of_lt (by show b.val < _; omega)
  omega

theorem optRef_some {w : U64} (h : w ≠ 0#u64) : Notif.optRef w = some w.bv := by
  rw [Notif.optRef, if_neg h]

theorem VsPath.lvl' {m : U64 → U64} {ksb : U64} {k : Nat} {q : U64} {a v : Nat} (h : VsPath m ksb k q a v) :
    1 ≤ k ∧ k ≤ 5 := by
  cases h <;> decide

section
variable {th : TypedHeap} {P L4 L3 L2 L1 : Set U64} {m m' : U64 → U64} {ksb : U64} {σ σ' : Fl4Spec.State Unit}

/-! ## Table maps and ASID assign -/

/-- **(F1 stage 4) A table map / ASID assign, spec form**: the parent `p0`'s
other entries step alike, every other set object unchanged in the spec, the
ASID table unchanged. -/
theorem VsNamed.mapTabS (hN : VsNamed th m ksb) (hS : VsSlotsW th P L4 L3 L2 L1 m)
    (hR : VsRel P m ksb σ) (hPt : PtRel L4 L3 L2 L1 m σ) (hPI : PoolsIn P L4 m)
    (hR' : VsRel P m' ksb σ') (hPt' : PtRel L4 L3 L2 L1 m' σ')
    {y0 : U64} (hy0 : IsSlot th y0) {k0 : Nat} {q0 : U64} {a0 v0 : Nat} (hk1 : 1 ≤ k0) (hk4 : k0 ≤ 4)
    (hu0 : TabUn (capV m y0)) (hkey0 : VKey (capV m y0) = some (k0, q0))
    (hkey1 : VKey (capV m' y0) = some (k0, q0)) (hr1 : VRefOf (capV m' y0) = some (true, a0, v0))
    (hK : ∀ y, IsSlot th y → y ≠ y0 → (VKey (capV m y) ≠ none ∨ VKey (capV m' y) ≠ none) → capV m' y = capV m y)
    {p0 i0 : U64} {a1 v1 : Nat} (hp0 : VsPath m ksb (k0 + 1) p0 a1 v1) (hi0 : i0.val < bnd (k0 + 1))
    (hw0 : wstep (k0 + 1) (m' (peA p0 i0)) = some q0) (hr0 : rstep (k0 + 1) a1 v1 i0.val = (a0, v0))
    (hPo : ∀ i : U64, i.val < bnd (k0 + 1) → i ≠ i0 →
      wstep (k0 + 1) (m' (peA p0 i)) = wstep (k0 + 1) (m (peA p0 i)))
    (hko : ∀ q, (q ∈ P ∨ q ∈ L4 ∨ q ∈ L3 ∨ q ∈ L2 ∨ q ∈ L1) → q ≠ p0 → σ'.kheap q.bv = σ.kheap q.bv)
    (hat : σ'.archState.x64AsidTable = σ.archState.x64AsidTable) :
    VsNamed th m' ksb := by
  have hp0m := hp0.mem hR hPt hPI
  refine hN.mapTab hS hy0 hk1 hk4 hu0 hkey0 hkey1 hr1 hK hp0 hi0 hw0 hr0 (tbl_same_of_asid hR hR' hat) ?_ ?_
  · intro k p a v i hp h2 h5 hi hne
    by_cases e : p = p0
    · subst e
      have hkk : k = k0 + 1 := lvl_disj hR hPt ⟨by omega, h5⟩ ⟨by omega, by omega⟩ (hp.mem hR hPt hPI) hp0m
      subst hkk
      exact hPo i hi (fun hi' => hne ⟨rfl, rfl, hi'⟩)
    · exact wstep_keep hR hPt hR' hPt' hPI (fun q hq => hq) (X := (· = p0)) hko k p a v i hp h2 h5 hi e
  · intro y hy hu k q hk i hi
    by_cases e : q = p0
    · subst e
      exfalso
      have hq := hS.need hy (vneed_of_un hu hk)
      have hl := un_lvl hu hk
      have hkk : k = k0 + 1 := lvl_disj hR hPt ⟨hl.1, by omega⟩ ⟨by omega, by omega⟩ hq hp0m
      subst hkk
      exact hN.unNotWalk hy hu hk hp0
    · exact unEmpty_keep hPt hPt' hN hS (X := (· = p0)) (fun q hq hx => hko q (.inr hq) hx) y hy hu k q hk e i hi

/-- **(F1 stage 4) PDPT Map** (`performPdptInvocation (.pdptMap …)`): the PML4
`pm` the ASID lookup finds (`VsPath.of_find`) gets entry `j` (`va`'s index)
written with the PDPT `q0`. -/
theorem VsNamed.pdptMapS (hN : VsNamed th m ksb) (hS : VsSlotsW th P L4 L3 L2 L1 m)
    (hR : VsRel P m ksb σ) (hPt : PtRel L4 L3 L2 L1 m σ) (hPI : PoolsIn P L4 m)
    (hR' : VsRel P m' ksb σ') (hPt' : PtRel L4 L3 L2 L1 m' σ')
    {y0 : U64} (hy0 : IsSlot th y0) {q0 as0 va0 asid va : U64}
    (hc0 : capV m y0 = .Pdpt q0 false as0 va0) (hc1 : capV m' y0 = .Pdpt q0 true asid va)
    (hK : ∀ y, IsSlot th y → y ≠ y0 → (VKey (capV m y) ≠ none ∨ VKey (capV m' y) ≠ none) → capV m' y = capV m y)
    {pm j : U64} (hpm : VsPath m ksb 4 pm asid.val 0) (hj : j.val < 256) (hva : va.val = j.val * 2 ^ 39)
    {f : BitVec 9 → Fl4Spec.PML4E} (hk : σ.kheap pm.bv = some (.archObj (.pageMapL4 f)))
    {tab : Fl4Spec.ObjRef} {ta : _} {tr : _}
    (hk' : σ'.kheap pm.bv = some (.archObj (.pageMapL4
      (Function.update f (Fl4Spec.ucast 9 j.bv) (.pdPointerTablePML4E tab ta tr)))))
    (htab : ∀ w, (eA w).bv = tab → eT w = q0)
    (hko : ∀ q, (q ∈ P ∨ q ∈ L4 ∨ q ∈ L3 ∨ q ∈ L2 ∨ q ∈ L1) → q ≠ pm → σ'.kheap q.bv = σ.kheap q.bv)
    (hat : σ'.archState.x64AsidTable = σ.archState.x64AsidTable) :
    VsNamed th m' ksb := by
  have hpmL : pm ∈ L4 := hpm.mem hR hPt hPI
  refine hN.mapTabS hS hR hPt hPI hR' hPt' hy0 (k0 := 3) (a0 := asid.val) (v0 := va.val) (by omega) (by omega)
    (by rw [hc0]; try exact rfl) (by rw [hc0]; try exact rfl) (by rw [hc1]; try exact rfl) (by rw [hc1]; try exact rfl) hK hpm (by simpa [bnd] using hj)
    ?_ ?_ ?_ hko hat
  · exact wstep4_tab hPt' hpmL hj hk' (a := ta) (r := tr) (by simp) htab
  · simp [rstep, hva]
  · intro i hi hij
    exact (e4_upd hPt hPt' hpmL (by omega) hk hk' (by simpa [bnd] using hi) hij).2

/-- **(F1 stage 4) PD Map**: the PDPT `pd` (a level-3 walk node at the ASID
and `va`'s PML4 prefix) gets entry `j` written with the PD `q0`. -/
theorem VsNamed.pdMapS (hN : VsNamed th m ksb) (hS : VsSlotsW th P L4 L3 L2 L1 m)
    (hR : VsRel P m ksb σ) (hPt : PtRel L4 L3 L2 L1 m σ) (hPI : PoolsIn P L4 m)
    (hR' : VsRel P m' ksb σ') (hPt' : PtRel L4 L3 L2 L1 m' σ')
    {y0 : U64} (hy0 : IsSlot th y0) {q0 as0 va0 asid va : U64}
    (hc0 : capV m y0 = .PageDirectory q0 false as0 va0) (hc1 : capV m' y0 = .PageDirectory q0 true asid va)
    (hK : ∀ y, IsSlot th y → y ≠ y0 → (VKey (capV m y) ≠ none ∨ VKey (capV m' y) ≠ none) → capV m' y = capV m y)
    {pd j : U64} {v1 : Nat} (hpd : VsPath m ksb 3 pd asid.val v1) (hj : j.val < 512)
    (hva : va.val = v1 + j.val * 2 ^ 30)
    {f : BitVec 9 → Fl4Spec.PDPTE} (hk : σ.kheap pd.bv = some (.archObj (.pdPointerTable f)))
    {tab : Fl4Spec.ObjRef} {ta : _} {tr : _}
    (hk' : σ'.kheap pd.bv = some (.archObj (.pdPointerTable
      (Function.update f (Fl4Spec.ucast 9 j.bv) (.pageDirectoryPDPTE tab ta tr)))))
    (htab : ∀ w, (eA w).bv = tab → eT w = q0)
    (hko : ∀ q, (q ∈ P ∨ q ∈ L4 ∨ q ∈ L3 ∨ q ∈ L2 ∨ q ∈ L1) → q ≠ pd → σ'.kheap q.bv = σ.kheap q.bv)
    (hat : σ'.archState.x64AsidTable = σ.archState.x64AsidTable) :
    VsNamed th m' ksb := by
  have hpdL : pd ∈ L3 := hpd.mem hR hPt hPI
  refine hN.mapTabS hS hR hPt hPI hR' hPt' hy0 (k0 := 2) (a0 := asid.val) (v0 := va.val) (by omega) (by omega)
    (by rw [hc0]; try exact rfl) (by rw [hc0]; try exact rfl) (by rw [hc1]; try exact rfl) (by rw [hc1]; try exact rfl) hK hpd (by simpa [bnd] using hj)
    ?_ ?_ ?_ hko hat
  · exact wstep3_tab hPt' hpdL hj hk' (a := ta) (r := tr) (by simp) htab
  · simp [rstep, hva]
  · intro i hi hij
    exact (e3_upd hPt hPt' hpdL hj hk hk' (by simpa [bnd] using hi) hij).2

/-- **(F1 stage 4) PT Map**: the PD `pd` (a level-2 walk node) gets entry `j`
written with the PT `q0`. -/
theorem VsNamed.ptMapS (hN : VsNamed th m ksb) (hS : VsSlotsW th P L4 L3 L2 L1 m)
    (hR : VsRel P m ksb σ) (hPt : PtRel L4 L3 L2 L1 m σ) (hPI : PoolsIn P L4 m)
    (hR' : VsRel P m' ksb σ') (hPt' : PtRel L4 L3 L2 L1 m' σ')
    {y0 : U64} (hy0 : IsSlot th y0) {q0 as0 va0 asid va : U64}
    (hc0 : capV m y0 = .PageTable q0 false as0 va0) (hc1 : capV m' y0 = .PageTable q0 true asid va)
    (hK : ∀ y, IsSlot th y → y ≠ y0 → (VKey (capV m y) ≠ none ∨ VKey (capV m' y) ≠ none) → capV m' y = capV m y)
    {pd j : U64} {v1 : Nat} (hpd : VsPath m ksb 2 pd asid.val v1) (hj : j.val < 512)
    (hva : va.val = v1 + j.val * 2 ^ 21)
    {f : BitVec 9 → Fl4Spec.PDE} (hk : σ.kheap pd.bv = some (.archObj (.pageDirectory f)))
    {tab : Fl4Spec.ObjRef} {ta : _} {tr : _}
    (hk' : σ'.kheap pd.bv = some (.archObj (.pageDirectory
      (Function.update f (Fl4Spec.ucast 9 j.bv) (.pageTablePDE tab ta tr)))))
    (htab : ∀ w, (eA w).bv = tab → eT w = q0)
    (hko : ∀ q, (q ∈ P ∨ q ∈ L4 ∨ q ∈ L3 ∨ q ∈ L2 ∨ q ∈ L1) → q ≠ pd → σ'.kheap q.bv = σ.kheap q.bv)
    (hat : σ'.archState.x64AsidTable = σ.archState.x64AsidTable) :
    VsNamed th m' ksb := by
  have hpdL : pd ∈ L2 := hpd.mem hR hPt hPI
  refine hN.mapTabS hS hR hPt hPI hR' hPt' hy0 (k0 := 1) (a0 := asid.val) (v0 := va.val) (by omega) (by omega)
    (by rw [hc0]; try exact rfl) (by rw [hc0]; try exact rfl) (by rw [hc1]; try exact rfl) (by rw [hc1]; try exact rfl) hK hpd (by simpa [bnd] using hj)
    ?_ ?_ ?_ hko hat
  · exact wstep2_tab hPt' hpdL hj hk' (a := ta) (r := tr) (by simp) htab
  · simp [rstep, hva]
  · intro i hi hij
    exact (e2_upd hPt hPt' hpdL hj hk hk' (by simpa [bnd] using hi) hij).2

/-- **(F1 stage 4) ASID assign** (`performAsidPoolInvocation (.assign …)`): the
pool `pool` (a walk node at base `b`) gets entry `lo` written with the unmapped
PML4 `q0`, whose cap becomes mapped at `b + lo`. -/
theorem VsNamed.assignS (hN : VsNamed th m ksb) (hS : VsSlotsW th P L4 L3 L2 L1 m)
    (hR : VsRel P m ksb σ) (hPt : PtRel L4 L3 L2 L1 m σ) (hPI : PoolsIn P L4 m)
    (hR' : VsRel P m' ksb σ') (hPt' : PtRel L4 L3 L2 L1 m' σ')
    {y0 : U64} (hy0 : IsSlot th y0) {q0 as0 asid : U64}
    (hc0 : capV m y0 = .Pml4 q0 false as0) (hc1 : capV m' y0 = .Pml4 q0 true asid)
    (hK : ∀ y, IsSlot th y → y ≠ y0 → (VKey (capV m y) ≠ none ∨ VKey (capV m' y) ≠ none) → capV m' y = capV m y)
    {pool lo : U64} {b : Nat} (hpl : VsPath m ksb 5 pool b 0) (hlo : lo.val < 512) (hasid : asid.val = b + lo.val)
    (hq0 : q0 ≠ 0#u64) (hq0t : q0 &&& 1#u64 = 0#u64)
    {f : BitVec 9 → Option Fl4Spec.ObjRef} (hk : σ.kheap pool.bv = some (.archObj (.asidPool f)))
    (hk' : σ'.kheap pool.bv = some (.archObj (.asidPool (Function.update f (Fl4Spec.ucast 9 lo.bv) (some q0.bv)))))
    (hko : ∀ q, (q ∈ P ∨ q ∈ L4 ∨ q ∈ L3 ∨ q ∈ L2 ∨ q ∈ L1) → q ≠ pool → σ'.kheap q.bv = σ.kheap q.bv)
    (hat : σ'.archState.x64AsidTable = σ.archState.x64AsidTable) :
    VsNamed th m' ksb := by
  have hplP : pool ∈ P := hpl.mem hR hPt hPI
  obtain ⟨g, hg, hr⟩ := hR.pool pool hplP
  rw [hk] at hg; cases hg
  obtain ⟨g', hg', hr'⟩ := hR'.pool pool hplP
  rw [hk'] at hg'; cases hg'
  have hnew : m' (peA pool lo) = q0 := by
    have := hr' lo hlo
    rw [Function.update_self, ← optRef_some hq0] at this
    exact (optRef_inj this).symm
  refine hN.mapTabS hS hR hPt hPI hR' hPt' hy0 (k0 := 4) (a0 := asid.val) (v0 := 0) (by omega) (by omega)
    (by rw [hc0]; try exact rfl) (by rw [hc0]; try exact rfl) (by rw [hc1]; try exact rfl) (by rw [hc1]; try exact rfl) hK hpl (by simpa [bnd] using hlo)
    ?_ ?_ ?_ hko hat
  · rw [hnew]; exact wstep5.2 ⟨⟨hq0, hq0t⟩, rfl⟩
  · simp [rstep, hasid]
  · intro i hi hij
    have hi' : i.val < 512 := by simpa [bnd] using hi
    have e := hr' i hi'
    rw [Function.update_of_ne (fun h => hij (ucast9_inj hi' hlo h)), hr i hi'] at e
    rw [optRef_inj e.symm]

/-! ## MakePool -/

/-- **(F1 stage 4) MakePool** (`performAsidControlInvocation`): the free
ASID-table index `hi0` gets the fresh pool `q0` (empty in the spec), whose new
cap at base `hi0 · 512` goes into an unkeyed slot; the sets' objects
unchanged (the pool is new; the relations after at a pool set `P' ⊇ P ∪ {q0}`). -/
theorem VsNamed.makePoolS (hN : VsNamed th m ksb) (hS : VsSlotsW th P L4 L3 L2 L1 m)
    (hR : VsRel P m ksb σ) (hPt : PtRel L4 L3 L2 L1 m σ) (hPI : PoolsIn P L4 m)
    {P' : Set U64} (hR' : VsRel P' m' ksb σ') (hPt' : PtRel L4 L3 L2 L1 m' σ') (hPP : ∀ q ∈ P, q ∈ P')
    {y0 q0 b0 hi0 : U64} (hq0P : q0 ∈ P') (hy0 : IsSlot th y0) (hc1 : capV m' y0 = .AsidPool q0 b0)
    (hk0 : VKey (capV m y0) = none) (hb0 : b0.val = hi0.val * 512) (hhi0 : hi0.val < 2048) (hq0 : q0 ≠ 0#u64)
    (hfresh : ∀ y, IsSlot th y → VKey (capV m y) ≠ some (5, q0))
    (hK : ∀ y, IsSlot th y → y ≠ y0 → (VKey (capV m y) ≠ none ∨ VKey (capV m' y) ≠ none) → capV m' y = capV m y)
    (hat0 : σ.archState.x64AsidTable (Fl4Spec.ucast 11 hi0.bv) = none)
    (hat : σ'.archState.x64AsidTable =
      Function.update σ.archState.x64AsidTable (Fl4Spec.ucast 11 hi0.bv) (some q0.bv))
    (hkq0 : σ'.kheap q0.bv = some (.archObj (.asidPool fun _ => none)))
    (hko : ∀ q, (q ∈ P ∨ q ∈ L4 ∨ q ∈ L3 ∨ q ∈ L2 ∨ q ∈ L1) → σ'.kheap q.bv = σ.kheap q.bv) :
    VsNamed th m' ksb := by
  have hT0 : m (atA ksb hi0) = 0#u64 := by
    have := hR.table hi0 hhi0
    rw [hat0] at this
    exact optRef_eq_none.1 this.symm
  have hT0' : m' (atA ksb hi0) = q0 := by
    have := hR'.table hi0 hhi0
    rw [hat, Function.update_self, ← optRef_some hq0] at this
    exact (optRef_inj this).symm
  refine hN.makePool hS hy0 hc1 hk0 hb0 hhi0 hq0 hfresh hK hT0 hT0' (fun hi hh hne => ?_)
    (fun k p a v i hp h2 h5 hi => wstep_keep hR hPt hR' hPt' hPI hPP (X := fun _ => False)
      (fun q hq _ => hko q hq) k p a v i hp h2 h5 hi not_false) (fun i hi => ?_)
    (fun y hy hu k q hk i hi => unEmpty_keep hPt hPt' hN hS (X := fun _ => False)
      (fun q hq _ => hko q (.inr hq)) y hy hu k q hk not_false i hi)
  · have e := hR'.table hi hh
    rw [hat, Function.update_of_ne (fun h => hne (ucast11_inj (by omega) (by omega) h)), hR.table hi hh] at e
    exact optRef_inj e.symm
  · obtain ⟨g, hg, hr⟩ := hR'.pool q0 hq0P
    rw [hkq0] at hg; cases hg
    have := hr i hi
    rw [optRef_eq_none.1 this.symm]
    exact wstep_zero 5

/-! ## The frame class -/

/-- **(F1 stage 4) The frame class** (frame map / remap / unmap, subframe,
test-and-clear, PML4 flush): the tables written (`X`) are walk nodes whose
walk steps are kept (a PT's entries are no step; a large / huge page entry
stays one), every other set object unchanged, the ASID table unchanged, the
keyed caps kept. -/
theorem VsNamed.leafS (hN : VsNamed th m ksb) (hS : VsSlotsW th P L4 L3 L2 L1 m)
    (hR : VsRel P m ksb σ) (hPt : PtRel L4 L3 L2 L1 m σ) (hPI : PoolsIn P L4 m)
    (hR' : VsRel P m' ksb σ') (hPt' : PtRel L4 L3 L2 L1 m' σ')
    (hK : ∀ y, IsSlot th y → (VKey (capV m y) ≠ none ∨ VKey (capV m' y) ≠ none) → capV m' y = capV m y)
    {X : U64 → Prop}
    (hX : ∀ q, X q → ∃ k a v, VsPath m ksb k q a v ∧
      ∀ i : U64, i.val < bnd k → wstep k (m' (peA q i)) = wstep k (m (peA q i)))
    (hko : ∀ q, (q ∈ P ∨ q ∈ L4 ∨ q ∈ L3 ∨ q ∈ L2 ∨ q ∈ L1) → ¬ X q → σ'.kheap q.bv = σ.kheap q.bv)
    (hat : σ'.archState.x64AsidTable = σ.archState.x64AsidTable) :
    VsNamed th m' ksb := by
  have hT := tbl_same_of_asid hR hR' hat
  refine hN.shrink hK (fun hi hh => .inl (hT hi hh)) (fun k p a v i hp h2 h5 hi => .inl ?_) ?_ ?_
  · by_cases e : X p
    · obtain ⟨k', a', v', hp', hst⟩ := hX p e
      have hkk : k = k' := by
        have hb : 1 ≤ k' ∧ k' ≤ 5 := hp'.lvl'
        exact lvl_disj hR hPt ⟨by omega, h5⟩ hb (hp.mem hR hPt hPI) (hp'.mem hR hPt hPI)
      subst hkk
      exact hst i hi
    · exact wstep_keep hR hPt hR' hPt' hPI (fun q hq => hq) hko k p a v i hp h2 h5 hi e
  · intro y hy hu k q hk i hi
    by_cases e : X q
    · exfalso
      obtain ⟨k', a', v', hp', -⟩ := hX q e
      have hq := hS.need hy (vneed_of_un hu hk)
      have hl := un_lvl hu hk
      have hkk : k = k' := by
        have hb : 1 ≤ k' ∧ k' ≤ 5 := hp'.lvl'
        exact lvl_disj hR hPt ⟨hl.1, by omega⟩ hb hq (hp'.mem hR hPt hPI)
      subst hkk
      exact hN.unNotWalk hy hu hk hp'
    · exact unEmpty_keep hPt hPt' hN hS (fun q hq hx => hko q (.inr hq) hx) y hy hu k q hk e i hi
  · intro y hy q b hb hi hib
    have hcw := hS y hy
    rw [hb] at hcw
    rw [hT _ (pool_hi hcw hib).1]
    exact hN.poolT y hy q b hb hi hib

/-! ## Unmap, finalise, delete -/

/-- **A cap the only one of its key names every walk to its table**, with its
ref (a final cap: `FinM` / `is_final_capability`). -/
theorem VsNamed.own (hN : VsNamed th m ksb) {y0 : U64} {k0 : Nat} {q0 : U64}
    (hkey0 : VKey (capV m y0) = some (k0, q0))
    (huq : ∀ y, IsSlot th y → y ≠ y0 → VKey (capV m y) ≠ VKey (capV m y0)) :
    ∀ a v, VsPath m ksb k0 q0 a v → VRefOf (capV m y0) = some (true, a, v) := by
  intro a v h
  obtain ⟨y, hy, hk, hr⟩ := hN.named _ _ _ _ h
  by_cases e : y = y0
  · subst e; exact hr
  · exact absurd (hk.trans hkey0.symm) (huq y hy e)

/-- **No walk to a table once the step at its ref is cleared** (`hgone` of
`unmapTab` / `delSlot`): every walk to `q0` before carries the ref `(a, v)`
(`own`), the walks after are walks before (`VsPath.sub_down`), and no step
after out of a walk node one level up at that ref goes to `q0` (FL4's
`unmap_pdpt` … / `delete_asid` clear the entry at the ref when it names
`q0`). -/
theorem VsNamed.gone {k0 : Nat} {q0 : U64} {a v : Nat} (hk4 : k0 ≤ 4)
    (hown : ∀ a' v', VsPath m ksb k0 q0 a' v' → a' = a ∧ v' = v)
    (hsub : ∀ k q a v, VsPath m' ksb k q a v → VsPath m ksb k q a v)
    (hpar : ∀ (p : U64) (a1 v1 : Nat) (i : U64), VsPath m ksb (k0 + 1) p a1 v1 → i.val < bnd (k0 + 1) →
      rstep (k0 + 1) a1 v1 i.val = (a, v) → wstep (k0 + 1) (m' (peA p i)) ≠ some q0) :
    ∀ a' v', ¬ VsPath m' ksb k0 q0 a' v' := by
  intro a' v' h
  rcases h.inv with ⟨h5, -⟩ | ⟨p, a1, v1, i, hp, -, -, hi, hw, hr⟩
  · omega
  · obtain ⟨e1, e2⟩ := hown a' v' (hsub _ _ _ _ h)
    subst e1; subst e2
    exact hpar p a1 v1 i (hsub _ _ _ _ hp) hi hr.symm hw

/-- `own` in `gone`'s form. -/
theorem VsNamed.own_ref (hN : VsNamed th m ksb) {y0 : U64} {k0 : Nat} {q0 : U64} {a v : Nat}
    (hkey0 : VKey (capV m y0) = some (k0, q0))
    (huq : ∀ y, IsSlot th y → y ≠ y0 → VKey (capV m y) ≠ VKey (capV m y0))
    (hr0 : VRefOf (capV m y0) = some (true, a, v)) :
    ∀ a' v', VsPath m ksb k0 q0 a' v' → a' = a ∧ v' = v := by
  intro a' v' h
  have := hN.own hkey0 huq a' v' h
  rw [hr0] at this
  simp at this
  exact ⟨this.1.symm, this.2.symm⟩

end

section Inv
variable {L4 L3 L2 L1 : Set U64} {m' : U64 → U64} {σ' : Fl4Spec.State Unit}
  (hPt' : PtRel L4 L3 L2 L1 m' σ')
include hPt'

/-- A cleared PML4 entry is no step. -/
theorem wstep4_inv {p : U64} (hp : p ∈ L4) {f : BitVec 9 → Fl4Spec.PML4E} {j : U64} (hj : j.val < 256)
    (hk' : σ'.kheap p.bv = some (.archObj (.pageMapL4 f))) (he : f (Fl4Spec.ucast 9 j.bv) = .invalidPML4E) :
    wstep 4 (m' (peA p j)) = none := by
  obtain ⟨g, hg, hr⟩ := hPt'.l4 p hp
  rw [hk'] at hg; cases hg
  have h := hr j hj
  rw [he] at h
  exact wstep_none (by decide) (show ¬ eP _ from h)

theorem wstep3_inv {p : U64} (hp : p ∈ L3) {f : BitVec 9 → Fl4Spec.PDPTE} {j : U64} (hj : j.val < 512)
    (hk' : σ'.kheap p.bv = some (.archObj (.pdPointerTable f))) (he : f (Fl4Spec.ucast 9 j.bv) = .invalidPDPTE) :
    wstep 3 (m' (peA p j)) = none := by
  obtain ⟨g, hg, hr⟩ := hPt'.l3 p hp
  rw [hk'] at hg; cases hg
  have h := hr j hj
  rw [he] at h
  exact wstep_none (by decide) (show ¬ eP _ from h)

theorem wstep2_inv {p : U64} (hp : p ∈ L2) {f : BitVec 9 → Fl4Spec.PDE} {j : U64} (hj : j.val < 512)
    (hk' : σ'.kheap p.bv = some (.archObj (.pageDirectory f))) (he : f (Fl4Spec.ucast 9 j.bv) = .invalidPDE) :
    wstep 2 (m' (peA p j)) = none := by
  obtain ⟨g, hg, hr⟩ := hPt'.l2 p hp
  rw [hk'] at hg; cases hg
  have h := hr j hj
  rw [he] at h
  exact wstep_none (by decide) (show ¬ eP _ from h)

end Inv

/-- A cleared pool entry is no step. -/
theorem wstep5_inv {P : Set U64} {m' : U64 → U64} {ksb : U64} {σ' : Fl4Spec.State Unit}
    (hR' : VsRel P m' ksb σ') {p : U64} (hp : p ∈ P) {f : BitVec 9 → Option Fl4Spec.ObjRef} {j : U64}
    (hj : j.val < 512) (hk' : σ'.kheap p.bv = some (.archObj (.asidPool f))) (he : f (Fl4Spec.ucast 9 j.bv) = none) :
    wstep 5 (m' (peA p j)) = none := by
  obtain ⟨g, hg, hr⟩ := hR'.pool p hp
  rw [hk'] at hg; cases hg
  have h := hr j hj
  rw [he] at h
  rw [optRef_eq_none.1 h.symm]
  exact wstep_zero 5

end

end Fl4Proofs.P3.Vs
