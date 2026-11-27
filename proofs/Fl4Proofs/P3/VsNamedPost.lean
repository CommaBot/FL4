/-
P3 (issue #16, F1 stage 5; KENTRY-PLAN f4): **`VsNamed` across a VSpace step
from its `J`-layer post** (VsDecFrame's `VsPostJ`, whose `VsOpF` carries what
the refinement's success path knows: the decode's checks and the perform's
spec writes, per operation).

The refinements (VsPdptMapRel …) export these facts at their success
endpoints, where the decode is computed forward; no decode inversion is needed
(KENTRY-PLAN f3 (2) proposed carrying the decode equation instead).

* `capV_of_foot`, `arch_of_set`: the other slots' caps kept (`SlotFoot`), the
  sets' objects spec arch objects (`VsRel` / `PtRel`).
* **`VsNamed.ofPdptMapF`**, **`ofPdMapF`**, **`ofPtMapF`**: the table maps (VsNamedStep's
  `pdptMapS` / `pdMapS` / `ptMapS`); **`ofAssignF`** (`assignS`); **`ofOpF`**:
  dispatch over VsDecFrame's `VsOpF`.
-/
import Fl4Proofs.P3.VsNamedStep
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Vs
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Classical

noncomputable section

section
variable {th : TypedHeap} {P L4 L3 L2 L1 : Set U64} {m m' : U64 → U64} {ksb : U64} {σ σ' : Fl4Spec.State Unit}

/-- The slots other than `x` keep their caps across a `SlotFoot` step. -/
theorem capV_of_foot {x : U64} (h : SlotFoot th m m' x) :
    ∀ y, IsSlot th y → y ≠ x → capV m' y = capV m y := by
  intro y hy hne
  obtain ⟨-, -, h2⟩ := h y hy
  unfold capV; rw [(h2 hne).1, (h2 hne).2]

/-- A set's object is a spec arch object. -/
theorem arch_of_set (hR : VsRel P m ksb σ) (hPt : PtRel L4 L3 L2 L1 m σ) {q : U64}
    (hq : q ∈ P ∨ q ∈ L4 ∨ q ∈ L3 ∨ q ∈ L2 ∨ q ∈ L1) : ∃ ao, σ.kheap q.bv = some (.archObj ao) := by
  rcases hq with hq | hq | hq | hq | hq
  · obtain ⟨g, hg, -⟩ := hR.pool q hq; exact ⟨_, hg⟩
  · obtain ⟨g, hg, -⟩ := hPt.l4 q hq; exact ⟨_, hg⟩
  · obtain ⟨g, hg, -⟩ := hPt.l3 q hq; exact ⟨_, hg⟩
  · obtain ⟨g, hg, -⟩ := hPt.l2 q hq; exact ⟨_, hg⟩
  · obtain ⟨g, hg, -⟩ := hPt.l1 q hq; exact ⟨_, hg⟩

/-- **(F1 stage 5) PDPT Map with its post's facts** (`PdptMapF`). -/
theorem VsNamed.ofPdptMapF (hN : VsNamed th m ksb) (hS : VsSlotsW th P L4 L3 L2 L1 m)
    (hR : VsRel P m ksb σ) (hPt : PtRel L4 L3 L2 L1 m σ) (hPI : PoolsIn P L4 m)
    (hR' : VsRel P m' ksb σ') (hPt' : PtRel L4 L3 L2 L1 m' σ')
    {x : U64} (hx : IsSlot th x) {c : capability.Cap} (hc : capV m x = c) (hSF : SlotFoot th m m' x)
    (hF : PdptMapF m' x c σ σ') : VsNamed th m' ksb := by
  obtain ⟨q0, as0, va0, asid, va, pm, j, f, ta, tr, rfl, hc1, h0, h20, hfind, hj, hva, hk, hk', hko, hat⟩ := hF
  exact hN.pdptMapS hS hR hPt hPI hR' hPt' hx hc hc1 (fun y hy hne _ => capV_of_foot hSF y hy hne)
    (VsPath.of_find hR h0 h20 hfind) hj hva hk hk' (fun w hw => eT_of_addr hw)
    (fun q hq hne => hko q (arch_of_set hR hPt hq) hne) hat

/-- **(F1 stage 5) PD Map with its post's facts** (`PdMapF`). -/
theorem VsNamed.ofPdMapF (hN : VsNamed th m ksb) (hS : VsSlotsW th P L4 L3 L2 L1 m)
    (hR : VsRel P m ksb σ) (hPt : PtRel L4 L3 L2 L1 m σ) (hPI : PoolsIn P L4 m)
    (hR' : VsRel P m' ksb σ') (hPt' : PtRel L4 L3 L2 L1 m' σ')
    {x : U64} (hx : IsSlot th x) {c : capability.Cap} (hc : capV m x = c) (hSF : SlotFoot th m m' x)
    (hF : PdMapF m m' x c σ σ') : VsNamed th m' ksb := by
  obtain ⟨q0, as0, va0, asid, va, pm, i, pd, j, f, ta, tr, rfl, hc1, h0, h20, hfind, hi, hP4, hT4, hj, hva, hk,
    hk', hko, hat⟩ := hF
  subst hT4
  exact hN.pdMapS hS hR hPt hPI hR' hPt' hx hc hc1 (fun y hy hne _ => capV_of_foot hSF y hy hne)
    (VsPath.l4 (VsPath.of_find hR h0 h20 hfind) hi hP4) hj hva hk hk' (fun w hw => eT_of_addr hw)
    (fun q hq hne => hko q (arch_of_set hR hPt hq) hne) hat

/-- **(F1 stage 5) PT Map with its post's facts** (`PtMapF`). -/
theorem VsNamed.ofPtMapF (hN : VsNamed th m ksb) (hS : VsSlotsW th P L4 L3 L2 L1 m)
    (hR : VsRel P m ksb σ) (hPt : PtRel L4 L3 L2 L1 m σ) (hPI : PoolsIn P L4 m)
    (hR' : VsRel P m' ksb σ') (hPt' : PtRel L4 L3 L2 L1 m' σ')
    {x : U64} (hx : IsSlot th x) {c : capability.Cap} (hc : capV m x = c) (hSF : SlotFoot th m m' x)
    (hF : PtMapF m m' x c σ σ') : VsNamed th m' ksb := by
  obtain ⟨q0, as0, va0, asid, va, pm, i, pt3, k, pd, j, f, ta, tr, rfl, hc1, h0, h20, hfind, hi, hP4, hT4, hk3,
    hP3, hS3, hT3, hj, hva, hk, hk', hko, hat⟩ := hF
  subst hT4
  subst hT3
  exact hN.ptMapS hS hR hPt hPI hR' hPt' hx hc hc1 (fun y hy hne _ => capV_of_foot hSF y hy hne)
    (VsPath.l3 (VsPath.l4 (VsPath.of_find hR h0 h20 hfind) hi hP4) hk3 hP3 hS3) hj hva hk hk'
    (fun w hw => eT_of_addr hw) (fun q hq hne => hko q (arch_of_set hR hPt hq) hne) hat

/-- **(F1 stage 5) ASID assign with its post's facts** (`AssignF`): the pool
is the walk node at the ASID-table entry; the PML4's tag bit clear by its
placement (an unmapped PML4 cap's table is in `L4`, `VsSlotsW`). -/
theorem VsNamed.ofAssignF (hN : VsNamed th m ksb) (hS : VsSlotsW th P L4 L3 L2 L1 m)
    (hR : VsRel P m ksb σ) (hPt : PtRel L4 L3 L2 L1 m σ) (hPI : PoolsIn P L4 m) (hPP : PtPlaced L4 L3 L2 L1)
    (hR' : VsRel P m' ksb σ') (hPt' : PtRel L4 L3 L2 L1 m' σ')
    {x : U64} (hx : IsSlot th x) {c : capability.Cap} (hc : capV m x = c) (hSF : SlotFoot th m m' x)
    (hF : AssignF m' x c σ σ') : VsNamed th m' ksb := by
  obtain ⟨q0, as0, asid, pool, hi, lo, f, rfl, hc1, hhi, htab, hlo, hasid, hq0, hk, hk', hko, hat⟩ := hF
  have e := hR.table hi hhi
  rw [htab] at e
  have hw0 : m (atA ksb hi) ≠ 0#u64 := fun h0 => by rw [h0, Notif.optRef_zero] at e; cases e
  have hw : m (atA ksb hi) = pool := by
    rw [optRef_some hw0] at e
    exact (eq_of_bv (Option.some.inj e)).symm
  have hpl : VsPath m ksb 5 pool (hi.val * 512) 0 := hw ▸ VsPath.tbl hhi hw0
  have hv := hS x hx
  rw [hc] at hv
  simp only [VCapW] at hv
  have hq4 : q0 ∈ L4 := by first | exact hv.1 trivial | exact hv.1 rfl | exact hv.1
  have hqa : q0.val % 4096 = 0 := hPP q0 (Or.inl hq4)
  have hq0t : q0 &&& 1#u64 = 0#u64 := by
    apply UScalar.eq_of_val_eq
    have : (q0 &&& 1#u64).val = q0.val % 2 := by
      rw [UScalar.val_and]; exact Nat.and_two_pow_sub_one_eq_mod q0.val 1
    rw [this]; show q0.val % 2 = 0; omega
  exact hN.assignS hS hR hPt hPI hR' hPt' hx hc hc1 (fun y hy hne _ => capV_of_foot hSF y hy hne) hpl hlo hasid
    hq0 hq0t hk hk' (fun q hq hne => hko q (arch_of_set hR hPt hq) hne) hat

/-! ## The frame class -/

/-- A frame cap has no VSpace key. -/
theorem frameC_vkey {c : capability.Cap} (h : IsFrameC c) : VKey c = none := by
  cases c <;> first | rfl | exact False.elim h

theorem VWalk3.path {pm q : U64} {a : Nat} (h : VWalk3 m pm q) (hp : VsPath m ksb 4 pm a 0) :
    ∃ v, VsPath m ksb 3 q a v := by
  obtain ⟨i, hi, hP, rfl⟩ := h
  exact ⟨_, VsPath.l4 hp hi hP⟩

theorem VWalk2.path {pm q : U64} {a : Nat} (h : VWalk2 m pm q) (hp : VsPath m ksb 4 pm a 0) :
    ∃ v, VsPath m ksb 2 q a v := by
  obtain ⟨p, i, h3, hi, hP, hS, rfl⟩ := h
  obtain ⟨v, hv⟩ := h3.path hp
  exact ⟨_, VsPath.l3 hv hi hP hS⟩

theorem VWalk1.path {pm q : U64} {a : Nat} (h : VWalk1 m pm q) (hp : VsPath m ksb 4 pm a 0) :
    ∃ v, VsPath m ksb 1 q a v := by
  obtain ⟨p, i, h2, hi, hP, hS, rfl⟩ := h
  obtain ⟨v, hv⟩ := h2.path hp
  exact ⟨_, VsPath.l2 hv hi hP hS⟩

theorem wstep2_noStep {w : U64} {d : Fl4Spec.PDE} (hr : PDERel L1 w d) (hd : NoStep2 d) : wstep 2 w = none := by
  rcases hd with rfl | ⟨a, b, c, rfl⟩
  · exact wstep_none (by decide) hr
  · exact wstep_none_S (.inr rfl) hr.2.1

theorem wstep3_noStep {w : U64} {d : Fl4Spec.PDPTE} (hr : PDPTERel L2 w d) (hd : NoStep3 d) : wstep 3 w = none := by
  rcases hd with rfl | ⟨a, b, c, rfl⟩
  · exact wstep_none (by decide) hr
  · exact wstep_none_S (.inl rfl) hr.2.1

/-- The keyed caps kept when the invoked cap is a frame cap before and after. -/
theorem keep_of_frame {x : U64} {c : capability.Cap} (hc : capV m x = c) (hSF : SlotFoot th m m' x)
    (hc0 : IsFrameC c) (hc1 : IsFrameC (capV m' x)) :
    ∀ y, IsSlot th y → (VKey (capV m y) ≠ none ∨ VKey (capV m' y) ≠ none) → capV m' y = capV m y := by
  intro y hy hk
  by_cases e : y = x
  · subst e
    exfalso
    rcases hk with hk | hk
    · rw [hc] at hk; exact hk (frameC_vkey hc0)
    · exact hk (frameC_vkey hc1)
  · exact capV_of_foot hSF y hy e

/-- **(F1 stage 5) Frame map with its post's facts** (`MapLeafF`; VsNamedStep's
`leafS` with the written table). -/
theorem VsNamed.ofMapLeafF (hN : VsNamed th m ksb) (hS : VsSlotsW th P L4 L3 L2 L1 m)
    (hR : VsRel P m ksb σ) (hPt : PtRel L4 L3 L2 L1 m σ) (hPI : PoolsIn P L4 m)
    (hR' : VsRel P m' ksb σ') (hPt' : PtRel L4 L3 L2 L1 m' σ')
    {x : U64} {c : capability.Cap} (hc : capV m x = c) (hSF : SlotFoot th m m' x)
    (hF : MapLeafF m m' x c σ σ') : VsNamed th m' ksb := by
  obtain ⟨hc0, hc1, hat, asid, pm, q, h0, h20, hfind, hko, hW⟩ := hF
  have hpm := VsPath.of_find hR h0 h20 hfind
  refine hN.leafS hS hR hPt hPI hR' hPt' (keep_of_frame hc hSF hc0 hc1) (X := (· = q)) ?_
    (fun q' hq' hne => hko q' (arch_of_set hR hPt hq') hne) hat
  intro q' (hq' : q' = q)
  rw [hq']
  rcases hW with hW | ⟨hW, f, j, d, hj, hk, hd0, hd1, hk'⟩ | ⟨hW, f, j, d, hj, hk, hd0, hd1, hk'⟩
  · obtain ⟨v, hv⟩ := hW.path hpm
    exact ⟨1, _, v, hv, fun i _ => by rw [wstep_one, wstep_one]⟩
  · obtain ⟨v, hv⟩ := hW.path hpm
    refine ⟨2, _, v, hv, fun i hi => ?_⟩
    have hq2 : q ∈ L2 := hv.mem hR hPt hPI
    have hi' : i.val < 512 := by simpa [bnd] using hi
    by_cases hij : i = j
    · subst hij
      obtain ⟨g, hg, hr⟩ := hPt.l2 q hq2
      obtain ⟨g', hg', hr'⟩ := hPt'.l2 q hq2
      rw [hk] at hg; cases hg
      rw [hk'] at hg'; cases hg'
      have h1 := hr i hi'
      have h2 := hr' i hi'
      rw [Function.update_self] at h2
      rw [wstep2_noStep h1 hd0, wstep2_noStep h2 hd1]
    · exact (e2_upd hPt hPt' hq2 hj hk hk' hi' hij).2
  · obtain ⟨v, hv⟩ := hW.path hpm
    refine ⟨3, _, v, hv, fun i hi => ?_⟩
    have hq3 : q ∈ L3 := hv.mem hR hPt hPI
    have hi' : i.val < 512 := by simpa [bnd] using hi
    by_cases hij : i = j
    · subst hij
      obtain ⟨g, hg, hr⟩ := hPt.l3 q hq3
      obtain ⟨g', hg', hr'⟩ := hPt'.l3 q hq3
      rw [hk] at hg; cases hg
      rw [hk'] at hg'; cases hg'
      have h1 := hr i hi'
      have h2 := hr' i hi'
      rw [Function.update_self] at h2
      rw [wstep3_noStep h1 hd0, wstep3_noStep h2 hd1]
    · exact (e3_upd hPt hPt' hq3 hj hk hk' hi' hij).2

/-- Under `ArchShr`, a set table's entry steps alike or is cleared. -/
theorem ent_shr (hPt : PtRel L4 L3 L2 L1 m σ) (hPt' : PtRel L4 L3 L2 L1 m' σ') (hsh : ArchShr σ σ')
    {k : Nat} (hk1 : 1 ≤ k) (hk4 : k ≤ 4) {q : U64} (hq : q ∈ lvlSet P L4 L3 L2 L1 k) {i : U64} (hi : i.val < bnd k) :
    ((eP (m' (peA q i)) ↔ eP (m (peA q i))) ∧ wstep k (m' (peA q i)) = wstep k (m (peA q i))) ∨
      (¬ eP (m' (peA q i)) ∧ wstep k (m' (peA q i)) = none) := by
  obtain rfl | rfl | rfl | rfl : k = 4 ∨ k = 3 ∨ k = 2 ∨ k = 1 := by omega
  · obtain ⟨f, hf, hr⟩ := hPt.l4 q hq
    obtain ⟨g, hg, hr'⟩ := hPt'.l4 q hq
    have hi' : i.val < 256 := by simpa [bnd] using hi
    obtain ⟨ao', h', he⟩ := hsh.2 _ _ hf
    rw [hg] at h'; cases h'
    rcases he with he | ⟨f1, g1, e1, e2, hfg⟩ | ⟨f1, g1, e1, e2, hfg⟩ | ⟨f1, g1, e1, e2, hfg⟩ | ⟨f1, g1, e1, e2, hfg⟩
    · cases he; exact .inl (e4_same (hr i hi') (hr' i hi'))
    · cases e1
    · cases e1
    · cases e1
    · cases e1; cases e2
      have h2 := hr' i hi'
      rcases hfg (Fl4Spec.ucast 9 i.bv) with h | h <;> rw [h] at h2
      · exact .inl (e4_same (hr i hi') h2)
      · exact .inr ⟨h2, wstep_none (by decide) h2⟩
  · obtain ⟨f, hf, hr⟩ := hPt.l3 q hq
    obtain ⟨g, hg, hr'⟩ := hPt'.l3 q hq
    have hi' : i.val < 512 := by simpa [bnd] using hi
    obtain ⟨ao', h', he⟩ := hsh.2 _ _ hf
    rw [hg] at h'; cases h'
    rcases he with he | ⟨f1, g1, e1, e2, hfg⟩ | ⟨f1, g1, e1, e2, hfg⟩ | ⟨f1, g1, e1, e2, hfg⟩ | ⟨f1, g1, e1, e2, hfg⟩
    · cases he; exact .inl (e3_same (hr i hi') (hr' i hi'))
    · cases e1
    · cases e1
    · cases e1; cases e2
      have h2 := hr' i hi'
      rcases hfg (Fl4Spec.ucast 9 i.bv) with h | h <;> rw [h] at h2
      · exact .inl (e3_same (hr i hi') h2)
      · exact .inr ⟨h2, wstep_none (by decide) h2⟩
    · cases e1
  · obtain ⟨f, hf, hr⟩ := hPt.l2 q hq
    obtain ⟨g, hg, hr'⟩ := hPt'.l2 q hq
    have hi' : i.val < 512 := by simpa [bnd] using hi
    obtain ⟨ao', h', he⟩ := hsh.2 _ _ hf
    rw [hg] at h'; cases h'
    rcases he with he | ⟨f1, g1, e1, e2, hfg⟩ | ⟨f1, g1, e1, e2, hfg⟩ | ⟨f1, g1, e1, e2, hfg⟩ | ⟨f1, g1, e1, e2, hfg⟩
    · cases he; exact .inl (e2_same (hr i hi') (hr' i hi'))
    · cases e1
    · cases e1; cases e2
      have h2 := hr' i hi'
      rcases hfg (Fl4Spec.ucast 9 i.bv) with h | h <;> rw [h] at h2
      · exact .inl (e2_same (hr i hi') h2)
      · exact .inr ⟨h2, wstep_none (by decide) h2⟩
    · cases e1
    · cases e1
  · obtain ⟨f, hf, hr⟩ := hPt.l1 q hq
    obtain ⟨g, hg, hr'⟩ := hPt'.l1 q hq
    have hi' : i.val < 512 := by simpa [bnd] using hi
    obtain ⟨ao', h', he⟩ := hsh.2 _ _ hf
    rw [hg] at h'; cases h'
    rcases he with he | ⟨f1, g1, e1, e2, hfg⟩ | ⟨f1, g1, e1, e2, hfg⟩ | ⟨f1, g1, e1, e2, hfg⟩ | ⟨f1, g1, e1, e2, hfg⟩
    · cases he; exact .inl (e1_same (hr i hi') (hr' i hi'))
    · cases e1; cases e2
      have h2 := hr' i hi'
      rcases hfg (Fl4Spec.ucast 9 i.bv) with h | h <;> rw [h] at h2
      · exact .inl (e1_same (hr i hi') h2)
      · exact .inr ⟨h2, wstep_one _⟩
    · cases e1
    · cases e1
    · cases e1

/-- **(F1 stage 5) Frame unmap with its post's facts** (`UnmapLeafF`;
VsNamedOps' `shrink`: only entries cleared). -/
theorem VsNamed.ofUnmapLeafF (hN : VsNamed th m ksb) (hS : VsSlotsW th P L4 L3 L2 L1 m)
    (hR : VsRel P m ksb σ) (hPt : PtRel L4 L3 L2 L1 m σ) (hPI : PoolsIn P L4 m)
    (hR' : VsRel P m' ksb σ') (hPt' : PtRel L4 L3 L2 L1 m' σ')
    {x : U64} {c : capability.Cap} (hc : capV m x = c) (hSF : SlotFoot th m m' x)
    (hF : UnmapLeafF m' x c σ σ') : VsNamed th m' ksb := by
  obtain ⟨hc0, hc1, hsh⟩ := hF
  have hT := tbl_same_of_asid hR hR' hsh.1
  refine hN.shrink (keep_of_frame hc hSF hc0 hc1) (fun hi hh => .inl (hT hi hh)) ?_ ?_ ?_
  · intro k p a v i hp h2 h5 hi
    have hm := hp.mem hR hPt hPI
    by_cases e5 : k = 5
    · subst e5
      left
      obtain ⟨f, hf, -⟩ := hR.pool p hm
      obtain ⟨ao', h', he⟩ := hsh.2 _ _ hf
      have hko : σ'.kheap p.bv = σ.kheap p.bv := by
        rcases he with rfl | ⟨_, _, e1, -⟩ | ⟨_, _, e1, -⟩ | ⟨_, _, e1, -⟩ | ⟨_, _, e1, -⟩
        · rw [h', hf]
        all_goals cases e1
      rw [pool_same_of_kheap hR hR' hm hm hko (by simpa [bnd] using hi)]
    · rcases ent_shr hPt hPt' hsh (by omega) (by omega) hm hi with h | h
      · exact .inl h.2
      · exact .inr h.2
  · intro y hy hu k q hk i hi
    have hq := hS.need hy (vneed_of_un hu hk)
    have hk14 := un_lvl hu hk
    rcases ent_shr hPt hPt' hsh hk14.1 hk14.2 hq hi with h | h
    · rw [h.1]; exact hN.empty y hy hu k q hk i hi
    · exact h.1
  · intro y hy q b hb hi hib
    have hcw := hS y hy
    rw [hb] at hcw
    rw [hT _ (pool_hi hcw hib).1]
    exact hN.poolT y hy q b hb hi hib

/-! ## Table unmaps (`UnmapTabF`) -/

/-- Under `ArchShr`, a walk node's entry steps alike or is cleared. -/
theorem wsub_of_shr (hR : VsRel P m ksb σ) (hPt : PtRel L4 L3 L2 L1 m σ) (hPI : PoolsIn P L4 m)
    (hR' : VsRel P m' ksb σ') (hPt' : PtRel L4 L3 L2 L1 m' σ') (hsh : ArchShr σ σ') :
    ∀ (k : Nat) (p : U64) (a v : Nat) (i : U64), VsPath m ksb k p a v → 2 ≤ k → k ≤ 5 → i.val < bnd k →
      wstep k (m' (peA p i)) = wstep k (m (peA p i)) ∨ wstep k (m' (peA p i)) = none := by
  intro k p a v i hp h2 h5 hi
  have hm := hp.mem hR hPt hPI
  by_cases e5 : k = 5
  · subst e5
    left
    obtain ⟨f, hf, -⟩ := hR.pool p hm
    obtain ⟨ao', h', he⟩ := hsh.2 _ _ hf
    have hko : σ'.kheap p.bv = σ.kheap p.bv := by
      rcases he with rfl | ⟨_, _, e1, -⟩ | ⟨_, _, e1, -⟩ | ⟨_, _, e1, -⟩ | ⟨_, _, e1, -⟩
      · rw [h', hf]
      all_goals cases e1
    rw [pool_same_of_kheap hR hR' hm hm hko (by simpa [bnd] using hi)]
  · rcases ent_shr hPt hPt' hsh (by omega) (by omega) hm hi with h | h
    · exact .inl h.2
    · exact .inr h.2

/-- The ASID lookup data of a level-4 walk node at its ASID. -/
theorem sw4_of_path (hR : VsRel P m ksb σ) {pm : U64} {a : Nat} (h : VsPath m ksb 4 pm a 0) {asid : U64}
    (ha : asid.val = a) : SW4 σ asid pm := by
  cases h with
  | @pool p b lo hp hl h0 ht =>
    cases hp with
    | @tbl hi hh h0' =>
      have hq := hR.tmem hi hh h0'
      obtain ⟨f, hkf, hfp⟩ := hR.pool _ hq
      have e1 : (hi &&& 2047#u64) = hi := UScalar.eq_of_val_eq (by
        rw [and_val hi 11 2047#u64 rfl]; exact Nat.mod_eq_of_lt (by norm_num; omega))
      have hhi : (Fl4Spec.ucast 11 hi.bv : BitVec 11) = Fl4Spec.asidHighBitsOf asid.bv := by
        have := hi_bv asid hi (by rw [Nat.shiftRight_eq_div_pow, ha]; norm_num; omega)
        rwa [e1] at this
      have e2 : (asid &&& 511#u64) = lo := UScalar.eq_of_val_eq (by
        rw [and_val asid 9 511#u64 rfl, ha]; norm_num; omega)
      have hlo : (Fl4Spec.ucast 9 lo.bv : BitVec 9) = Fl4Spec.asidLowBitsOf asid.bv := by
        have := lo_bv asid
        rwa [e2] at this
      refine ⟨_, f, ?_, hkf, ?_⟩
      · rw [← hhi, hR.table hi hh, optRef_some h0']
      · rw [← hlo, hfp lo hl, nativeAsidRoot_optRef, nativeRef, if_pos ht, optRef_some h0]

/-- `gone`'s `hpar` for a PT unmap: a parent PD at the cap's ref is the one
l4v's lookup reaches, whose entry no longer names the table (`NoName2`). -/
theorem hpar2 (hR : VsRel P m ksb σ) (hPt : PtRel L4 L3 L2 L1 m σ) (hPI : PoolsIn P L4 m)
    (hPt' : PtRel L4 L3 L2 L1 m' σ') {asid0 va0 q0 : U64} (hNN : NoName2 σ σ' asid0 va0 q0) :
    ∀ (p : U64) (a1 v1 : Nat) (i : U64), VsPath m ksb 2 p a1 v1 → i.val < bnd 2 →
      rstep 2 a1 v1 i.val = (asid0.val, va0.val) → wstep 2 (m' (peA p i)) ≠ some q0 := by
  intro p a1 v1 i hp hi hr hw
  have hp2 : p ∈ L2 := hp.mem hR hPt hPI
  have hi' : i.val < 512 := by simpa [bnd] using hi
  cases hp with
  | @l3 p3 _ v i3 hp3 hi3 he3 hs3 =>
    have hp3m : p3 ∈ L3 := hp3.mem hR hPt hPI
    cases hp3 with
    | @l4 pm _ i4 hpm hi4 he4 =>
      unfold rstep at hr
      rw [if_neg (show ¬ (2 : Nat) = 5 by decide), if_neg (show ¬ (2 : Nat) = 4 by decide),
        if_neg (show ¬ (2 : Nat) = 3 by decide)] at hr
      simp only [Prod.mk.injEq] at hr
      obtain ⟨ha, hv⟩ := hr
      have e39 : vIdx va0 39 = i4 := UScalar.eq_of_val_eq (by
        rw [vIdx_val, Nat.shiftRight_eq_div_pow]; norm_num at hv ⊢; omega)
      have e30 : vIdx va0 30 = i3 := UScalar.eq_of_val_eq (by
        rw [vIdx_val, Nat.shiftRight_eq_div_pow]; norm_num at hv ⊢; omega)
      have e21 : vIdx va0 21 = i := UScalar.eq_of_val_eq (by
        rw [vIdx_val, Nat.shiftRight_eq_div_pow]; norm_num at hv ⊢; omega)
      have hsw := sw4_of_path hR hpm ha.symm
      have hpm4 : pm ∈ L4 := hpm.mem hR hPt hPI
      obtain ⟨f, hkf, hrf⟩ := hPt.l4 pm hpm4
      obtain ⟨ta4, tr4, hf4⟩ := entry4_of (hrf i4 hi4) he4
      obtain ⟨g, hkg, hrg⟩ := hPt.l3 _ hp3m
      obtain ⟨ta3, tr3, hg3⟩ := entry3_of (hrg i3 hi3) he3 hs3
      obtain ⟨⟨hP2, hS2⟩, hT2⟩ := (wstep32 (.inr rfl)).1 hw
      obtain ⟨h, hkh, hrh⟩ := hPt'.l2 _ hp2
      obtain ⟨ta, tr, hh⟩ := entry2_of (hrh i hi') hP2 hS2
      rw [hT2] at hh
      refine hNN pm _ _ hsw ⟨f, ta4, tr4, hkf, by rw [e39]; exact hf4⟩ ⟨g, ta3, tr3, hkg, by rw [e30]; exact hg3⟩
        h hkh ta tr ?_
      rw [e21]; exact hh

/-- `gone`'s `hpar` for a PD unmap (`NoName3`). -/
theorem hpar3 (hR : VsRel P m ksb σ) (hPt : PtRel L4 L3 L2 L1 m σ) (hPI : PoolsIn P L4 m)
    (hPt' : PtRel L4 L3 L2 L1 m' σ') {asid0 va0 q0 : U64} (hNN : NoName3 σ σ' asid0 va0 q0) :
    ∀ (p : U64) (a1 v1 : Nat) (i : U64), VsPath m ksb 3 p a1 v1 → i.val < bnd 3 →
      rstep 3 a1 v1 i.val = (asid0.val, va0.val) → wstep 3 (m' (peA p i)) ≠ some q0 := by
  intro p a1 v1 i hp hi hr hw
  have hp3 : p ∈ L3 := hp.mem hR hPt hPI
  have hi' : i.val < 512 := by simpa [bnd] using hi
  cases hp with
  | @l4 pm _ i4 hpm hi4 he4 =>
    unfold rstep at hr
    rw [if_neg (show ¬ (3 : Nat) = 5 by decide), if_neg (show ¬ (3 : Nat) = 4 by decide), if_pos rfl] at hr
    simp only [Prod.mk.injEq] at hr
    obtain ⟨ha, hv⟩ := hr
    have e39 : vIdx va0 39 = i4 := UScalar.eq_of_val_eq (by
      rw [vIdx_val, Nat.shiftRight_eq_div_pow]; norm_num at hv ⊢; omega)
    have e30 : vIdx va0 30 = i := UScalar.eq_of_val_eq (by
      rw [vIdx_val, Nat.shiftRight_eq_div_pow]; norm_num at hv ⊢; omega)
    have hsw := sw4_of_path hR hpm ha.symm
    have hpm4 : pm ∈ L4 := hpm.mem hR hPt hPI
    obtain ⟨f, hkf, hrf⟩ := hPt.l4 pm hpm4
    obtain ⟨ta4, tr4, hf4⟩ := entry4_of (hrf i4 hi4) he4
    obtain ⟨⟨hP3, hS3⟩, hT3⟩ := (wstep32 (.inl rfl)).1 hw
    obtain ⟨h, hkh, hrh⟩ := hPt'.l3 _ hp3
    obtain ⟨ta, tr, hh⟩ := entry3_of (hrh i hi') hP3 hS3
    rw [hT3] at hh
    refine hNN pm _ hsw ⟨f, ta4, tr4, hkf, by rw [e39]; exact hf4⟩ h hkh ta tr ?_
    rw [e30]; exact hh

/-- `gone`'s `hpar` for a PDPT unmap (`NoName4`). -/
theorem hpar4 (hR : VsRel P m ksb σ) (hPt : PtRel L4 L3 L2 L1 m σ) (hPI : PoolsIn P L4 m)
    (hPt' : PtRel L4 L3 L2 L1 m' σ') {asid0 va0 q0 : U64} (hNN : NoName4 σ σ' asid0 va0 q0) :
    ∀ (p : U64) (a1 v1 : Nat) (i : U64), VsPath m ksb 4 p a1 v1 → i.val < bnd 4 →
      rstep 4 a1 v1 i.val = (asid0.val, va0.val) → wstep 4 (m' (peA p i)) ≠ some q0 := by
  intro p a1 v1 i hp hi hr hw
  have hp4 : p ∈ L4 := hp.mem hR hPt hPI
  have hi' : i.val < 256 := by simpa [bnd] using hi
  have hv0 := hp.v4
  subst hv0
  unfold rstep at hr
  rw [if_neg (show ¬ (4 : Nat) = 5 by decide), if_pos rfl] at hr
  simp only [Prod.mk.injEq] at hr
  obtain ⟨ha, hv⟩ := hr
  have e39 : vIdx va0 39 = i := UScalar.eq_of_val_eq (by
    rw [vIdx_val, Nat.shiftRight_eq_div_pow]; norm_num at hv ⊢; omega)
  have hsw := sw4_of_path hR hp ha.symm
  obtain ⟨hP4, hT4⟩ := wstep4.1 hw
  obtain ⟨h, hkh, hrh⟩ := hPt'.l4 _ hp4
  obtain ⟨ta, tr, hh⟩ := entry4_of (hrh i hi') hP4
  rw [hT4] at hh
  refine hNN p hsw h hkh ta tr ?_
  rw [e39]; exact hh

/-- **(F1 stage 5) Table Unmap with its post's facts** (`UnmapTabF`;
VsNamedOps' `unmapTab`): `huq` (the cap the only one of its key) from the
decode's final check (`huq_of_finF`, at the caller). -/
theorem VsNamed.ofUnmapTabF (hN : VsNamed th m ksb) (hS : VsSlotsW th P L4 L3 L2 L1 m)
    (hR : VsRel P m ksb σ) (hPt : PtRel L4 L3 L2 L1 m σ) (hPI : PoolsIn P L4 m)
    (hR' : VsRel P m' ksb σ') (hPt' : PtRel L4 L3 L2 L1 m' σ')
    {x : U64} (hx : IsSlot th x) {c : capability.Cap} (hc : capV m x = c) (hSF : SlotFoot th m m' x)
    (hF : UnmapTabF m' x c σ σ')
    (huq : ∀ y, IsSlot th y → y ≠ x → VKey (capV m y) ≠ VKey (capV m x)) : VsNamed th m' ksb := by
  obtain ⟨hsh, q0, mp, asid0, va0, hcase, hz⟩ := hF
  have hT := tbl_same_of_asid hR hR' hsh.1
  have hW := wsub_of_shr hR hPt hPI hR' hPt' hsh
  have hsub : ∀ k q a v, VsPath m' ksb k q a v → VsPath m ksb k q a v :=
    fun _ _ _ _ h => VsPath.sub_down (fun hi hh => .inl (hT hi hh)) hW h
  obtain ⟨k0, hk1, hk3, hkey0, hu1, hkey1, hr0, hpar⟩ : ∃ k0, 1 ≤ k0 ∧ k0 ≤ 3 ∧
      VKey (capV m x) = some (k0, q0) ∧ TabUn (capV m' x) ∧ VKey (capV m' x) = some (k0, q0) ∧
      VRefOf (capV m x) = some (mp, asid0.val, va0.val) ∧
      (mp = true → ∀ (p : U64) (a1 v1 : Nat) (i : U64), VsPath m ksb (k0 + 1) p a1 v1 → i.val < bnd (k0 + 1) →
        rstep (k0 + 1) a1 v1 i.val = (asid0.val, va0.val) → wstep (k0 + 1) (m' (peA p i)) ≠ some q0) := by
    rcases hcase with ⟨rfl, h1, hn⟩ | ⟨rfl, h1, hn⟩ | ⟨rfl, h1, hn⟩
    · exact ⟨1, le_rfl, by omega, by rw [hc]; exact rfl, by rw [h1]; exact rfl, by rw [h1]; exact rfl,
        by rw [hc]; exact rfl, fun hm => hpar2 hR hPt hPI hPt' (hn hm)⟩
    · exact ⟨2, by omega, by omega, by rw [hc]; exact rfl, by rw [h1]; exact rfl, by rw [h1]; exact rfl,
        by rw [hc]; exact rfl, fun hm => hpar3 hR hPt hPI hPt' (hn hm)⟩
    · exact ⟨3, by omega, le_rfl, by rw [hc]; exact rfl, by rw [h1]; exact rfl, by rw [h1]; exact rfl,
        by rw [hc]; exact rfl, fun hm => hpar4 hR hPt hPI hPt' (hn hm)⟩
  have hun0 : mp = false → TabUn (capV m x) := fun hm => by
    rw [tabUn_iff]; exact ⟨by rw [hkey0]; simp, _, _, hm ▸ hr0⟩
  refine hN.unmapTab hS hkey0 huq hu1 hkey1 (fun y hy hne _ => capV_of_foot hSF y hy hne) hT hW ?_ ?_
  · intro a v h
    cases mp
    · exact hN.unNotWalk hx (hun0 rfl) hkey0 (hsub _ _ _ _ h)
    · exact VsNamed.gone (by omega) (hN.own_ref hkey0 huq hr0) hsub (hpar rfl) a v h
  · intro y hy hu k q hk i hi
    by_cases e : y = x
    · subst e
      rw [hkey1] at hk
      obtain ⟨rfl, rfl⟩ : k0 = k ∧ q0 = q := by simpa using hk
      cases mp
      · have hu0 := hun0 rfl
        have hq := hS.need hy (vneed_of_un hu0 hkey0)
        rcases ent_shr hPt hPt' hsh hk1 (by omega) hq hi with h | h
        · rw [h.1]; exact hN.empty y hy hu0 k0 q0 hkey0 i hi
        · exact h.1
      · exact hz rfl i (lt_of_lt_of_le hi (bnd_le _))
    · have hc' := capV_of_foot hSF y hy e
      rw [hc'] at hu hk
      have hq := hS.need hy (vneed_of_un hu hk)
      have hk14 := un_lvl hu hk
      rcases ent_shr hPt hPt' hsh hk14.1 hk14.2 hq hi with h | h
      · rw [h.1]; exact hN.empty y hy hu k q hk i hi
      · exact h.1

/-- **`VsNamed.stepShr` with new slots and new keyed caps** (a PML4 retype):
the old keyed slots kept with their caps, every keyed cap after old or new,
a new one unmapped, the only cap of its key, its table empty after (as
`VsNamed.grow`), only entries cleared in the spec (`ArchShr`), the
relations before and after at the same sets. -/
theorem VsNamed.stepShrGrow {th' : TypedHeap} (hN : VsNamed th m ksb) (hS : VsSlotsW th P L4 L3 L2 L1 m)
    (hR : VsRel P m ksb σ) (hPt : PtRel L4 L3 L2 L1 m σ) (hPI : PoolsIn P L4 m)
    (hR' : VsRel P m' ksb σ') (hPt' : PtRel L4 L3 L2 L1 m' σ') (hsh : ArchShr σ σ')
    (hth : ∀ y, IsSlot th y → IsSlot th' y)
    (hold : ∀ y, IsSlot th y → VKey (capV m y) ≠ none → capV m' y = capV m y)
    (hnew : ∀ y, IsSlot th' y → VKey (capV m' y) ≠ none → (IsSlot th y ∧ capV m' y = capV m y) ∨
      (TabUn (capV m' y) ∧ (∀ z, IsSlot th' z → z ≠ y → VKey (capV m' z) ≠ VKey (capV m' y)) ∧
        ∀ k q, VKey (capV m' y) = some (k, q) → ∀ i : U64, i.val < (if k = 4 then 256 else 512) →
          ¬ eP (m' (peA q i)))) :
    VsNamed th' m' ksb := by
  have hT := tbl_same_of_asid hR hR' hsh.1
  have hW := wsub_of_shr hR hPt hPI hR' hPt' hsh
  refine ⟨fun k q a v h => ?_, fun y1 y2 hy1 hy2 hk hn => ?_, fun y1 y2 hy1 hy2 hk hu => ?_,
    fun y hy hu k q hk i hi => ?_, fun y hy q b hb hi hib => ?_⟩
  · obtain ⟨y, hy, hk, hr⟩ := hN.named k q a v (VsPath.sub_down (fun hi hh => .inl (hT hi hh)) hW h)
    have hc := hold y hy (by rw [hk]; simp)
    exact ⟨y, hth y hy, by rw [hc]; exact hk, by rw [hc]; exact hr⟩
  · rcases hnew y1 hy1 hn with ⟨o1, c1⟩ | ⟨-, f1, -⟩
    · rcases hnew y2 hy2 (by rw [← hk]; exact hn) with ⟨o2, c2⟩ | ⟨-, f2, -⟩
      · rw [c1, c2] at hk; rw [c1] at hn; rw [c1, c2]; exact hN.uref y1 y2 o1 o2 hk hn
      · by_cases e : y1 = y2
        · rw [e]
        · exact absurd hk (f2 y1 hy1 e)
    · by_cases e : y2 = y1
      · rw [e]
      · exact absurd hk.symm (f1 y2 hy2 e)
  · have hn := tabUn_key hu
    rcases hnew y1 hy1 hn with ⟨o1, c1⟩ | ⟨-, f1, -⟩
    · rcases hnew y2 hy2 (by rw [← hk]; exact hn) with ⟨o2, c2⟩ | ⟨-, f2, -⟩
      · rw [c1, c2] at hk; rw [c1] at hu; exact hN.uun y1 y2 o1 o2 hk hu
      · by_contra e; exact f2 y1 hy1 e hk
    · by_contra e; exact f1 y2 hy2 (Ne.symm e) hk.symm
  · rcases hnew y hy (tabUn_key hu) with ⟨o, c⟩ | ⟨-, -, he⟩
    · rw [c] at hu hk
      have hq := hS.need o (vneed_of_un hu hk)
      have hk14 := un_lvl hu hk
      have hi' : i.val < bnd k := by unfold bnd; exact hi
      rcases ent_shr hPt hPt' hsh hk14.1 hk14.2 hq hi' with h | h
      · rw [h.1]; exact hN.empty y o hu k q hk i hi
      · exact h.1
    · exact he k q hk i hi
  · have hk0 : VKey (capV m' y) = some (5, q) := by rw [hb]; rfl
    rcases hnew y hy (by rw [hk0]; simp) with ⟨o, c⟩ | ⟨hu, -, -⟩
    · rw [c] at hb
      have hcw := hS y o
      rw [hb] at hcw
      rw [hT _ (pool_hi hcw (by omega)).1]
      exact hN.poolT y o q b hb hi (by omega)
    · rw [hb] at hu; exact hu.elim

/-- **(F1 stage 5, item 4 vehicle) `VsNamed` across a step keeping the keyed
caps (`VsKeep`) with only spec entries cleared (`ArchShr`)**: the relations at
the same sets before and after (no FL4 word equality asked: a frame / CSpace
step's `ArchShr.of_keep` from its kept arch objects and ASID table). -/
theorem VsNamed.stepShr {th' : TypedHeap} (hN : VsNamed th m ksb) (hS : VsSlotsW th P L4 L3 L2 L1 m)
    (hR : VsRel P m ksb σ) (hPt : PtRel L4 L3 L2 L1 m σ) (hPI : PoolsIn P L4 m)
    (hR' : VsRel P m' ksb σ') (hPt' : PtRel L4 L3 L2 L1 m' σ')
    (hK : VsKeep th th' m m') (hsh : ArchShr σ σ') : VsNamed th' m' ksb := by
  have hT := tbl_same_of_asid hR hR' hsh.1
  have hW := wsub_of_shr hR hPt hPI hR' hPt' hsh
  refine ⟨fun k q a v h => ?_, fun y1 y2 hy1 hy2 hk hn => ?_, fun y1 y2 hy1 hy2 hk hu => ?_,
    fun y' hy' hu k q hk i hi => ?_, fun y' hy' q b hb hi hib => ?_⟩
  · obtain ⟨y, hy, hk, hr⟩ := hN.named k q a v (VsPath.sub_down (fun hi hh => .inl (hT hi hh)) hW h)
    obtain ⟨y', hy', e1, e2⟩ := hK.fwd y hy (by rw [hk]; simp)
    exact ⟨y', hy', by rw [e1]; exact hk, by rw [e2]; exact hr⟩
  · obtain ⟨z1, hz1, a1, b1⟩ := hK.back y1 hy1 hn
    obtain ⟨z2, hz2, a2, b2⟩ := hK.back y2 hy2 (by rw [← hk]; exact hn)
    rw [← b1, ← b2]
    exact hN.uref z1 z2 hz1 hz2 (by rw [a1, a2, hk]) (by rw [a1]; exact hn)
  · by_contra hne
    obtain ⟨z1, z2, hz1, hz2, hz, a1, b1, a2⟩ := hK.inj y1 y2 hy1 hy2 hne hk hu
    exact hz (hN.uun z1 z2 hz1 hz2 (by rw [a1, a2]) (TabUn.of_ref a1 b1 hu))
  · obtain ⟨z, hz, a1, b1⟩ := hK.back y' hy' (tabUn_key hu)
    have hu' := TabUn.of_ref a1 b1 hu
    have hk' : VKey (capV m z) = some (k, q) := a1.trans hk
    have hq := hS.need hz (vneed_of_un hu' hk')
    have hk14 := un_lvl hu' hk'
    have hi' : i.val < bnd k := by unfold bnd; exact hi
    rcases ent_shr hPt hPt' hsh hk14.1 hk14.2 hq hi' with h | h
    · rw [h.1]; exact hN.empty z hz hu' k q hk' i hi
    · exact h.1
  · have hk0 : VKey (capV m' y') = some (5, q) := by rw [hb]; rfl
    obtain ⟨z, hz, a1, b1⟩ := hK.back y' hy' (by rw [hk0]; simp)
    obtain ⟨b', hb'⟩ := pool_of_key (a1.trans hk0)
    rw [hb', hb] at b1
    simp only [VRefOf, Option.some.injEq, Prod.mk.injEq, true_and, and_true] at b1
    have hcw := hS z hz
    rw [hb'] at hcw
    rw [hT _ (pool_hi hcw (by omega)).1]
    exact hN.poolT z hz q b' hb' hi (by omega)

/-- **(f4g) `VsNamed` after emptying the slot `x`** of a `VsPend` state (the deletion loop's
`empty_slot`): the other slots kept, only spec entries cleared (`ArchShr`), the relations before
and after at the same sets (as `VsNamed.stepShr`). -/
theorem VsNamed.ofPendShr {x : U64} (hN : VsPend th m ksb x) (hS : VsSlotsW th P L4 L3 L2 L1 m)
    (hR : VsRel P m ksb σ) (hPt : PtRel L4 L3 L2 L1 m σ) (hPI : PoolsIn P L4 m)
    (hR' : VsRel P m' ksb σ') (hPt' : PtRel L4 L3 L2 L1 m' σ') (hsh : ArchShr σ σ')
    (hc : ∀ y, IsSlot th y → y ≠ x → capV m' y = capV m y) (hx : VKey (capV m' x) = none) :
    VsNamed th m' ksb := by
  have hT := tbl_same_of_asid hR hR' hsh.1
  have hW := wsub_of_shr hR hPt hPI hR' hPt' hsh
  refine ⟨fun k q a v h => ?_, fun y1 y2 hy1 hy2 hk hn => ?_, fun y1 y2 hy1 hy2 hk hu => ?_,
    fun y hy hu k q hk i hi => ?_, fun y hy q b hb hi hib => ?_⟩
  · obtain ⟨y, hy, hyx, hr⟩ := hN.named k q a v (VsPath.sub_down (fun hi hh => .inl (hT hi hh)) hW h)
    exact ⟨y, hy, by rw [hc y hy hyx]; exact hr⟩
  · have h1x : y1 ≠ x := fun e => hn (by rw [e]; exact hx)
    have h2x : y2 ≠ x := fun e => hn (by rw [hk, e]; exact hx)
    rw [hc y1 hy1 h1x, hc y2 hy2 h2x] at hk ⊢; rw [hc y1 hy1 h1x] at hn
    exact hN.uref y1 y2 hy1 hy2 h1x h2x hk hn
  · have h1x : y1 ≠ x := fun e => tabUn_key hu (by rw [e]; exact hx)
    have h2x : y2 ≠ x := fun e => tabUn_key hu (by rw [hk, e]; exact hx)
    rw [hc y1 hy1 h1x, hc y2 hy2 h2x] at hk; rw [hc y1 hy1 h1x] at hu
    exact hN.uun y1 y2 hy1 hy2 h1x h2x hk hu
  · have hyx : y ≠ x := fun e => tabUn_key hu (by rw [e]; exact hx)
    rw [hc y hy hyx] at hu hk
    have hq := hS.need hy (vneed_of_un hu hk)
    have hk14 := un_lvl hu hk
    have hi' : i.val < bnd k := by unfold bnd; exact hi
    rcases ent_shr hPt hPt' hsh hk14.1 hk14.2 hq hi' with h | h
    · rw [h.1]; exact hN.empty y hy hyx hu k q hk i hi
    · exact h.1
  · have hyx : y ≠ x := fun e => by rw [e] at hb; rw [hb] at hx; simp [VKey] at hx
    rw [hc y hy hyx] at hb
    have hcw := hS y hy
    rw [hb] at hcw
    rw [hT _ (pool_hi hcw (by omega)).1]
    exact hN.poolT y hy hyx q b hb hi (by omega)

/-- **(f4g) `VsPend` after a table cap's unmap at finalisation** (the cap kept in its slot; only
spec entries cleared, the mapped table no longer named at its ref, `NoName2/3/4`): `VsNamed` after
(`stepShr`), and the cap's walk named by another cap of its key or gone (`VsNamed.gone`). -/
theorem VsNamed.pendUnmap (hN : VsNamed th m ksb) (hS : VsSlotsW th P L4 L3 L2 L1 m)
    (hR : VsRel P m ksb σ) (hPt : PtRel L4 L3 L2 L1 m σ) (hPI : PoolsIn P L4 m)
    (hR' : VsRel P m' ksb σ') (hPt' : PtRel L4 L3 L2 L1 m' σ') (hsh : ArchShr σ σ')
    (hc : ∀ y, IsSlot th y → capV m' y = capV m y) {x : U64} (hx : IsSlot th x)
    (hF : ∃ (q0 : U64) (mp : Bool) (asid0 va0 : U64),
      (capV m x = .PageTable q0 mp asid0 va0 ∧ (mp = true → NoName2 σ σ' asid0 va0 q0)) ∨
      (capV m x = .PageDirectory q0 mp asid0 va0 ∧ (mp = true → NoName3 σ σ' asid0 va0 q0)) ∨
      (capV m x = .Pdpt q0 mp asid0 va0 ∧ (mp = true → NoName4 σ σ' asid0 va0 q0))) :
    VsPend th m' ksb x := by
  have hN' := hN.stepShr hS hR hPt hPI hR' hPt' (VsKeep.of_eq hc) hsh
  have hT := tbl_same_of_asid hR hR' hsh.1
  have hW := wsub_of_shr hR hPt hPI hR' hPt' hsh
  have hsub : ∀ k q a v, VsPath m' ksb k q a v → VsPath m ksb k q a v :=
    fun _ _ _ _ h => VsPath.sub_down (fun hi hh => .inl (hT hi hh)) hW h
  refine hN'.pendSelf fun k q a v hp hr => ?_
  rw [hc x hx] at hr ⊢
  by_cases hex : ∃ y1, IsSlot th y1 ∧ y1 ≠ x ∧ VKey (capV m y1) = VKey (capV m x)
  · obtain ⟨y1, hy1, hne, hk1⟩ := hex
    exact ⟨y1, hy1, hne, by rw [hc y1 hy1]; exact hk1⟩
  · exfalso
    have huq : ∀ y, IsSlot th y → y ≠ x → VKey (capV m y) ≠ VKey (capV m x) :=
      fun y hy hne he => hex ⟨y, hy, hne, he⟩
    obtain ⟨q0, mp, asid0, va0, hcase⟩ := hF
    obtain ⟨k0, hk1, hk3, hkey0, hr0, hpar⟩ : ∃ k0, 1 ≤ k0 ∧ k0 ≤ 3 ∧ VKey (capV m x) = some (k0, q0) ∧
        VRefOf (capV m x) = some (mp, asid0.val, va0.val) ∧
        (mp = true → ∀ (p : U64) (a1 v1 : Nat) (i : U64), VsPath m ksb (k0 + 1) p a1 v1 → i.val < bnd (k0 + 1) →
          rstep (k0 + 1) a1 v1 i.val = (asid0.val, va0.val) → wstep (k0 + 1) (m' (peA p i)) ≠ some q0) := by
      rcases hcase with ⟨e, hn⟩ | ⟨e, hn⟩ | ⟨e, hn⟩ <;> rw [e]
      · exact ⟨1, le_rfl, by omega, rfl, rfl, fun hm => hpar2 hR hPt hPI hPt' (hn hm)⟩
      · exact ⟨2, by omega, by omega, rfl, rfl, fun hm => hpar3 hR hPt hPI hPt' (hn hm)⟩
      · exact ⟨3, by omega, le_rfl, rfl, rfl, fun hm => hpar4 hR hPt hPI hPt' (hn hm)⟩
    obtain ⟨hk, hrf⟩ := hr
    rw [hkey0] at hk
    obtain ⟨rfl, rfl⟩ : k0 = k ∧ q0 = q := by simpa using hk
    rw [hr0] at hrf
    obtain ⟨rfl, ha, hv⟩ : mp = true ∧ asid0.val = a ∧ va0.val = v := by simpa using hrf
    subst ha; subst hv
    exact VsNamed.gone (by omega) (hN.own_ref hkey0 huq hr0) hsub (hpar rfl) _ _ hp

/-- (f4g) Aligned table / pool words of the sets. -/
theorem peA_al_sets (hVP : VsPlaced P ksb) (hPP : PtPlaced L4 L3 L2 L1) {q : U64}
    (hq : q ∈ P ∨ q ∈ L4 ∨ q ∈ L3 ∨ q ∈ L2 ∨ q ∈ L1) {i : U64} (hi : i.val < 512) : Aligned (peA q i) := by
  have hqa : q.val % 4096 = 0 := by
    rcases hq with hq | hq
    · exact (hVP.pal q hq).1
    · exact hPP q hq
  have hv := peA_val (tbl_fit hqa) hi
  unfold Aligned; rw [hv]; omega

/-- **(f4g) `VsNamed` across zero writes keeping the ASID table** (`delete_asid`: a pool word
zeroed; the slots kept): `VsNamed.shrink`. -/
theorem VsNamed.shrinkZ (hN : VsNamed th m ksb) (hS : VsSlotsW th P L4 L3 L2 L1 m) (hVP : VsPlaced P ksb)
    (hPP : PtPlaced L4 L3 L2 L1) (hR : VsRel P m ksb σ) (hPt : PtRel L4 L3 L2 L1 m σ) (hPI : PoolsIn P L4 m)
    (hc : ∀ y, IsSlot th y → capV m' y = capV m y) (hz : ∀ b, Aligned b → m' b = m b ∨ m' b = 0#u64)
    (htbl : ∀ hi : U64, hi.val < 2048 → m' (atA ksb hi) = m (atA ksb hi)) : VsNamed th m' ksb := by
  refine hN.shrink (fun y hy _ => hc y hy) (fun hi hh => .inl (htbl hi hh)) ?_ ?_ ?_
  · intro k p a v i hp _ _ hi
    have hm := lvl_mem (hp.mem hR hPt hPI)
    rcases hz _ (peA_al_sets hVP hPP hm (lt_of_lt_of_le hi (bnd_le k))) with e | e
    · exact .inl (by rw [e])
    · exact .inr (by rw [e]; exact wstep_zero k)
  · intro y hy hu k q hk i hi
    have hq := lvl_mem (hS.need hy (vneed_of_un hu hk))
    rcases hz _ (peA_al_sets hVP hPP hq (lt_of_lt_of_le hi (bnd_le k))) with e | e
    · rw [e]; exact hN.empty y hy hu k q hk i (by unfold bnd at hi; exact hi)
    · rw [e]; simp [eP]
  · intro y hy q b hb hi hib
    have hcw := hS y hy
    rw [hb] at hcw
    rw [htbl _ (pool_hi hcw (by omega)).1]
    exact hN.poolT y hy q b hb hi hib

/-- **(f4g) `VsPend` after a PML4 cap's `delete_asid` at finalisation** (the cap kept): `VsNamed`
after (`shrinkZ`), and the cap's walk named by another cap of its key or gone (the ASID's pool
word, if it was the root, zeroed). -/
theorem VsNamed.pendDa (hN : VsNamed th m ksb) (hS : VsSlotsW th P L4 L3 L2 L1 m) (hVP : VsPlaced P ksb)
    (hPP : PtPlaced L4 L3 L2 L1) (hR : VsRel P m ksb σ) (hPt : PtRel L4 L3 L2 L1 m σ) (hPI : PoolsIn P L4 m)
    (hc : ∀ y, IsSlot th y → capV m' y = capV m y) (hz : ∀ b, Aligned b → m' b = m b ∨ m' b = 0#u64)
    (htbl : ∀ hi : U64, hi.val < 2048 → m' (atA ksb hi) = m (atA ksb hi)) {x : U64} (hx : IsSlot th x)
    {q a : U64} {mp : Bool} (hcx : capV m x = .Pml4 q mp a)
    (hgone : mp = true → ∀ hi lo : U64, hi.val = a.val / 512 % 2048 → lo.val = a.val % 512 →
      m (atA ksb hi) ≠ 0#u64 → m (peA (m (atA ksb hi)) lo) = q → m (peA (m (atA ksb hi)) lo) &&& 1#u64 = 0#u64 →
      m' (peA (m (atA ksb hi)) lo) = 0#u64) :
    VsPend th m' ksb x := by
  have hN' := hN.shrinkZ hS hVP hPP hR hPt hPI hc hz htbl
  have hW : ∀ (k : Nat) (p : U64) (a v : Nat) (i : U64), VsPath m ksb k p a v → 2 ≤ k → k ≤ 5 → i.val < bnd k →
      wstep k (m' (peA p i)) = wstep k (m (peA p i)) ∨ wstep k (m' (peA p i)) = none := by
    intro k p a v i hp _ _ hi
    have hm := lvl_mem (hp.mem hR hPt hPI)
    rcases hz _ (peA_al_sets hVP hPP hm (lt_of_lt_of_le hi (bnd_le k))) with e | e
    · exact .inl (by rw [e])
    · exact .inr (by rw [e]; exact wstep_zero k)
  have hsub : ∀ k q a v, VsPath m' ksb k q a v → VsPath m ksb k q a v :=
    fun _ _ _ _ h => VsPath.sub_down (fun hi hh => .inl (htbl hi hh)) hW h
  refine hN'.pendSelf fun k q' a' v' hp hr => ?_
  rw [hc x hx] at hr ⊢
  by_cases hex : ∃ y1, IsSlot th y1 ∧ y1 ≠ x ∧ VKey (capV m y1) = VKey (capV m x)
  · obtain ⟨y1, hy1, hne, hk1⟩ := hex
    exact ⟨y1, hy1, hne, by rw [hc y1 hy1]; exact hk1⟩
  · exfalso
    have huq : ∀ y, IsSlot th y → y ≠ x → VKey (capV m y) ≠ VKey (capV m x) :=
      fun y hy hne he => hex ⟨y, hy, hne, he⟩
    have hkey0 : VKey (capV m x) = some (4, q) := by rw [hcx]; rfl
    obtain ⟨hk, hrf⟩ := hr
    rw [hkey0] at hk
    obtain ⟨rfl, rfl⟩ : 4 = k ∧ q = q' := by simpa using hk
    have hr0 : VRefOf (capV m x) = some (mp, a.val, 0) := by rw [hcx]; rfl
    rw [hr0] at hrf
    obtain ⟨rfl, rfl, rfl⟩ : mp = true ∧ a.val = a' ∧ 0 = v' := by simpa using hrf
    refine VsNamed.gone (k0 := 4) (by omega) (hN.own_ref hkey0 huq hr0) hsub ?_ _ _ hp
    intro p a1 v1 i hp5 hi hrs hw
    have hpm := lvl_mem (hp5.mem hR hPt hPI)
    cases hp5 with
    | @tbl hi5 hh h0 =>
      have hrs' : hi5.val * 512 + i.val = a.val := by
        simp [rstep] at hrs; omega
      have hi' : i.val < 512 := by simpa [bnd] using hi
      obtain ⟨⟨hne0, htag⟩, heq⟩ := wstep5.1 hw
      have hmw : m' (peA (m (atA ksb hi5)) i) = m (peA (m (atA ksb hi5)) i) := by
        rcases hz _ (peA_al_sets hVP hPP hpm hi') with e | e
        · exact e
        · exact absurd e hne0
      have h0' := hgone rfl hi5 i (by omega) (by omega) h0 (by rw [← hmw]; exact heq) (by rw [← hmw]; exact htag)
      exact hne0 h0'

/-- **(f4g) `VsPend` after a final ASID pool cap's `delete_asid_pool`** (the window: the ASID
table no longer names the pool, so `VsNamed` fails at the pool's slot until its `empty_slot`): zero
writes, only the table word at the pool's base changed, and not to the pool; the cap the only one of
its key (finality). -/
theorem VsNamed.pendPool (hN : VsNamed th m ksb) (hS : VsSlotsW th P L4 L3 L2 L1 m) (hVP : VsPlaced P ksb)
    (hPP : PtPlaced L4 L3 L2 L1) (hR : VsRel P m ksb σ) (hPt : PtRel L4 L3 L2 L1 m σ) (hPI : PoolsIn P L4 m)
    (hc : ∀ y, IsSlot th y → capV m' y = capV m y) (hz : ∀ b, Aligned b → m' b = m b ∨ m' b = 0#u64)
    {x : U64} (hx : IsSlot th x) {q b : U64} (hcx : capV m x = .AsidPool q b)
    (hd1 : ∀ c, Aligned c → (∀ hi : U64, hi.val = b.val / 512 % 2048 → c ≠ atA ksb hi) → m' c = m c)
    (hd2 : ∀ hi : U64, hi.val = b.val / 512 % 2048 → m' (atA ksb hi) ≠ q)
    (huq : ∀ y, IsSlot th y → y ≠ x → VKey (capV m y) ≠ VKey (capV m x)) : VsPend th m' ksb x := by
  have hAl : ∀ hi : U64, hi.val < 2048 → Aligned (atA ksb hi) := fun hi hh => by
    have hv := atA_val hVP.ksb_fit hh; have := hVP.ksb_al; unfold Aligned; rw [hv]; omega
  have hcwx := hS x hx
  rw [hcx] at hcwx
  simp only [VCapW, VCapOK] at hcwx
  obtain ⟨-, hb5, hb20⟩ := hcwx
  refine hN.pend hc (fun hi hh => hz _ (hAl hi hh)) ?_ ?_ ?_ ?_
  · intro k p a v i hp _ _ hi
    have hm := lvl_mem (hp.mem hR hPt hPI)
    rcases hz _ (peA_al_sets hVP hPP hm (lt_of_lt_of_le hi (bnd_le k))) with e | e
    · exact .inl (by rw [e])
    · exact .inr (by rw [e]; exact wstep_zero k)
  · intro y hy _ hu k q' hk i hi
    have hq := lvl_mem (hS.need hy (vneed_of_un hu hk))
    rcases hz _ (peA_al_sets hVP hPP hq (lt_of_lt_of_le hi (bnd_le k))) with e | e
    · rw [e]; exact hN.empty y hy hu k q' hk i (by unfold bnd at hi; exact hi)
    · rw [e]; simp [eP]
  · intro y hy hyx q' b' hb' hi hib
    have hcw := hS y hy
    rw [hb'] at hcw
    have hh := (pool_hi hcw (by omega)).1
    by_cases e : hi.val = b.val / 512 % 2048
    · exfalso
      have h1 := hN.poolT y hy q' b' hb' hi hib
      have h2 := hN.poolT x hx q b hcx hi (by omega)
      apply huq y hy hyx
      rw [hb', hcx]
      show some (5, q') = some (5, q)
      rw [← h1, h2]
    · rw [hd1 _ (hAl hi hh) (fun hi' hh' heq => e (by
        have v1 := atA_val hVP.ksb_fit hh
        have v2 := atA_val hVP.ksb_fit (show hi'.val < 2048 by omega)
        have := congrArg UScalar.val heq
        rw [v1, v2] at this; omega))]
      exact hN.poolT y hy q' b' hb' hi hib
  · intro k q' a v hp hr
    exfalso
    obtain ⟨hk, hrf⟩ := hr
    rw [hcx] at hk hrf
    simp only [VKey, Option.some.injEq, Prod.mk.injEq] at hk
    obtain ⟨rfl, hq⟩ := hk
    have ha : b.val = a := by
      simp only [VRefOf, Option.some.injEq, Prod.mk.injEq] at hrf; omega
    cases hp with
    | @tbl hi hh h0 => exact hd2 hi (by omega) hq.symm

/-- **(F1 stage 5) `VsNamed` across a VSpace step with its `VsOpF`** (the
per-operation facts; `hUq`, the cap the only one of its key, for a table
Unmap, from the decode's final check). -/
theorem VsNamed.ofOpF (hN : VsNamed th m ksb) (hS : VsSlotsW th P L4 L3 L2 L1 m)
    (hR : VsRel P m ksb σ) (hPt : PtRel L4 L3 L2 L1 m σ) (hPI : PoolsIn P L4 m) (hPP : PtPlaced L4 L3 L2 L1)
    (hR' : VsRel P m' ksb σ') (hPt' : PtRel L4 L3 L2 L1 m' σ')
    {x : U64} (hx : IsSlot th x) {c : capability.Cap} (hc : capV m x = c) (hSF : SlotFoot th m m' x)
    (hF : VsOpF m m' x c σ σ')
    (hUq : finF m x = true → VKey (capV m x) ≠ none → ∀ y, IsSlot th y → y ≠ x → VKey (capV m y) ≠ VKey (capV m x)) :
    VsNamed th m' ksb := by
  rcases hF with h | h | h | h | h | h | h
  · exact hN.ofPdptMapF hS hR hPt hPI hR' hPt' hx hc hSF h
  · exact hN.ofPdMapF hS hR hPt hPI hR' hPt' hx hc hSF h
  · exact hN.ofPtMapF hS hR hPt hPI hR' hPt' hx hc hSF h
  · exact hN.ofAssignF hS hR hPt hPI hPP hR' hPt' hx hc hSF h
  · exact hN.ofMapLeafF hS hR hPt hPI hR' hPt' hc hSF h
  · exact hN.ofUnmapLeafF hS hR hPt hPI hR' hPt' hc hSF h
  · refine hN.ofUnmapTabF hS hR hPt hPI hR' hPt' hx hc hSF h.1 (hUq h.2 ?_)
    obtain ⟨-, q0, mp, a0, v0, hcase, -⟩ := h.1
    rw [hc]
    rcases hcase with ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ <;> rw [e] <;> simp [VKey]

end

end

end Fl4Proofs.P3.Vs
