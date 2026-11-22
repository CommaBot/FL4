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

/-- **(F1 stage 5) `VsNamed` across a VSpace step with its `VsOpF`** (the
operations whose facts are exported; `hTodo` for the rest, KENTRY-PLAN f4). -/
theorem VsNamed.ofOpF (hN : VsNamed th m ksb) (hS : VsSlotsW th P L4 L3 L2 L1 m)
    (hR : VsRel P m ksb σ) (hPt : PtRel L4 L3 L2 L1 m σ) (hPI : PoolsIn P L4 m) (hPP : PtPlaced L4 L3 L2 L1)
    (hR' : VsRel P m' ksb σ') (hPt' : PtRel L4 L3 L2 L1 m' σ')
    {x : U64} (hx : IsSlot th x) {c : capability.Cap} (hc : capV m x = c) (hSF : SlotFoot th m m' x)
    (hF : VsOpF m m' x c σ σ') (hTodo : VsOpTodo → VsNamed th m' ksb) : VsNamed th m' ksb := by
  rcases hF with h | h | h | h | h | h | h
  · exact hN.ofPdptMapF hS hR hPt hPI hR' hPt' hx hc hSF h
  · exact hN.ofPdMapF hS hR hPt hPI hR' hPt' hx hc hSF h
  · exact hN.ofPtMapF hS hR hPt hPI hR' hPt' hx hc hSF h
  · exact hN.ofAssignF hS hR hPt hPI hPP hR' hPt' hx hc hSF h
  · exact hN.ofMapLeafF hS hR hPt hPI hR' hPt' hc hSF h
  · exact hN.ofUnmapLeafF hS hR hPt hPI hR' hPt' hc hSF h
  · exact hTodo h

end

end

end Fl4Proofs.P3.Vs
