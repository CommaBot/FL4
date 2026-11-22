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

/-- **(F1 stage 5) `VsNamed` across a VSpace step with its `VsOpF`** (the
operations whose facts are exported; `hTodo` for the rest, KENTRY-PLAN f4). -/
theorem VsNamed.ofOpF (hN : VsNamed th m ksb) (hS : VsSlotsW th P L4 L3 L2 L1 m)
    (hR : VsRel P m ksb σ) (hPt : PtRel L4 L3 L2 L1 m σ) (hPI : PoolsIn P L4 m) (hPP : PtPlaced L4 L3 L2 L1)
    (hR' : VsRel P m' ksb σ') (hPt' : PtRel L4 L3 L2 L1 m' σ')
    {x : U64} (hx : IsSlot th x) {c : capability.Cap} (hc : capV m x = c) (hSF : SlotFoot th m m' x)
    (hF : VsOpF m m' x c σ σ') (hTodo : VsOpTodo → VsNamed th m' ksb) : VsNamed th m' ksb := by
  rcases hF with h | h | h | h | h
  · exact hN.ofPdptMapF hS hR hPt hPI hR' hPt' hx hc hSF h
  · exact hN.ofPdMapF hS hR hPt hPI hR' hPt' hx hc hSF h
  · exact hN.ofPtMapF hS hR hPt hPI hR' hPt' hx hc hSF h
  · exact hN.ofAssignF hS hR hPt hPI hPP hR' hPt' hx hc hSF h
  · exact hTodo h

end

end

end Fl4Proofs.P3.Vs
