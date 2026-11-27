/-
P3 (DESIGN.md §9), scheduler, g7d (KENTRY-PLAN g7c-2 1., INV-PLAN §1.U3L D2):
**the guard of `ArchSwF`**. `VsRootOK T σ`: every TCB of `T` whose vtable is a
mapped PML4 cap has a nonzero ASID (l4v `valid_cap` of a mapped PML4 cap), and
every ASID-table entry names an ASID pool (l4v `valid_asid_table`). Under it
the spec's `setVmRoot t` (`findVspaceForAsid`: `assertE (asid > 0)`,
`getAsidPool`) cannot fail for `t ∈ T`; without it `ArchSwF` was unsatisfiable
(g6b audit, INV-PLAN §1.U3L.H D2).

* `VsRootOK.of_heap`: kept when the heap's TCB vtables and pools and the ASID
  table are kept.
-/
import Fl4Proofs.P3.VsRel
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core

/-- **The vspace-root facts a thread switch needs** (module docstring). -/
def VsRootOK (T : Set U64) (σ : Fl4Spec.State Unit) : Prop :=
  (∀ t ∈ T, ∀ x : Fl4Spec.Tcb, σ.kheap t.bv = some (.tcb x) → ∀ p a,
      x.tcbVtable = .archObjectCap (.pml4Cap p (some a)) → a ≠ 0) ∧
  (∀ i p, σ.archState.x64AsidTable i = some p → ∃ f, σ.kheap p = some (.archObj (.asidPool f)))

theorem VsRootOK.of_heap {T : Set U64} {σ σ' : Fl4Spec.State Unit} (h : VsRootOK T σ)
    (hk : ∀ p, σ'.kheap p = σ.kheap p ∨ ∃ x y, σ.kheap p = some (.tcb x) ∧ σ'.kheap p = some (.tcb y) ∧
      y.tcbVtable = x.tcbVtable)
    (ha : σ'.archState.x64AsidTable = σ.archState.x64AsidTable) : VsRootOK T σ' := by
  refine ⟨fun t ht y hy p a hv => ?_, fun i p hi => ?_⟩
  · rcases hk t.bv with e | ⟨x, y', hx, hy', ev⟩
    · rw [e] at hy; exact h.1 t ht y hy p a hv
    · rw [hy] at hy'; cases hy'
      exact h.1 t ht x hx p a (by rw [← ev]; exact hv)
  · rw [ha] at hi
    obtain ⟨f, hf⟩ := h.2 i p hi
    rcases hk p with e | ⟨x, y', hx, -, -⟩
    · exact ⟨f, by rw [e]; exact hf⟩
    · rw [hf] at hx; cases hx

theorem VsRootOK.of_eq {T : Set U64} {σ σ' : Fl4Spec.State Unit} (h : VsRootOK T σ)
    (hk : σ'.kheap = σ.kheap) (ha : σ'.archState.x64AsidTable = σ.archState.x64AsidTable) : VsRootOK T σ' :=
  h.of_heap (fun p => Or.inl (congrFun hk p)) ha

end Fl4Proofs.P3.Sched
