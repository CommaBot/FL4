/-
P3 (line p3J, gen 9): **the idle half of `ArchSwF` is a theorem where it is used**.

`ArchSwF` [P] (ScArchF) has a thread half (`set_vm_root` against `archSwitchToThread`) and an idle half
(`set_kernel_vm_root` against `archSwitchToIdleThread` = `setVmRoot idleThread`), both asked at every
related state. The idle half is false as stated wherever the idle TCB's vtable is a mapped PML4 cap (the
spec then switches to that PML4, FL4 to the kernel root), which `SchedRel`/`NtfnStateRel`/`VsRootOK` do not
exclude. Its only use on the U-chain is G7eChain's `scnt_refines0FA`, at states where `RootFr` (hence
`RootOK.idle` = `IdleVt`) is carried.

* Collapse A, K: `ArchSwFT` (the thread half, verbatim) and **`ArchSwFI`** (the idle half with one more
  antecedent `IdleVt σ`: the idle TCB is in the heap and its vtable is no mapped PML4 cap) are in ScArchF, and
  `ArchSwF := ArchSwFT ∧ ArchSwFI` there (gen 9's `ArchSwF'`, written back in place). G7eChain's
  `scnt_refines0FA` / `sw_refinesFA` take gen 9's re-proofs (the two idle instances `hO.now.idle` and
  `(hO _ _ hwN haK.1 hcN).idle`). The pre-g7e scheduler chain (ScNextDomF's `scnt_refines0F`, ScNextDomCF,
  ScNextDomCFR's `schedule_refinesWP0FR`, ScScheduleF's `sw_refinesF`), which applied the old idle half at states
  without `IdleVt`, had no user left and is removed, with gen 9's `scnt_refines0FI` / `sw_refinesFI`.
* **`archSwFI_of : P0.ArchTotal ar → ArchSwFI st ar N T C c`** at every ghost set: no opaque step is
  involved. The spec's `setCurrentCr3` is a plain state update (VSpace.lean, l4v `set_current_cr3`), so
  `archSwitchToIdleThread σ` has the single outcome `cr3Upd σ (globCr3 σ)` (VsRoot's `setVmRoot_other`);
  FL4's `set_kernel_vm_root` keeps the store (`set_kernel_vm_root_s`) and is total (P0, `ArchTotal`);
  `SchedRel` / `NtfnStateRel` / `ArchKeeps` across a CR3-only change (`SchedRel.fpu`, `NtfnStateRel.fpu`).
  So there is no CR3-write determinism premise: the idle half is removed outright. `ArchSwFT.toN`: the thread
  half gives `ArchSwF`.

Named premises: none new (`ArchSwFT` is `ArchSwF`'s thread half, [P] where it is assumed). No sorry.
-/
import Fl4Proofs.P3.G7eChain
import Fl4Proofs.P3.ScFpuNd
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3 Fl4Proofs.P3.Vs

noncomputable section

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]

/-- The spec's idle switch at an `IdleVt` state: CR3 to the global PML4, nothing else. -/
theorem archSwitchToIdle_eq {σ : Fl4Spec.State Unit} (hIV : IdleVt σ) :
    Fl4Spec.archSwitchToIdleThread (Z := Unit) σ = ({((), cr3Upd σ (globCr3 σ))}, False) := by
  obtain ⟨x, hx, hv⟩ := hIV
  unfold Fl4Spec.archSwitchToIdleThread
  rw [nd_gets_bind]
  exact setVmRoot_other hx hv

theorem archKeeps_cr3 (σ : Fl4Spec.State Unit) (c : Fl4Spec.Cr3) : ArchKeeps σ (cr3Upd σ c) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **The idle half is a theorem** (module docstring). -/
theorem archSwFI_of (hAT : P0.ArchTotal ar) {N T C : Set U64} {c : U64} : ArchSwFI st ar N T C c := by
  intro s a σ hS hR _ hIV
  have hSt : P0.StoreTotal st := P1.LawfulStore.total
  have hk := archKeeps_cr3 σ (globCr3 σ)
  refine WP.spec_mono (P1.spec_eq' (Fl4Proofs.P0.vspace.set_kernel_vm_root.p0 st ar s a hSt hAT)) ?_
  rintro r ⟨hr, -⟩
  rw [set_kernel_vm_root_s hr]
  exact ⟨_, archSwitchToIdle_eq hIV, hS.fpu (ArchKeeps.toF hk) rfl, hR.fpu (ArchKeeps.toF hk).1, hk⟩

theorem ArchSwFT.toN (hAT : P0.ArchTotal ar) {N T C : Set U64} {c : U64} (h : ArchSwFT st ar N T C c) :
    ArchSwF st ar N T C c :=
  ⟨h, archSwFI_of hAT⟩

end

end

end Fl4Proofs.P3.Sched
