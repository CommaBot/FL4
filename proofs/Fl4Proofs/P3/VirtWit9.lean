/-
P3x for virtualization (line virt, gen 9, item 2): **the virt top's own premises at the jboot witness** — the
FL4-side `hvirt` [P] and the spec-side start `NR` hold there, so `kernel_entry_reachV2/V3` is not vacuous on
account of them; what `hvk` [S] means at the witness.

* `hvirt_modelArch`, **`hvirt_warI`**: P3's `modelArch` and the witness arch `P2.Wit.warI` report no VT-x
  (`virtualization _ = ok 0`), by `rfl`. p3J's `warI1` (`{ warI with num_ioapics, ioapic_pins }`, JBootIoa, the
  arch of `u40_w1I1` / `u45nv_w1I1`) does not override `virtualization`, so the same `rfl` is p3J's
  `noVirt_warI1`; it is not restated here (JBootIoa is not on this branch's base int/j22).
* **`nr_fInit`** (`NR fInitASt`, jboot's boot state `w0` image) and **`nr_σ1`** (`NR σ1`, jboot's gen-4
  root-thread state, the image of `w1`): via VirtNvK2's `nr_boot` (`NoVirtCaps`, `NoVirtObjects`, `NoRunVM`),
  from the objects of the two heaps (idle TCB / SC, empty IRQ CNodes, the three global tables; plus the root TCB
  (`running`, caps: its CSpace-root CNode cap), root SC, root CNode (a thread cap and an SC cap)). `NR` reads only
  `kheap`; p3J's `JBootQ.σ1` (the `σ1` of `u40_w1I1`) is the gen-15 copy of this `σ1` that changes only the IRQ
  words / IRQ states of the boot state, not the heap objects, so the same proof applies verbatim there.
* `hvk : virtKind = .none` [S] at the witness: `virtKind` is `virtPlatform.kind` for the **opaque** spec constant
  `virtPlatform` (Ext/VirtBackend: "the backend FL4 selected at boot"), so it is neither provable nor refutable
  in the theory; `virtPlatform_none_exists` shows the premise is satisfiable (the `Inhabited` platform has kind
  `none`). Its content is the agreement between the spec's backend constant and FL4's report:
  **`hvk_of_agree`** (with `hvirt`, the agreement `∀ r, virtualization a = ok r → r.val = virtKind.code` gives
  `hvk`) and `agree_of_hvk` (conversely). At the witness, where FL4 reports 0, `hvk` says exactly "the spec is
  instantiated with the backend the witness platform runs" (no VT-x), i.e. a [P]-style platform agreement.

No new named premise; no [J]/[P]/[W]/[S]. New file only.
-/
import Fl4Proofs.P3.VirtNvK2
import Fl4Proofs.P3.JBoot1St
import Fl4Proofs.P3.JBootInv
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.VirtWit9
open Fl4Spec Fl4Proofs.P3 Fl4Proofs.P3.JBoot

noncomputable section

/-! ## `hvirt` at the witness arch -/

theorem hvirt_modelArch : ∀ a, Fl4Proofs.P3.modelArch.virtualization a = ok 0#u64 := fun _ => rfl

/-- **The witness arch reports no VT-x** (`hvirt` [P] holds at the jboot witness). -/
theorem hvirt_warI : ∀ a, Fl4Proofs.P2.Wit.warI.virtualization a = ok 0#u64 := fun _ => rfl

/-! ## `hvk`: satisfiable, and equivalent to the backend agreement given `hvirt` -/

theorem virtPlatform_none_exists : ∃ P : VirtPlatform, P.kind = .none := ⟨default, rfl⟩

theorem virtKind_none_of_code {k : VirtKind} (h : k.code = 0) : k = .none := by
  cases k <;> first | rfl | (simp [VirtKind.code] at h)

/-- **`hvk` from the backend agreement** (spec constant = FL4's report) and `hvirt`. -/
theorem hvk_of_agree {A : Type} (arI : fl4_core.machine.Arch A) (a : A) (hvirt : arI.virtualization a = ok 0#u64)
    (hag : ∀ r, arI.virtualization a = ok r → r.val = virtKind.code) : virtKind = .none :=
  virtKind_none_of_code (by have := hag _ hvirt; rw [← this]; rfl)

/-- **The backend agreement from `hvk` and `hvirt`.** -/
theorem agree_of_hvk {A : Type} (arI : fl4_core.machine.Arch A) (hvk : virtKind = .none)
    (hvirt : ∀ a, arI.virtualization a = ok 0#u64) :
    ∀ a r, arI.virtualization a = ok r → r.val = virtKind.code := by
  intro a r h
  rw [hvirt a] at h
  rw [← ok_inj h, hvk]
  rfl

/-! ## `NR` at the witness states -/

theorem notVirt_null : ¬ IsVirtCap .nullCap := fun h => h

theorem fInit_noVirtCaps : NoVirtCaps fInitASt := by
  intro p ko hk c hc hv
  obtain ⟨l, hl⟩ := hc
  rcases fInit_objs hk with rfl | rfl | rfl | rfl | rfl | rfl
  · have e : c = .nullCap := idleTcb_map hl
    subst e; exact hv
  · cases hl
  · have hl' : emptyCnode 0 l = some c := hl
    unfold emptyCnode at hl'
    split_ifs at hl'
    cases hl'; exact hv
  all_goals cases hl

theorem fInit_noVirtObjects : NoVirtObjects fInitASt := by
  intro p ao hk
  rcases fInit_objs hk with e | e | e | e | e | e <;> (try cases e) <;>
    exact ⟨fun _ h => (nomatch h), fun _ _ h => (nomatch h)⟩

theorem fInit_noRunVM : VirtR7d.NoRunVM fInitASt := by
  intro p x hk
  rcases fInit_objs hk with e | e | e | e | e | e <;> cases e
  intro h; cases h

/-- **`NR` at jboot's boot state.** -/
theorem nr_fInit : VirtR7e.NR fInitASt :=
  VirtNvK2.nr_boot fInit_noVirtCaps fInit_noVirtObjects fInit_noRunVM

theorem σ1_noVirtCaps : NoVirtCaps σ1 := by
  intro p ko hk c hc hv
  rcases kh1_some hk with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, -, -, h⟩
  · obtain ⟨l, hl⟩ := hc
    rcases rootTcb_map hl with ⟨-, rfl⟩ | rfl
    · exact hv
    · exact hv
  · obtain ⟨l, hl⟩ := hc
    cases hl
  · obtain ⟨l, hl⟩ := hc
    rcases rootCs_cases hl with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact hv
    · exact hv
  · exact fInit_noVirtCaps p ko h c hc hv

theorem σ1_noVirtObjects : NoVirtObjects σ1 := by
  intro p ao hk
  rcases kh1_some hk with ⟨-, e⟩ | ⟨-, e⟩ | ⟨-, e⟩ | ⟨-, -, -, h⟩
  · cases e
  · cases e
  · cases e
  · exact fInit_noVirtObjects p ao h

theorem σ1_noRunVM : VirtR7d.NoRunVM σ1 := by
  intro p x hk
  rcases kh1_some hk with ⟨-, e⟩ | ⟨-, e⟩ | ⟨-, e⟩ | ⟨-, -, -, h⟩
  · cases e; intro h; cases h
  · cases e
  · cases e
  · exact fInit_noRunVM p x h

/-- **`NR` at jboot's root-thread state `σ1`** (the start of the witness line). -/
theorem nr_σ1 : VirtR7e.NR σ1 :=
  VirtNvK2.nr_boot σ1_noVirtCaps σ1_noVirtObjects σ1_noRunVM

end

end Fl4Proofs.P3.VirtWit9
