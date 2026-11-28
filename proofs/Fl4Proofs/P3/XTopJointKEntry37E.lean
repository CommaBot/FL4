/-
P3 (DESIGN.md §9), invariant line g5c (KENTRY-PLAN g5c; g5b's handoff):
**`kernel_entryJ37E`** = `kernel_entryJ36E` whose exit also carries l4v
`valid_ioports` ∧ `ioports_no_overlap`, and the induction **`JReachIP` /
`jreach_invIP` / `kernel_entry_reachIP`** whose step no longer asks
`SpecIoP` of the exit.

`SpecIoP` (l4v `valid_ioports`) is not inductive alone: deleting the final
IO-port cap of a range frees the whole range (`empty_slot` →
`arch_post_cap_deletion` → `free_ioport_range`), while finality compares only
the first port. With l4v's `ioports_no_overlap` (`SInvIo.IoNoOverlap`: two
IO-port caps with overlapping ranges have equal ranges) the pair is kept by
every syscall entry and every event (SpecInvIoPortsS's `kentry_ioi` /
`kcall_ioi`, spec side, no side condition; `boot_ioi` at the spec's initial
state). So `JReachIP` starts from `JAtZ ∧ SInvX ∧ SpecIoP ∧ IoNoOverlap ∧
SpecUtZ ∧ MR` and its step asks only **`SpecUtZ σ'`** (l4v
`untyped_ranges_zero`, [J] spec) of the exit: the one open carry left of g5b's
`SInvIR`. `FlagsRel` and `LargeFrOK` stay per-state premises of
`kernel_entry_reachIP` at the entry (as in `kernel_entry_reachI`; their carry
is not done, KENTRY-PLAN g5c).
-/
import Fl4Proofs.P3.XTopJointKEntry36E
import Fl4Proofs.P3.SpecInvIoPortsS
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.SInvIo
open Fl4Spec Fl4Proofs.P3

/-! ## `IOI` as g5a's `SpecIoP` with `IoNoOverlap` -/

theorem has_iff_capAt {σ : State Unit} {f l : IoPort} :
    Has σ f l ↔ ∃ sl, SInvU.capAt σ sl = some (.archObjectCap (.ioPortCap f l)) := by
  unfold Has
  constructor
  · rintro ⟨p, cref, h⟩; exact ⟨(p, cref), by rw [SInv.vfh_capAt]; exact h⟩
  · rintro ⟨⟨p, cref⟩, h⟩; exact ⟨p, cref, by rw [SInv.vfh_capAt] at h; exact h⟩

theorem ioi_iff {σ : State Unit} : IOI σ ↔ SInvR.G5.SpecIoP σ ∧ IoNoOverlap σ := by
  constructor
  · intro h
    refine ⟨fun sl f l hc => h.1 f l (has_iff_capAt.2 ⟨sl, hc⟩), fun sl sl' f l f' l' h1 h2 ho =>
      h.2 f l f' l' (has_iff_capAt.2 ⟨sl, h1⟩) (has_iff_capAt.2 ⟨sl', h2⟩) ho⟩
  · rintro ⟨h1, h2⟩
    refine ⟨fun f l hh => ?_, fun f l f' l' a b ho => ?_⟩
    · obtain ⟨sl, hc⟩ := has_iff_capAt.1 hh; exact h1 sl f l hc
    · obtain ⟨sl, hc⟩ := has_iff_capAt.1 a
      obtain ⟨sl', hc'⟩ := has_iff_capAt.1 b
      exact h2 sl sl' f l f' l' hc hc' ho

/-- **`SpecIoP ∧ IoNoOverlap` across a whole syscall entry** (no side condition). -/
theorem kentry_ioi {rep : Bool} {c : Syscall} {σ : State Unit} (h : SInvR.G5.SpecIoP σ ∧ IoNoOverlap σ) :
    ∀ y ∈ ((fl4KernelEntrySyscall (Z := Unit) rep c σ).1), SInvR.G5.SpecIoP y.2 ∧ IoNoOverlap y.2 :=
  fun y hy => ioi_iff.1 (ioi_fl4KernelEntrySyscall rep c σ (ioi_iff.2 h) y hy)

/-- **The same across every event** (`fl4CallKernel rep ev`). -/
theorem kcall_ioi {rep : Bool} {ev : Event} {σ : State Unit} (h : SInvR.G5.SpecIoP σ ∧ IoNoOverlap σ) :
    ∀ y ∈ ((fl4CallKernel (Z := Unit) rep ev σ).1), SInvR.G5.SpecIoP y.2 ∧ IoNoOverlap y.2 :=
  fun y hy => ioi_iff.1 (ioi_fl4CallKernel rep ev σ (ioi_iff.2 h) y hy)

/-- The spec's initial state holds no IO-port cap (non-vacuity check, INV-PLAN lead decision). -/
theorem boot_ioi : SInvR.G5.SpecIoP (initASt (Z := Unit)) ∧ IoNoOverlap (initASt (Z := Unit)) :=
  ioi_iff.1 ⟨fun f l hh => absurd hh (boot_noIo f l), fun f l _ _ hh => absurd hh (boot_noIo f l)⟩

end Fl4Proofs.P3.SInvIo

namespace Fl4Proofs.P3.SInvR.G5
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {MR : A → Fl4Spec.MachineState → Prop}

/-- The spec facts carried by `JReachIP` beside `SInvX`: `valid_ioports`,
`ioports_no_overlap`, `untyped_ranges_zero`. -/
structure SInvIP (σ : Fl4Spec.State Unit) : Prop where
  ioP : SpecIoP σ
  ioN : SInvIo.IoNoOverlap σ
  utZ : SpecUtZ σ

theorem SInvIP.toIR {σ : Fl4Spec.State Unit} (h : SInvIP σ) : SInvIR σ := ⟨h.ioP, h.utZ⟩

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)

/-- **The reachable joint states with `SInvIP`** (module docstring): `start`
from `JAtZ ∧ SInvX ∧ SInvIP ∧ MR`; `step` along `RJM` with `SpecUtZ` of the
exit (the open carry; `SpecIoP ∧ IoNoOverlap` are carried, `kentry_ioi`). -/
inductive JReachIP : S → A → Fl4Spec.State Unit → Prop
  | start {s : S} {a : A} {σ : Fl4Spec.State Unit} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
      {Lst : U64 → List U64} {D : Set U64} :
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → SInvX σ → SInvIP σ → MR a σ.machineState → JReachIP s a σ
  | step {s : S} {a : A} {σ : Fl4Spec.State Unit} {s' : S} {a' : A} {σ' : Fl4Spec.State Unit} (n : I64)
      (c : Fl4Spec.Syscall) :
      JReachIP s a σ → σ.curThread ≠ σ.idleThread → NativeSys n c →
      syscall.handle_syscall st arI s a n = ok (s', a') →
      ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 →
      RJM (L := L) arI AR MR s' a' σ' → SpecUtZ σ' → JReachIP s' a' σ'

variable {arI AR MR}

end

end

end Fl4Proofs.P3.SInvR.G5
