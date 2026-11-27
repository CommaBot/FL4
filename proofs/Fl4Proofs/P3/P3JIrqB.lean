/-
P3 (p3J gen 38): **`SpecIrqB` discharged on every `RunMcWKR` state; the top without it.**

Finding: gen 37's `SpecIrqB` [J] was already carried. `RunMcWKR` unfolds to `RunCK = JReachU40 ∧ CKI` with
`JReachU40 = JReachU36I ∧ IoaRel` and `JReachU36I = JReachU17 ∧ IrqCarry` (XTopJointKEntryU36I / U40): irqfix
gen 3's carried IRQ fact `IrqCarry σ := IrqStB σ ∨ (IrqStS σ ∧ ValidIrqHandlersL σ)` (SpecInvIrqStS), kept by every
clause (`EvOut.irqCarry`, `kentry_irqCarry`) and true at the 2-core boot witness (that is how `runMcWKR_w2` is
proved). With the port's `ValidIrqHandlers` (in `SInvX`, `hX.sb.1.1.vih`) it gives SpecInvIrqBoundKit's
`IrqCapBound σ` (l4v `valid_cap` for `IRQHandlerCap irq`: `irq ≤ maxIRQ`, `IrqCarry.capBound`), which is
`SpecIrqB σ` read through `BitVec.le_def`.

* **`specIrqB_of_capBound`**: `IrqCapBound σ → SpecIrqB σ`.
* **`specIrqB_run`**: `RunMcWKR s a σ → SpecIrqB σ` (no premise beyond `numDomains = 1`, a global of every top).
* **`DispStabFootLs` [J]**: gen 37's `DispStabFootLq` without its `irqB` field (the other four fields verbatim).
* **`dispStabFootLq_of_Ls`**: `DispStabFootLs → DispStabFootLq` (the `irqB` field by `specIrqB_run`), and
  **`dispStabFootLs_of_Lq`** (the converse, field projection): the two are equivalent.
* Top **`kernel_entry_runMcWKR_sysLs`**: `_sysLq`'s statement with `hLq` ↦ `hLs : DispStabFootLs`.

Premise honesty: `DispStabFootLs` = `DispStabFootLq` minus `irqB`, so implied by `DispStabFootLq` (and equivalent
to it, `dispStabFootLq_of_Ls`). It is `DispStabFootLo` with the decode fields at the smaller cap predicate
`IsRestCap3` (CNode, Thread, SchedContext): implied by `DispStabFootLo` (P3JCapIrqTop's `restCap_of3`).

Named premises: `DispStabFootLs` [J]. No sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P3.P3JCapIrqTop
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

/-- (p3J gen 38) **l4v `valid_cap`'s handler-cap bound gives `SpecIrqB`** (module docstring). -/
theorem specIrqB_of_capBound {σ : Fl4Spec.State Unit} (h : SInvIB.IrqCapBound σ) : SpecIrqB σ :=
  fun p cref i hc => BitVec.le_def.1 (h p cref i hc)

end Fl4Proofs.P3

namespace Fl4Proofs.P3.Mc
open fl4_core Classical Fl4Spec Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P2.Wit
open Fl4Proofs.P3.JBoot Fl4Proofs.P3.SInvR.G5 Fl4Proofs.P3.Vs Fl4Proofs.P3.JBootQ
open Fl4Proofs.P3.SInvR.G4

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)

/-- (p3J gen 38) **`DispStabFootLs` [J]**: gen 37's `DispStabFootLq` without `irqB` (module docstring). -/
structure DispStabFootLs (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop where
  /-- `DispStabFootLq.invDecRest`, verbatim. -/
  invDecRest : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (call bl don : Bool),
        σ.curThread ≠ σ.idleThread → InvSys n call bl don → SysFlag (L := L) s →
        SysK6 (L := L) arI AR Z H Cs s a σ n (invSysOf call bl) →
        InvDecStW (L := L) arI AR MR (fun cp => SInvCk.KW (absCap cp) ∧ IsRestCap3 cp) Z H Cs s a σ n call bl don
  /-- `DispStabFootLq.midDecRest`, verbatim. -/
  midDecRest : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (c : Fl4Spec.Syscall),
        σ.curThread ≠ σ.idleThread → MidSys n c → SysFlag (L := L) s → SysK6 (L := L) arI AR Z H Cs s a σ n c →
        MidDecStW (L := L) arI AR MR (fun cp => SInvCk.KW (absCap cp) ∧ IsRestCap3 cp) Z H Cs s a σ n c
  /-- `DispStabFootLq.midSpec`, verbatim. -/
  midSpec : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (c : Fl4Spec.Syscall),
        σ.curThread ≠ σ.idleThread → MidSys n c → SysFlag (L := L) s → SysK6 (L := L) arI AR Z H Cs s a σ n c →
        MidSpecAt σ
  /-- `DispStabFootLq.midRecvSw`, verbatim. -/
  midRecvSw : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (c : Fl4Spec.Syscall),
        σ.curThread ≠ σ.idleThread → MidSys n c → SysFlag (L := L) s → SysK6 (L := L) arI AR Z H Cs s a σ n c →
        MidRecvSw (L := L) arI AR MR Z H Cs s a σ n c

variable {arI AR MR}

/-- (p3J gen 38) **`SpecIrqB` at every `RunMcWKR` state** (module docstring: the carried `IrqCarry` and
`SInvX`'s `ValidIrqHandlers`). -/
theorem specIrqB_run (hnd : Fl4Spec.numDomains = 1) {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (hR : RunMcWKR (L := L) arI AR MR s a σ) : SpecIrqB σ := by
  obtain ⟨⟨⟨⟨⟨hJ17, hC⟩, -⟩, -⟩, -⟩, -⟩ := hR.1.1
  obtain ⟨_, _, _, _, _, _, -, hX, -⟩ := jreach_invU3 hnd hJ17.1
  exact specIrqB_of_capBound (SInvIB.IrqCarry.capBound hX.sb.1.1.vih hC)

/-- (p3J gen 38) **`DispStabFootLs → DispStabFootLq`** (`irqB` by `specIrqB_run`). -/
theorem dispStabFootLq_of_Ls (hnd : Fl4Spec.numDomains = 1) {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (h : DispStabFootLs (L := L) arI AR MR s a σ) : DispStabFootLq (L := L) arI AR MR s a σ where
  invDecRest := h.invDecRest
  midDecRest := h.midDecRest
  midSpec := h.midSpec
  midRecvSw := h.midRecvSw
  irqB := specIrqB_run hnd

/-- (p3J gen 38) **`DispStabFootLq → DispStabFootLs`** (the two are equivalent). -/
theorem dispStabFootLs_of_Lq {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (h : DispStabFootLq (L := L) arI AR MR s a σ) : DispStabFootLs (L := L) arI AR MR s a σ where
  invDecRest := h.invDecRest
  midDecRest := h.midDecRest
  midSpec := h.midSpec
  midRecvSw := h.midRecvSw

set_option maxHeartbeats 4000000 in
/-- (p3J gen 38) **The native syscall entry, `RunMcWKR` to `RunMcWKR`, with `DispStabFootLs` only** (`hLs` [J];
module docstring). -/
theorem kernel_entry_runMcWKR_sysLs [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR)
    (hKD : MRKeepD arI MR)
    (hPAi : ∀ a c, AR a c → arI.irq_pending a ⦃ r => AR r.2 c ⦄)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    (hFpu : FpuImplDet) (hFW : FpuWriteDet)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hR : RunMcWKR (L := L) arI AR MR s a σ)
    (hLs : DispStabFootLs (L := L) arI AR MR s a σ) :
    ∀ (n : I64) (c : Fl4Spec.Syscall), σ.curThread ≠ σ.idleThread → NativeSys n c → SysFlag (L := L) s →
      (∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
        JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → SysK6 (L := L) arI AR Z H Cs s a σ n c) →
      syscall.handle_syscall st arI s a n ⦃ r =>
        ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧
          RunMcWKR (L := L) arI AR MR r.1 r.2 σ' ⦄ :=
  kernel_entry_runMcWKR_sysLq hARI hA hnd hM hIp hKD hPAi hT hmax htu hRef hSX hDR hFpu hFW hR
    (dispStabFootLq_of_Ls hnd hLs)

end

end Fl4Proofs.P3.Mc
