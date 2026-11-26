/-
P3 (line jboot, gen 6): **two facts that FL4's real boot meets and the joint invariants do not** (jboot.md
gen 6: scope check of a JAtZ / JReachU34 witness at the state FL4's boot code produces).

* **`irqStB_false_of_ipiWord`**: FL4's boot (`boot::init_root_cnode` → `init_irq_states`,
  crates/fl4-core/src/arch/x86_64/boot.rs l.77–90) writes `IRQ_IPI` (= 3) into the IRQ-state words of lines
  `REMOTE_CALL_IPI = 126` and `RESCHEDULE_IPI = 127` (arch/x86_64/layout.rs l.119–120). `IrqRel.st` makes the spec's
  `interruptStates 126` equal `irqSt 3 = irqReserved` (IntRel `irqSt`), while irqfix's `IrqStB` (U34's start
  conjunct in `JReachU34`) asks every line above `maxIRQ = 125` to be `irqInactive`. So no spec state related to
  FL4's real boot image is a `JReachU34` state; jboot's witnesses `w0` / `w1` have those words 0, which FL4's boot
  never produces.
* **`idle2_not_sinvX`** (the 2-core obstacle): a related TCB (`NtfnStateRel.tcb`, `TcbRel1.st`) whose state word is
  `TS_IDLE` (7) and that is not the spec's `idleThread` makes `SInvX` false (its `SInvAll.OnlyIdle`, l4v
  `only_idle`, via `SInvX.sb`). FL4's boot gives every core its own idle TCB in state `TS_IDLE`
  (crates/fl4-core/src/boot.rs l.677–704, `create_idle_threads` / `create_idle_thread`), and the single-core spec
  has one `idleThread` (the current core's `IDLE_THREAD` word, `JAt.curIdle`).

No premise beyond the stated hypotheses; no sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P3.SpecInvIrqBoundKit
import Fl4Proofs.P3.XTopJointKEntry35
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.JBoot
open fl4_core Fl4Proofs.P3 Fl4Proofs.P3.Notif Fl4Proofs.P3.SInvR.G4

/-- **`IrqStB` is false at every spec state related to a memory whose line-126 IRQ-state word is `IRQ_IPI` (3)**
(module docstring; FL4's boot writes exactly that word). -/
theorem irqStB_false_of_ipiWord {mem : U64 → U64} {kb : U64} {σ : Fl4Spec.State Unit}
    (hR : IrqRel mem kb σ) (h : mem (irqStA kb 126#u64) = 3#u64) : ¬ SInvIB.IrqStB σ := by
  intro hB
  have h1 := hR.st 126#u64 (by decide)
  rw [h] at h1
  have h2 := hB (BitVec.ofNat 8 (126#u64).val) (by decide)
  rw [h1] at h2
  exact absurd ((irqSt_inactive _).1 h2) (by decide)

/-- A TCB state coded 7 is `idleThreadState`. -/
theorem tsCode_eq_idle {t : Fl4Spec.ThreadState} (h : tsCode t = 7) : t = .idleThreadState := by
  cases t <;> simp_all [tsCode]

/-- **A second related TCB in `TS_IDLE` breaks `SInvX`** (module docstring; `SInvAll.OnlyIdle`). -/
theorem idle2_not_sinvX {N T : Set U64} {m : U64 → U64} {σ : Fl4Spec.State Unit}
    (hN : NtfnStateRel N T m σ) {t : U64} (ht : t ∈ T) (h7 : (m (tStA t)).val = 7)
    (hne : t.bv ≠ σ.idleThread) : ¬ SInvX σ := by
  intro hX
  obtain ⟨x, hx, hr⟩ := hN.tcb t ht
  have hst : x.tcbState = .idleThreadState := tsCode_eq_idle (hr.st.symm.trans h7)
  exact hne ((SInvX.sb hX).2 t.bv x hx hst)

end Fl4Proofs.P3.JBoot
