/-
P3 (line irqfix, gen 3): **the IRQ line bound's carried fact, true at FL4's boot** (spec side only; outside the
`JAtZ` cone: SpecInvIrqBound and SpecInvVihLS).

gen 2's `IrqStB` (every line above `maxIRQ = 125` is `IRQInactive`) is false at FL4's boot: `init_irq_states`
(crates/fl4-core/src/arch/x86_64/boot.rs l.77–90) puts lines 126 / 127 in `IRQ_IPI`, which `IrqRel.st` maps to
`irqReserved` (jboot gen 6, `irqStB_false_of_ipiWord`). Here:

* **`IrqStS σ`**: no line above `maxIRQ` is `IRQSignal` (timer / reserved / inactive allowed). It has gen 2's
  bounded leaves (`wlb_irqStS`: `set_irq_state` only of `IRQInactive` or of a line `≤ maxIRQ`), so gen 2's `GKB`
  family keeps it across every entry (`kentry_irqStS`, `kcall_irqStS`, `fip_irqStS`, `budget_irqStS`).
* **`irqCapBound_of_L`**: l4v's `valid_irq_handlers` (`ValidIrqHandlersL`, a handler cap's line is in
  `IRQSignal`, SpecInvVihL) and `IrqStS` give `IrqCapBound`.
* **`IrqCarry σ := IrqStB σ ∨ (IrqStS σ ∧ ValidIrqHandlersL σ)`**, the carried fact of irqfix gen 3: the left
  disjunct is gen 2's (so U34's start states are covered), the right one holds at FL4's boot. Kept by every syscall
  entry (`kentry_irqCarry`), every event with or without the FaultIP write (`kcall_irqCarry`, `fipcall_irqCarry`),
  and at the dispatch state (`budget_irqCarry`); with the port's `ValidIrqHandlers` it gives `IrqCapBound`
  (`IrqCarry.capBound`). The right disjunct needs `ValidIrqMasks` at the start (SInvX carries it).
* Non-vacuity: `irqCarry_of_noHandler`; `irqStS_of_irqRel` (an `IrqRel` memory with the words FL4's boot writes
  at 126 / 127, `IRQ_IPI` = 3); the concrete state `fInitIpiASt` (jboot's `fInitASt` with line 125 `irqTimer`,
  126 / 127 `irqReserved`): `fInitIpi_irqCarry`, `fInitIpi_not_irqStB`.

No premise; no sorry.
-/
import Fl4Proofs.P3.SpecInvIrqBound
import Fl4Proofs.P3.SpecInvVihLS
import Fl4Proofs.P3.JBootSt
import Fl4Proofs.P3.IntRel

open Classical

namespace Fl4Proofs.P3.SInvIB
open Fl4Spec Fl4Proofs.P3 Fl4Proofs.P3.Vs Fl4Proofs.P3.MachF Fl4Proofs.P3.MachT Fl4Proofs.P3.SInvV

noncomputable section

/-- **No line above `maxIRQ` is `IRQSignal`** (module docstring). -/
def IrqStS (σ : State Unit) : Prop :=
  ∀ irq : Irq, maxIRQ < irq → σ.interruptStates irq ≠ .irqSignal

theorem irqStS_of_irqStB {σ : State Unit} (h : IrqStB σ) : IrqStS σ := fun irq hi e => by
  rw [h irq hi] at e; cases e

/-- **l4v's `valid_irq_handlers` and `IrqStS` give `IrqCapBound`.** -/
theorem irqCapBound_of_L {σ : State Unit} (hv : SInvVL.ValidIrqHandlersL σ) (hs : IrqStS σ) : IrqCapBound σ := by
  intro p cref irq hc
  by_contra hn
  exact hs irq (BitVec.not_le.1 hn) (hv p cref irq hc)

/-! ## The leaves -/

theorem ik_dmo_irqStS {α : Type} (mop : NonDet MachineState α) : IK IrqStS (doMachineOp (Z := Unit) mop) := by
  intro σ h x hx
  unfold doMachineOp at hx
  obtain ⟨⟨ms0, s1⟩, h1, ⟨⟨r, ms'⟩, s2⟩, h2, ⟨u, s3⟩, h3, hx⟩ := hx
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Set.mem_singleton_iff.1 h1)
  obtain ⟨-, e2⟩ := h2
  dsimp only at e2
  subst e2
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Set.mem_singleton_iff.1 h3)
  rw [Set.mem_singleton_iff.1 hx]
  exact h

theorem ik_sis_irqStS (st : IrqState) (i : Irq) (hb : st = .irqInactive ∨ i ≤ maxIRQ) :
    IK IrqStS (setIrqState (Z := Unit) st i) := by
  intro σ h x hx
  unfold setIrqState at hx
  obtain ⟨y, hy, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hy] at hx
  refine ik_dmo_irqStS _ _ ?_ x hx
  intro irq hirq
  show Function.update σ.interruptStates i st irq ≠ .irqSignal
  by_cases e : irq = i
  · subst e
    rw [Function.update_self]
    rcases hb with hb | hb
    · rw [hb]; exact fun h => by cases h
    · exact absurd hirq (BitVec.not_lt.2 hb)
  · rw [Function.update_of_ne e]; exact h irq hirq

/-- **`IrqStS` has the bounded leaves.** -/
theorem wlb_irqStS : WLB IrqStS where
  view σ σ' e h := by
    unfold vw at e; simp only [Prod.mk.injEq] at e
    intro irq hi; rw [e.2.2.1]; exact h irq hi
  uts σ h x hx := by
    obtain ⟨-, -, e, -⟩ := uts_out hx
    intro irq hi; rw [e]; exact h irq hi
  sisI i := ik_sis_irqStS _ i (Or.inl rfl)
  sisB st i hi := ik_sis_irqStS st i (Or.inr hi)
  msk mop _ := ik_dmo_irqStS mop
  ack i := ik_dmo_irqStS _

/-! ## Tops of `IrqStS` (gen 2's `GKB` family) -/

theorem kentry_irqStS (rep : Bool) (c : Syscall) {σ : State Unit} (h : IrqStS σ) :
    ∀ y ∈ ((fl4KernelEntrySyscall (Z := Unit) rep c) σ).1, IrqStS y.2 :=
  gkb_fl4KernelEntrySyscall rep c _ wlb_irqStS σ h

theorem kcall_irqStS (rep : Bool) (ev : Event) {σ : State Unit} (h : IrqStS σ) :
    ∀ y ∈ ((fl4CallKernel (Z := Unit) rep ev) σ).1, IrqStS y.2 :=
  gkb_fl4CallKernel rep ev _ wlb_irqStS σ h

theorem fip_irqStS (t : ObjRef) {σ : State Unit} (h : IrqStS σ) :
    ∀ y ∈ (fl4SyscallFaultIP (Z := Unit) t σ).1, IrqStS y.2 :=
  gkb_fl4SyscallFaultIP t _ wlb_irqStS σ h

theorem budget_irqStS {σ : State Unit} (h : IrqStS σ) :
    ∀ y ∈ ((updateTimeStamp (Z := Unit) >>= fun _ => checkBudgetRestart (Z := Unit)) σ).1, IrqStS y.2 :=
  gkb_budget _ wlb_irqStS σ h

/-! ## The carried fact -/

/-- **irqfix gen 3's carried fact** (module docstring). -/
def IrqCarry (σ : State Unit) : Prop :=
  IrqStB σ ∨ (IrqStS σ ∧ SInvVL.ValidIrqHandlersL σ)

/-- **`IrqCapBound` from the carried fact** (with the port's `ValidIrqHandlers`, which `SInvX` has). -/
theorem IrqCarry.capBound {σ : State Unit} (hv : ValidIrqHandlers σ) (h : IrqCarry σ) : IrqCapBound σ := by
  rcases h with h | ⟨hs, hl⟩
  · exact irqCapBound_of hv h
  · exact irqCapBound_of_L hl hs

/-- A step kept by gen 2's `GKB` family and by `VIL` keeps the carried fact (`ValidIrqMasks` at its start for
the right disjunct). -/
theorem irqCarry_step {α : Type} {m : NonDet (State Unit) α} (hg : GKB m) (hv : SInvV.IKH SInvVL.VIL m)
    {σ : State Unit} (hm : ValidIrqMasks σ) (h : IrqCarry σ) : ∀ y ∈ (m σ).1, IrqCarry y.2 := by
  intro y hy
  rcases h with h | ⟨hs, hl⟩
  · exact Or.inl (hg _ wlb_irqStB σ h y hy)
  · exact Or.inr ⟨hg _ wlb_irqStS σ hs y hy, (hv σ ⟨hm, hl, trivial⟩ y hy).2.1⟩

/-- **The carried fact across a syscall entry.** -/
theorem kentry_irqCarry (rep : Bool) (c : Syscall) {σ : State Unit} (hm : ValidIrqMasks σ) (h : IrqCarry σ) :
    ∀ y ∈ ((fl4KernelEntrySyscall (Z := Unit) rep c) σ).1, IrqCarry y.2 :=
  irqCarry_step (gkb_fl4KernelEntrySyscall rep c) (SInvVL.vil_fl4KernelEntrySyscall rep c) hm h

/-- **The carried fact across every kernel event.** -/
theorem kcall_irqCarry (rep : Bool) (ev : Event) {σ : State Unit} (hm : ValidIrqMasks σ) (h : IrqCarry σ) :
    ∀ y ∈ ((fl4CallKernel (Z := Unit) rep ev) σ).1, IrqCarry y.2 :=
  irqCarry_step (gkb_fl4CallKernel rep ev) (SInvVL.vil_fl4CallKernel rep ev) hm h

/-- The FaultIP write keeps the carried fact and, on the right disjunct, `ValidIrqMasks`. -/
theorem fip_irqCarry (t : ObjRef) {σ : State Unit} (hm : ValidIrqMasks σ) (h : IrqCarry σ)
    {w : Unit × State Unit} (hw : w ∈ (fl4SyscallFaultIP (Z := Unit) t σ).1) :
    IrqStB w.2 ∨ (ValidIrqMasks w.2 ∧ IrqStS w.2 ∧ SInvVL.ValidIrqHandlersL w.2) := by
  rcases h with h | ⟨hs, hl⟩
  · exact Or.inl (fip_irqStB t h w hw)
  · have e := SInvVL.vil_fl4SyscallFaultIP t σ ⟨hm, hl, trivial⟩ w hw
    exact Or.inr ⟨e.1, fip_irqStS t hs w hw, e.2.1⟩

/-- **The carried fact across the FaultIP write then an event.** -/
theorem fipcall_irqCarry (rep : Bool) (ev : Event) (t : ObjRef) {σ : State Unit} (hm : ValidIrqMasks σ)
    (h : IrqCarry σ) {w : Unit × State Unit} (hw : w ∈ (fl4SyscallFaultIP (Z := Unit) t σ).1) :
    ∀ y ∈ ((fl4CallKernel (Z := Unit) rep ev) w.2).1, IrqCarry y.2 := by
  intro y hy
  rcases fip_irqCarry t hm h hw with h1 | ⟨hm1, hs1, hl1⟩
  · exact Or.inl (kcall_irqStB rep ev h1 y hy)
  · exact kcall_irqCarry rep ev hm1 (Or.inr ⟨hs1, hl1⟩) y hy

/-- **The carried fact at the dispatch state** (FaultIP write, then the budget front). -/
theorem budget_irqCarry (t : ObjRef) {σ : State Unit} (hm : ValidIrqMasks σ) (h : IrqCarry σ)
    {w : Unit × State Unit} (hw : w ∈ (fl4SyscallFaultIP (Z := Unit) t σ).1) :
    ∀ y ∈ ((updateTimeStamp (Z := Unit) >>= fun _ => checkBudgetRestart (Z := Unit)) w.2).1, IrqCarry y.2 := by
  intro y hy
  rcases fip_irqCarry t hm h hw with h1 | ⟨hm1, hs1, hl1⟩
  · exact Or.inl (budget_irqStB h1 y hy)
  · exact irqCarry_step gkb_budget SInvVL.vil_budget hm1 (Or.inr ⟨hs1, hl1⟩) y hy

/-! ## Non-vacuity -/

/-- **A state with no IRQ handler cap and no `IRQSignal` line above `maxIRQ` carries the fact.** -/
theorem irqCarry_of_noHandler {σ : State Unit}
    (hn : ∀ p cref irq, capOpt (σ.kheap p) cref ≠ some (.irqHandlerCap irq)) (hs : IrqStS σ) : IrqCarry σ :=
  Or.inr ⟨hs, fun p cref irq hc => (hn p cref irq hc).elim⟩

theorem irqSt_signal (w : Aeneas.Std.U64) (e : irqSt w = .irqSignal) : w = 1#u64 := by
  unfold irqSt at e
  split_ifs at e with h0 h1 <;> first | exact h1 | cases e

/-- **`IrqStS` at a spec state related to FL4's boot IRQ words** (`IRQ_IPI` = 3 at lines 126 / 127, as
`init_irq_states` writes): the lines `≥ 128` (outside FL4's 128-entry table) are asked not to be `IRQSignal`. -/
theorem irqStS_of_irqRel {mem : Aeneas.Std.U64 → Aeneas.Std.U64} {kb : Aeneas.Std.U64} {σ : State Unit}
    (hR : IrqRel mem kb σ) (h126 : mem (irqStA kb 126#u64) = 3#u64) (h127 : mem (irqStA kb 127#u64) = 3#u64)
    (hhi : ∀ irq : Irq, 128 ≤ irq.toNat → σ.interruptStates irq ≠ .irqSignal) : IrqStS σ := by
  intro irq hi e
  have hi' : 125 < irq.toNat := by
    have := BitVec.lt_def.1 hi; simpa [maxIRQ] using this
  by_cases h8 : 128 ≤ irq.toNat
  · exact hhi irq h8 e
  · have h6 : irq = 126#8 ∨ irq = 127#8 := by
      have : irq.toNat = 126 ∨ irq.toNat = 127 := by omega
      rcases this with t | t
      · exact Or.inl (BitVec.eq_of_toNat_eq (by simpa using t))
      · exact Or.inr (BitVec.eq_of_toNat_eq (by simpa using t))
    rcases h6 with rfl | rfl
    · have h1 := hR.st 126#u64 (by decide)
      rw [h126] at h1
      have e' : σ.interruptStates (BitVec.ofNat 8 (126#u64).val) = .irqSignal := e
      rw [h1] at e'
      exact absurd (irqSt_signal _ e') (by decide)
    · have h1 := hR.st 127#u64 (by decide)
      rw [h127] at h1
      have e' : σ.interruptStates (BitVec.ofNat 8 (127#u64).val) = .irqSignal := e
      rw [h1] at e'
      exact absurd (irqSt_signal _ e') (by decide)

/-- **jboot's `fInitASt` with FL4's boot IRQ states**: line 125 `irqTimer`, lines 126 / 127 `irqReserved`. -/
def fInitIpiASt : State Unit :=
  { JBoot.fInitASt with
    interruptStates := Function.update (Function.update (Function.update JBoot.fInitASt.interruptStates
      125 .irqTimer) 126 .irqReserved) 127 .irqReserved }

theorem fInitIpi_125 : fInitIpiASt.interruptStates 125 = .irqTimer := by
  simp [fInitIpiASt, Function.update_apply]
theorem fInitIpi_126 : fInitIpiASt.interruptStates 126 = .irqReserved := by
  simp [fInitIpiASt, Function.update_apply]
theorem fInitIpi_127 : fInitIpiASt.interruptStates 127 = .irqReserved := by
  simp [fInitIpiASt, Function.update_apply]

/-- `fInitASt` (so `fInitIpiASt`, same heap) holds no IRQ handler cap. -/
theorem fInit_noHandler (p : ObjRef) (cref : CnodeIndex) (irq : Irq) :
    capOpt (JBoot.fInitASt.kheap p) cref ≠ some (.irqHandlerCap irq) := by
  intro hc
  have hb : ∀ q, capOpt (Fl4Spec.initKheap q) cref ≠ some (.irqHandlerCap irq) :=
    fun q h => SInvV.boot_vih q cref irq h rfl
  change capOpt (JBoot.fInitKheap p) cref = some (.irqHandlerCap irq) at hc
  simp only [JBoot.fInitKheap, Function.update_apply] at hc
  split_ifs at hc
  all_goals first
    | exact hb _ hc
    | (simp only [capOpt, Fl4Spec.emptyCnode] at hc; split_ifs at hc <;> simp_all; done)
    | (simp [capOpt] at hc; done)

theorem fInitIpi_irqStS : IrqStS fInitIpiASt := by
  intro irq _ e
  change Function.update (Function.update (Function.update JBoot.fInitASt.interruptStates
      125 .irqTimer) 126 .irqReserved) 127 .irqReserved irq = .irqSignal at e
  simp only [Function.update_apply] at e
  split_ifs at e <;> cases e

/-- **Non-vacuity: the carried fact holds at the boot-like state with 125 timer, 126 / 127 reserved.** -/
theorem fInitIpi_irqCarry : IrqCarry fInitIpiASt :=
  irqCarry_of_noHandler (fun p cref irq => fInit_noHandler p cref irq) fInitIpi_irqStS

/-- ... where gen 2's `IrqStB` fails. -/
theorem fInitIpi_not_irqStB : ¬ IrqStB fInitIpiASt := by
  intro h
  have := h 126 (by decide)
  rw [fInitIpi_126] at this; cases this

end

end Fl4Proofs.P3.SInvIB
