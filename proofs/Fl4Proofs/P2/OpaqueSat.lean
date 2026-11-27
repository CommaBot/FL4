/-
# P2 (line p3mc, gen 36): **`OpaqueH` against FL4's build values and the spec's default instances**
`OpaqueH` (P2/LocPlatModel) states eight facts about `opaque` constants of Fl4Spec/Machine. Lean's `opaque` gives
the logic no equation for a constant, so none of them is provable or refutable as stated. What can be checked is
that each is a satisfiable condition on the structure behind the constant, at the values FL4's build fixes, and how
it compares with the default instance (the witness Lean uses to accept the `opaque`, *not* its value in the logic).

* **`kcFL4`**: a `KernelConfig` with `numDomains = 1` (FL4: `NUM_DOMAINS = 1`, `crates/fl4-abi/build.rs` l.37).
* **`tcFL4`** (TSC at 1000 MHz, `timer.rs` l.15's initial `TSC_MHZ`) and **`tcFL4one`** (1 MHz, `timer.rs` l.149's
  fallback): `TimeConsts` with every Time.thy axiom proved, at FL4's values: `kernelWCETUs = 10`
  (`KERNEL_WCET_US`, `crates/fl4-arch-x86_64/src/timer.rs` l.22), `timerUnit = 1` and `ticksPerTimerUnit = mhz`
  (`us_to_ticks us = us * tsc_mhz`, l.261–263), `maxPeriodUs = (2^64 − 1) / mhz / 8` (`max_us = u64::MAX / tsc_mhz`,
  l.269–271; `max_period_us = max_us / 8`, `crates/fl4-core/src/sporadic.rs` l.30–33). Both have
  `maxPeriodUs < 2^61`.
* **`opaqueVals_sat`**: the eight conditions' value parts are jointly satisfiable: the `KernelConfig` and
  `TimeConsts` above, `maxTicksToUs := 2^64 − 1` (FL4's `update_consumed` threshold `u64::MAX`,
  `crates/fl4-core/src/schedcontext.rs` l.111), an IRQ oracle avoiding 126 / 127 (FL4's IPI lines
  `REMOTE_CALL_IPI = 158 − 0x20`, `RESCHEDULE_IPI = 159 − 0x20`, `crates/fl4-core/src/arch/x86_64/layout.rs`
  l.119–120, which FL4 never delivers as spec IRQs), and a deterministic `setDeadlineImpl` (`pure ()`; FL4's
  `set_deadline` is a function of its argument, `timer.rs` l.223–230).
* Against the default instances: **`default_nd`** (1 domain: consistent), **`default_tu`** (`timerUnit = 1`:
  consistent), **`default_maxP`** (one hour `< 2^61`: consistent), **`default_wcet`** (`kernelWCETUs = 100 ≠ 10`:
  `wcetUs` contradicts the default), **`default_maxTicks`** (`Word64`'s default is 0 `≠ 2^64 − 1`: `max` contradicts
  the default), **`default_dl`** (the default `NonDet` is `fail`, no outcome: `dl` holds there, vacuously),
  **`default_fail_empty`** (so with the default `in8Impl` / `in16Impl` / `in32Impl` (`fail`) the port read has no
  outcome at all and `pin0` would fail; FL4's `port_in` always returns a value, `crates/fl4-arch-x86_64/src/arch.rs`
  l.154–161, which `pin0` models by allowing 0). `irqOracle`'s default (`fun _ => 0`) satisfies `ipi`.
So no field of `OpaqueH` contradicts FL4's build; two (`wcetUs`, `max`) and `pin0` differ from the spec's default
witnesses, which only say the types are inhabited.
No premise. No existing statement changed except the root import list.
-/
import Fl4Proofs.P2.LocPlatModel

namespace Fl4Proofs.P2.OpaqueSat
open Fl4Spec

/-- A build configuration with FL4's one domain. -/
def kcFL4 : KernelConfig := ⟨1, by decide, by decide, 8, 256⟩

/-- FL4's x86_64 timer constants at a 1000 MHz TSC (module docstring). -/
def tcFL4 : TimeConsts where
  maxPeriodUs := 2305843009213693
  kernelWCETUs := 10
  ticksPerTimerUnit := 1000
  timerUnit := 1
  kernelWCET_us_pos2 := by decide
  MIN_BUDGET_le_MAX_PERIOD := by decide
  ticks_per_timer_unit_non_zero := by decide
  MIN_BUDGET_bound := by decide
  getCurrentTime_buffer_bound := by decide
  kernelWCET_pos' := by decide
  MIN_BUDGET_pos' := by decide
  init_domain_time_pos := by decide
  init_domain_time_bound := by decide
  getCurrentTime_buffer_pos := by decide

/-- FL4's x86_64 timer constants at the 1 MHz fallback rate. -/
def tcFL4one : TimeConsts where
  maxPeriodUs := 2305843009213693951
  kernelWCETUs := 10
  ticksPerTimerUnit := 1
  timerUnit := 1
  kernelWCET_us_pos2 := by decide
  MIN_BUDGET_le_MAX_PERIOD := by decide
  ticks_per_timer_unit_non_zero := by decide
  MIN_BUDGET_bound := by decide
  getCurrentTime_buffer_bound := by decide
  kernelWCET_pos' := by decide
  MIN_BUDGET_pos' := by decide
  init_domain_time_pos := by decide
  init_domain_time_bound := by decide
  getCurrentTime_buffer_pos := by decide

/-- `maxPeriodUs` is FL4's `max_us / 8` at each rate. -/
theorem tcFL4_maxP : tcFL4.maxPeriodUs.toNat = (2 ^ 64 - 1) / 1000 / 8 := by decide
theorem tcFL4one_maxP : tcFL4one.maxPeriodUs.toNat = (2 ^ 64 - 1) / 1 / 8 := by decide

/-- **The value parts of `OpaqueH`'s eight fields are jointly satisfiable at FL4's build values.** -/
theorem opaqueVals_sat :
    (∃ kc : KernelConfig, kc.numDomains = 1) ∧
    (∃ tc : TimeConsts, tc.kernelWCETUs = 10 ∧ tc.timerUnit = 1 ∧ tc.maxPeriodUs.toNat < 2 ^ 61) ∧
    (∃ w : Word64, w.toNat = 2 ^ 64 - 1) ∧
    (∃ f : Nat → Word8, ∀ n, (f n).toNat ≠ 126 ∧ (f n).toNat ≠ 127) ∧
    (∃ g : Word64 → MachineRestMonad Unit, ∀ (d : Word64) (mr : MachineStateRest) (x y : Unit × MachineStateRest),
      x ∈ (g d mr).1 → y ∈ (g d mr).1 → x = y) :=
  ⟨⟨kcFL4, rfl⟩, ⟨tcFL4, rfl, rfl, by decide⟩, ⟨BitVec.allOnes 64, by decide⟩,
    ⟨fun _ => 0, fun _ => by show (0 : Word8).toNat ≠ 126 ∧ (0 : Word8).toNat ≠ 127; decide⟩,
    ⟨fun _ => NonDet.pure (), fun _ _ _ _ hx hy =>
      (Set.mem_singleton_iff.mp hx).trans (Set.mem_singleton_iff.mp hy).symm⟩⟩

/-! ## The default instances -/

theorem default_nd : (default : KernelConfig).numDomains = 1 := rfl
theorem default_tu : (default : TimeConsts).timerUnit = 1 := rfl
theorem default_maxP : (default : TimeConsts).maxPeriodUs.toNat < 2 ^ 61 := by decide
theorem default_wcet : (default : TimeConsts).kernelWCETUs = 100 ∧ (default : TimeConsts).kernelWCETUs ≠ 10 :=
  ⟨rfl, by decide⟩
theorem default_maxTicks : (default : Word64).toNat = 0 := rfl
theorem default_fail_empty {σ α : Type} (s : σ) : ((default : NonDet σ α) s).1 = ∅ := rfl
theorem default_dl (d : Word64) (mr : MachineStateRest) (x y : Unit × MachineStateRest)
    (hx : x ∈ ((default : Word64 → MachineRestMonad Unit) d mr).1) : y ∈ ((default : Word64 → MachineRestMonad Unit) d mr).1 → x = y :=
  fun _ => False.elim hx
theorem default_ipi (n : Nat) : ((default : Nat → Word8) n).toNat ≠ 126 ∧ ((default : Nat → Word8) n).toNat ≠ 127 := by
  show (default : Word8).toNat ≠ 126 ∧ (default : Word8).toNat ≠ 127
  decide

end Fl4Proofs.P2.OpaqueSat
