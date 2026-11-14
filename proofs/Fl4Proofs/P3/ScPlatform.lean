/-
P3 (DESIGN.md §9), scheduling contexts: **the platform's timer constants**.

`TimeAgree ar`: the platform's `timeConsts` (Fl4Spec/Machine.lean) agree
with FL4's arch interface. FL4's `max_period_us` (C's default
`getMaxUsToTicks() / 8`) is the spec's `MAX_PERIOD_US` (a platform constant,
PORTING.md), `us_to_ticks` is the spec's `us_to_ticks` up to that bound, and
the kernel WCET in ticks is `kernelWCET_ticks`. From these,
`max_release_time` is `MAX_RELEASE_TIME` (`TimeAgree.mrt`) and `min_budget`
is `MIN_BUDGET` (`TimeAgree.mb`), the facts the scheduling-context proofs
use.
-/
import Fl4Proofs.P1.Refill
import Fl4Spec
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core

/-- The platform's timer constants agree with FL4's arch interface. -/
structure TimeAgree {A : Type} (ar : machine.Arch A) : Prop where
  maxPeriod : ∀ a, sporadic.max_period_us ar a ⦃ v => v.bv = Fl4Spec.MAX_PERIOD_US ⦄
  usToTicks : ∀ a (u : U64), u.bv ≤ Fl4Spec.MAX_PERIOD_US →
    ar.us_to_ticks a u ⦃ v => v.bv = Fl4Spec.usToTicks u.bv ⦄
  kernelWcet : ∀ a, ar.kernel_wcet_ticks a ⦃ v => v.bv = Fl4Spec.kernelWCETTicks ⦄
  /-- FL4's `min_budget_us` is `2 * 10`: the kernel WCET is 10 µs. -/
  wcetUs : Fl4Spec.kernelWCETUs = 10
  /-- The timer counts whole ticks per µs (x86: TSC MHz), as FL4's
  `us_to_ticks = us * tsc_mhz`. -/
  timerUnit : Fl4Spec.timerUnit = 1

namespace TimeAgree
variable {A : Type} {ar : machine.Arch A}

/-- **`max_release_time` is `MAX_RELEASE_TIME`.** -/
theorem mrt (hT : TimeAgree ar) (a : A) :
    sporadic.max_release_time ar a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄ := by
  unfold sporadic.max_release_time
  refine WP.spec_bind (hT.maxPeriod a) ?_
  intro i hi
  refine WP.spec_bind (hT.usToTicks a i (by rw [hi]; exact BitVec.le_refl _)) ?_
  intro p hp
  simp only [lift, bind_ok, WP.spec_ok]
  unfold Fl4Spec.MAX_RELEASE_TIME Fl4Spec.MAX_PERIOD
  rw [← hi, ← hp]
  simp [core.num.U64.MAX, U64.rMax, BitVec.mul_comm]
  rfl

/-- **`min_budget` is `MIN_BUDGET`.** -/
theorem mb (hT : TimeAgree ar) (a : A) :
    sporadic.min_budget ar a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄ := by
  unfold sporadic.min_budget
  refine WP.spec_bind (hT.kernelWcet a) ?_
  intro i hi
  rw [WP.spec_ok]
  unfold Fl4Spec.MIN_BUDGET
  rw [← hi]
  simp [BitVec.mul_comm]

/-- `us_to_ticks` below `MAX_PERIOD_US` is exact. -/
theorem usToTicks_toNat (hT : TimeAgree ar) {u : BitVec 64} (hu : u ≤ Fl4Spec.MAX_PERIOD_US) :
    (Fl4Spec.usToTicks u).toNat = u.toNat * Fl4Spec.ticksPerTimerUnit.toNat := by
  have hb := Fl4Spec.getCurrentTime_buffer_bound
  have hu' : u.toNat ≤ Fl4Spec.MAX_PERIOD_US.toNat := BitVec.le_def.1 hu
  simp only [Fl4Spec.unat, Fl4Spec.maxTime, BitVec.toNat_allOnes] at hb
  have : u.toNat * Fl4Spec.ticksPerTimerUnit.toNat ≤
      Fl4Spec.MAX_PERIOD_US.toNat * Fl4Spec.ticksPerTimerUnit.toNat := Nat.mul_le_mul_right _ hu'
  rw [Nat.mul_assoc] at hb
  have hlt : u.toNat * Fl4Spec.ticksPerTimerUnit.toNat < 2 ^ 64 := by omega
  unfold Fl4Spec.usToTicks
  rw [hT.timerUnit]
  simp [BitVec.toNat_mul, Nat.mod_eq_of_lt hlt]
  all_goals omega

/-- `us_to_ticks` is strictly monotone below `MAX_PERIOD_US`. -/
theorem usToTicks_lt (hT : TimeAgree ar) {u v : BitVec 64} (hu : u ≤ Fl4Spec.MAX_PERIOD_US)
    (hv : v ≤ Fl4Spec.MAX_PERIOD_US) : Fl4Spec.usToTicks u < Fl4Spec.usToTicks v ↔ u < v := by
  have ht : Fl4Spec.ticksPerTimerUnit.toNat ≠ 0 := fun h =>
    Fl4Spec.ticks_per_timer_unit_non_zero (BitVec.eq_of_toNat_eq (by simpa using h))
  rw [BitVec.lt_def, BitVec.lt_def, hT.usToTicks_toNat hu, hT.usToTicks_toNat hv]
  exact Nat.mul_lt_mul_right (Nat.pos_of_ne_zero ht)

/-- `MIN_BUDGET_US` is at most `MAX_PERIOD_US`. -/
theorem minUs_le : Fl4Spec.MIN_BUDGET_US ≤ Fl4Spec.MAX_PERIOD_US := Fl4Spec.MIN_BUDGET_le_MAX_PERIOD

/-- `MIN_BUDGET` is `us_to_ticks MIN_BUDGET_US`. -/
theorem minBudget_eq (hT : TimeAgree ar) : Fl4Spec.MIN_BUDGET = Fl4Spec.usToTicks Fl4Spec.MIN_BUDGET_US := by
  have hb := Fl4Spec.MIN_BUDGET_bound
  have hle : 2 * Fl4Spec.kernelWCETUs ≤ Fl4Spec.MAX_PERIOD_US := Fl4Spec.MIN_BUDGET_le_MAX_PERIOD
  rw [hT.wcetUs] at hle
  have hk : Fl4Spec.kernelWCETUs ≤ Fl4Spec.MAX_PERIOD_US := by
    rw [hT.wcetUs]; exact BitVec.le_trans (by decide) hle
  have h1 : (Fl4Spec.usToTicks Fl4Spec.kernelWCETUs).toNat = 10 * Fl4Spec.ticksPerTimerUnit.toNat := by
    rw [hT.usToTicks_toNat hk, hT.wcetUs]; rfl
  simp only [Fl4Spec.unat, Fl4Spec.maxTime, BitVec.toNat_allOnes, hT.wcetUs] at hb
  apply BitVec.eq_of_toNat_eq
  rw [hT.usToTicks_toNat minUs_le]
  show (2 * Fl4Spec.usToTicks Fl4Spec.kernelWCETUs).toNat =
    (2 * Fl4Spec.kernelWCETUs).toNat * Fl4Spec.ticksPerTimerUnit.toNat
  rw [BitVec.toNat_mul, h1, BitVec.toNat_mul, hT.wcetUs]
  simp at hb ⊢
  omega

end TimeAgree

end Fl4Proofs.P3.Sched
