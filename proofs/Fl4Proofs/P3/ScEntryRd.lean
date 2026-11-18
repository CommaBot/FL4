/-
P3 (DESIGN.md §9), scheduling contexts: **the current SC's head ready at an
invocation's start** (l4v `cur_sc_offset_ready`), from the system-call entry.

`decode_invocation_cnodeJ_steps` (XTopJointCnDel) asks `hRd0`: at a zero
consumed time, the current SC's head is ready. It is not a consequence of
`JAtZ` (whose `OffOK` speaks of a positive consumed time only), but of the
entry path the invocation runs after:

* `OffReady.rd0`: `OffReady` (the head plus the consumed time not after the
  current time, l4v `cur_sc_offset_ready (consumed_time s)`) gives `hRd0`.
* `offReady_entry`: the spec's `update_time_stamp; check_budget_restart`
  returning `true` (the invocation runs) keeps `OffReady`: the time update
  moves the time and the consumed time alike (time does not go back), and a
  successful `check_budget_restart` changes nothing (`checkBudgetRestart_true`).
* `budget_ok_offReady`: FL4's `syscall::budget_ok` (ScEntry's
  `budget_ok_refines`) with that: when it lets the invocation run, `OffReady`
  at the kernel entry gives `OffReady` at the invocation's start.

So `hRd0` is discharged at the entry step from `OffReady` at kernel entry:
the l4v invariant the entry carries (`cur_sc_offset_ready` of the running
thread's SC, established by `schedule`'s choice of a released thread with
the consumed time reset); no J-level entry theorem composes the steps yet.
-/
import Fl4Proofs.P3.XTopJointPP
import Fl4Proofs.P3.ScEntry
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section Spec
open Fl4Spec

/-- **`OffReady` gives `hRd0`** (module docstring). -/
theorem OffReady.rd0 {σ : State Unit} (h : OffReady σ) :
    σ.consumedTime = 0 → ∀ y n, σ.kheap σ.curSc = some (.schedContext y n) → scActive y = true →
      refillReady σ.curTime (refillHd y) = true := by
  intro h0 y n hy _
  have h1 := h y n hy
  rw [h0] at h1
  simp only [refillReady, refillReady', decide_eq_true_eq, bv_add0, BitVec.le_def]
  simpa using h1

/-- A successful `check_budget` changes nothing. -/
theorem checkBudget_true {σ : State Unit} {y : Bool × State Unit} (hy : y ∈ (checkBudget (Z := Unit) σ).1)
    (ht : y.1 = true) : y.2 = σ := by
  unfold checkBudget at hy
  obtain ⟨a1, h1, hy⟩ := hy
  obtain rfl : a1 = (σ.curSc, σ) := h1
  obtain ⟨a2, h2, hy⟩ := hy
  obtain rfl : a2 = (σ.consumedTime, σ) := h2
  obtain ⟨a3, h3, hy⟩ := hy
  unfold getScRefillSufficient NonDet.getsThe at h3
  cases hh : readScRefillSufficient (Z := Unit) σ.curSc σ.consumedTime σ with
  | none => rw [hh] at h3; exact h3.elim
  | some b =>
    rw [hh] at h3
    obtain rfl : a3 = (b, σ) := h3
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte] at hy
      obtain ⟨a4, -, hy⟩ := hy
      obtain ⟨a5, -, hy⟩ := hy
      obtain rfl : y = (false, a5.2) := hy
      cases ht
    · simp only [↓reduceIte] at hy
      obtain ⟨a4, h4, hy⟩ := hy
      obtain rfl : a4 = (isCurDomainExpired σ, σ) := h4
      obtain rfl : y = (!isCurDomainExpired σ, σ) := hy
      rfl

/-- A successful `check_budget_restart` changes nothing. -/
theorem checkBudgetRestart_true {σ : State Unit} {x : Bool × State Unit}
    (hx : x ∈ (checkBudgetRestart (Z := Unit) σ).1) (ht : x.1 = true) : x.2 = σ := by
  unfold checkBudgetRestart at hx
  obtain ⟨y, hy, hx⟩ := hx
  obtain ⟨c1, hc1, hx⟩ := hx
  obtain rfl : c1 = (y.2.curThread, y.2) := hc1
  obtain ⟨w, hw, hx⟩ := hx
  have ew := (PPS.getThreadState_mem hw).1
  obtain ⟨u, hu, hx⟩ := hx
  obtain rfl : x = (y.1, u.2) := hx
  simp only at ht
  have eu : u.2 = w.2 := by
    unfold NonDet.when at hu
    rw [if_neg (by simp [ht])] at hu
    obtain rfl : u = ((), w.2) := hu
    rfl
  show u.2 = σ
  rw [eu, ew]
  exact checkBudget_true hy ht

/-- **The entry's time update and successful budget check keep `OffReady`**
(module docstring), time not going back. -/
theorem offReady_entry {σ σ' : State Unit} {now : Word} {ms : MachineState} (hnd : numDomains = 1)
    (hm : doMachineOp (Z := Unit) getCurrentTime σ = ({(now, { σ with machineState := ms })}, False))
    (hle : σ.curTime ≤ now)
    (h : (updateTimeStamp (Z := Unit) >>= fun _ => checkBudgetRestart) σ = ({(true, σ')}, False))
    (hO : OffReady σ) : OffReady σ' := by
  have hx : (true, σ') ∈ ((updateTimeStamp (Z := Unit) >>= fun _ => checkBudgetRestart) σ).1 := by
    rw [h]; rfl
  obtain ⟨y, hy, hx⟩ := hx
  rw [updateTimeStamp_eq' hnd hm] at hy
  obtain rfl := Set.mem_singleton_iff.1 hy
  have e := checkBudgetRestart_true hx rfl
  simp only at e
  rw [e]
  intro y' m hy'
  have h0 : (refillHd y').rTime.toNat + σ.consumedTime.toNat ≤ σ.curTime.toNat := hO y' m hy'
  have hle' : σ.curTime.toNat ≤ now.toNat := by rw [← BitVec.le_def]; exact hle
  have hlt := now.isLt
  show (refillHd y').rTime.toNat + (σ.consumedTime + (now - σ.curTime)).toNat ≤ now.toNat
  rw [BitVec.toNat_add, BitVec.toNat_sub_of_le hle, Nat.mod_eq_of_lt (by omega)]
  omega

end Spec

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]

/-- **System-call entry: when `budget_ok` lets the invocation run, `OffReady`
at kernel entry gives `OffReady` at the invocation's start** (ScEntry's
`budget_ok_refines` and `offReady_entry`). -/
theorem budget_ok_offReady {N T C : Set U64} {c : U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) (hN : NSC N C σ) (hI : Inv σ)
    (hC : CurInv σ)
    (hnd : Fl4Spec.numDomains = 1)
    (hnow : ar.now a ⦃ r => ∃ ms, Fl4Spec.doMachineOp (Z := Unit) Fl4Spec.getCurrentTime σ =
      ({(r.1.bv, { σ with machineState := ms })}, False) ∧ σ.curTime ≤ r.1.bv ⦄)
    (hmrt : ∀ a : A, sporadic.max_release_time ar a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : ∀ a : A, sporadic.min_budget ar a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hval : ∀ (s' : S) (σ' : Fl4Spec.State Unit), SchedRel st N T C c s' σ' →
      TmoKeep st (nodeW st s c layout.node.CUR_THREAD) s σ s' σ' →
      faults.valid_timeout_handler st s' (nodeW st s c layout.node.CUR_THREAD) ⦃ b =>
        Fl4Spec.isValidTimeoutHandler (Z := Unit) (nodeW st s c layout.node.CUR_THREAD).bv σ' =
          ({(b, σ')}, False) ⦄)
    (hto : ∀ (s' : S) (a' : A) (σ' : Fl4Spec.State Unit), SchedRel st N T C c s' σ' →
      NtfnStateRel N T (L.mem s') σ' → NSC N C σ' → InvBut σ' (nodeW st s c layout.node.CUR_THREAD).bv →
      faults.handle_timeout st ar s' a' (nodeW st s c layout.node.CUR_THREAD)
        (error.Fault.Timeout (L.mem s' (scW (nodeW st s c layout.node.CUR_SC) 48#u64))) ⦃ r => ∃ σ'',
        Fl4Spec.handleTimeout (Z := Unit) (nodeW st s c layout.node.CUR_THREAD).bv
          (.timeout (L.mem s' (scW (nodeW st s c layout.node.CUR_SC) 48#u64)).bv) σ' = ({((), σ'')}, False) ∧
        SchedRel st N T C c r.1 σ'' ∧ Inv σ'' ∧ NtfnStateRel N T (L.mem r.1) σ'' ∧ NSC N C σ'' ∧
        σ''.consumedTime = σ'.consumedTime ∧ (IdleOK σ' → IdleOK σ'') ⦄) :
    syscall.budget_ok st ar s a ⦃ r => ∃ σ',
      (Fl4Spec.updateTimeStamp (Z := Unit) >>= fun _ => Fl4Spec.checkBudgetRestart) σ = ({(r.1, σ')}, False) ∧
      SchedRel st N T C c r.2.1 σ' ∧ Inv σ' ∧
      (r.1 = true → OffReady σ → OffReady σ') ⦄ := by
  obtain ⟨r0, -, ms, hm, hle⟩ := spec_exists hnow
  refine WP.spec_mono (budget_ok_refines s a σ hS hR hN hI hC hnd hnow hmrt hmb hval hto) ?_
  rintro r ⟨σ', h, hS', hI', -⟩
  refine ⟨σ', h, hS', hI', fun ht hO => ?_⟩
  rw [ht] at h
  exact offReady_entry hnd hm hle h hO

end

end

end Fl4Proofs.P3.Sched
