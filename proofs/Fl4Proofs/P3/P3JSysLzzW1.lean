/-
P3 (p3J gen 56): **`kernel_entry_runMcWKR_sysLzz` exercised on its per-call part at a non-idle state**: a closed
instance of gen 54's native syscall top at the root-thread witness, on gen 55's platform.

The platform is gen 55's (P3JSysLzzSat): store `wst` (`wL`, `wP`), arch `warI1`, CR3 relation `wAR`, machine
relation `ipiMR`, `A := Fl4Spec.MachineState`. The state is the boot line's root-thread witness `JBootQ.w1` /
`JBootQ.σ1` (JBootQ1St … JBootQ1U40: the 1-core boot state plus a running root TCB `rT` on its SC `rS`, CSpace a
radix-1 CNode `rC` holding the root's thread and SC caps), whose current thread is not idle (`σ1_nonIdle`).

* **`runMcWKR_w1`** (no premise): `RunMcWKR` at `w1 / σ1`, component by component: `RunCK` (`jReachU40_w1I1`,
  `cki_σ1`), `JAtMcW` (one core: `jAtMcW_of_one` with `jAtZ_w1I1`, `Zw1_vx`), `KhWF` (**`khWF_σ1`**: the three
  root objects by `kh1_some`, the rest by `khWF_fInit`), `NoSig` (`σ1`'s interrupt states are the boot state's:
  `noSig_fInit`), `RR` (**`rr_σ1`**: the root SC is the idle SC's record with a new `scTcb`, period 0; the rest by
  `rr_fInit`). The `*_w2` component proofs are one-line instances of boot-state facts (`khWF_fInit`, `rr_fInit`,
  `noSig_fInit`, `jAtZ_w0I1`), so nothing is generalised in place: the `w1` components reuse those facts and the
  existing `w1` witnesses (no copy).
* **`sysK6_yield`**: `SysK6` holds for `SysYield` / `.sysYield` at every state and ghost set (`SysYield` is no
  `InvSys` and no `MidSysR` number, so both fields of `KDispHypsKVU44w` are vacuous).
* **`nativeSys_yieldI`**: `NativeSys SysYield .sysYield` (its yield disjunct).
* **`sysLzz_w1_yield`** (closed, only `OpaqueWK` / `FpuImplDet` / `FpuWriteDet` [P] left): FL4's
  `handle_syscall` for `SysYield` at `w1 / σ1.machineState` terminates in a `RunMcWKR` state related to an
  outcome of the spec's `fl4KernelEntrySyscall true .sysYield σ1`. The per-call antecedents of `_sysLzz` are
  discharged: ct ≠ idle (`σ1_nonIdle`), `NativeSys`, `SysFlag` (`w1_hfl`), `SysK6` (`sysK6_yield`).
* **`sysLzz_w1`**: the same instance with the syscall left general (only the three opaque facts left, plus the
  per-call `NativeSys` / `SysK6` antecedents; ct ≠ idle and `SysFlag` discharged).

Caveat (as gen 55): `wAR := fun _ _ => True`, so the CR3-side globals and the CR3 fields inside `JAtZ` hold
trivially on this platform. `SysK6` at yield is vacuous by the syscall number (not by `wAR`).

Named premises: `OpaqueWK` [P] (JBootU34), `FpuImplDet` [P] (ScFpuNd), `FpuWriteDet` [P] (ArchSwThr), hypotheses of
`sysLzz_w1_yield` / `sysLzz_w1`; none new. No sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P3.P3JSysLzzSat
import Fl4Proofs.P3.P3JCkRun
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.JBootQ
open fl4_core Classical Fl4Spec Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P2.Wit
open Fl4Proofs.P3.JBoot Fl4Proofs.P3.SInvR.G5 Fl4Proofs.P3.SInvR.G4 Fl4Proofs.P3.Vs Fl4Proofs.P3.Mc

noncomputable section

/-- (p3J gen 56) **No garbage-typed object at the root-thread witness** (module docstring). -/
theorem khWF_σ1 : SInvKt.KhWF σ1 := by
  intro o k hk n hn
  have hk1 : kh1 o = some k := hk
  rcases kh1_some hk1 with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, -, -, h'⟩
  · simp [aType] at hn
  · simp only [aType] at hn
    rw [if_pos (by unfold validSchedContextSize minSchedContextBits untypedMaxBits; decide)] at hn
    cases hn
  · simp only [aType] at hn
    rw [if_pos rootCs_wf] at hn
    cases hn
  · exact SInvKt.khWF_fInit o k h' n hn

/-- (p3J gen 56) **Every SC of the root-thread witness is round-robin** (module docstring). -/
theorem rr_σ1 : SInvRr.RR σ1 := by
  funext o
  unfold SInvRr.rpV
  rw [σ1_kheap]
  cases hk : kh1 o with
  | none => rfl
  | some k =>
    rcases kh1_some hk with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, -, -, h'⟩
    · rfl
    · rfl
    · rfl
    · have e0 := congrFun SInvRr.rr_fInit o
      unfold SInvRr.rpV at e0
      have h'' : fInitASt.kheap o = some k := h'
      rw [h''] at e0
      exact e0

/-- (p3J gen 56) **No signal line at the root-thread witness** (its interrupt states are the boot state's). -/
theorem noSig_σ1 : SInvNs.NoSig σ1 := noSig_fInit

/-- (p3J gen 56) **`RunMcWKR` at the root-thread witness `w1 / σ1`**, no premise (module docstring). -/
theorem runMcWKR_w1 : RunMcWKR (L := wL) warI1 wAR ipiMR w1 σ1.machineState σ1 :=
  ⟨⟨⟨⟨⟨jReachU40_w1I1, cki_σ1⟩,
    jAtMcW_of_one (jAtZ_w1I1 _) Zw1_vx (fun c hc => by rw [cpu_w1]; exact hc)⟩, khWF_σ1⟩, noSig_σ1⟩, rr_σ1⟩

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop)

/-- (p3J gen 56) **`SysK6` at `SysYield`**: vacuous by the syscall number, at every state and ghost set. -/
theorem sysK6_yield (Z : XSets) (H : P1.Heap) (Cs : Set U64) (s : S) (a : A) (σ : Fl4Spec.State Unit) :
    SysK6 (L := L) arI AR Z H Cs s a σ fl4_abi.syscall.SysYield .sysYield := by
  intro _ _ _ _ _ _ _ _ _ _
  refine ⟨fun _ _ _ _ _ hi => ?_, fun _ _ _ _ _ hm => ?_⟩
  · exfalso
    rcases hi with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> revert h
    · unfold fl4_abi.syscall.SysYield fl4_abi.syscall.SysSend; decide
    · unfold fl4_abi.syscall.SysYield fl4_abi.syscall.SysNBSend; decide
    · unfold fl4_abi.syscall.SysYield fl4_abi.syscall.SysCall; decide
  · exfalso
    rcases hm with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> revert h
    · unfold fl4_abi.syscall.SysYield fl4_abi.syscall.SysReplyRecv; decide
    · unfold fl4_abi.syscall.SysYield fl4_abi.syscall.SysNBSendRecv; decide
    · unfold fl4_abi.syscall.SysYield fl4_abi.syscall.SysNBSendWait; decide

end

/-- (p3J gen 56) `SysYield` is a native syscall (its yield disjunct). -/
theorem nativeSys_yieldI : NativeSys fl4_abi.syscall.SysYield .sysYield :=
  Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))

set_option maxHeartbeats 4000000 in
/-- (p3J gen 56) **`kernel_entry_runMcWKR_sysLzz` at the root-thread witness**: ct ≠ idle and `SysFlag`
discharged; only `OpaqueWK`, `FpuImplDet`, `FpuWriteDet` [P] and the per-call `NativeSys` / `SysK6` left. -/
theorem sysLzz_w1 (O : OpaqueWK) (hFpu : FpuImplDet) (hFW : FpuWriteDet) :
    ∀ (n : I64) (c : Fl4Spec.Syscall), NativeSys n c →
      (∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
        JAtZ (L := wL) warI1 wAR Z H Cs Ac Lst D w1 σ1.machineState σ1 →
          SysK6 (L := wL) warI1 wAR Z H Cs w1 σ1.machineState σ1 n c) →
      syscall.handle_syscall wst warI1 w1 σ1.machineState n ⦃ r =>
        ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ1).1 ∧
          RunMcWKR (L := wL) warI1 wAR ipiMR r.1 r.2 σ' ⦄ := fun n c hN hK6 =>
  let ⟨_, h1, h2, h3, h4, h5, h6, h9, h10, h11, h12, h13, h14, h16, h17, _, _, _⟩ :=
    M2.sysLzz_globals_sat O hFpu hFW
  kernel_entry_runMcWKR_sysLzz (L := wL) (st := wst) (MR := ipiMR) h1 h2 h3 h4 h5 h6 h9 h10 h11 h12 h13 h14 h16 h17
    hFpu hFW runMcWKR_w1 n c σ1_nonIdle hN w1_hfl hK6

set_option maxHeartbeats 4000000 in
/-- (p3J gen 56) **A closed instance of `_sysLzz`'s per-call part**: `SysYield` at the root-thread witness, every
antecedent discharged; only `OpaqueWK`, `FpuImplDet`, `FpuWriteDet` [P] left (module docstring). -/
theorem sysLzz_w1_yield (O : OpaqueWK) (hFpu : FpuImplDet) (hFW : FpuWriteDet) :
    syscall.handle_syscall wst warI1 w1 σ1.machineState fl4_abi.syscall.SysYield ⦃ r =>
      ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true .sysYield σ1).1 ∧
        RunMcWKR (L := wL) warI1 wAR ipiMR r.1 r.2 σ' ⦄ :=
  sysLzz_w1 O hFpu hFW _ _ nativeSys_yieldI fun Z H Cs _ _ _ _ => sysK6_yield warI1 wAR Z H Cs _ _ _

end

end Fl4Proofs.P3.JBootQ
