/-
P3 (FL4 #71 / PR #66, line lcd; KENTRY-PLAN `lcd`): **a declined local entry, then the general
entry**: `kernel_entry_reachU29D`.

fl4-sync runs a syscall or a VM fault first beside its serial gate (`handle_syscall_local`,
`handle_reply_recv_vm_local`, `handle_ioport_local`, `handle_invocation_local`,
`handle_vm_fault_local`). One that returns `false` has written either nothing, or the current
thread's `FAULT_IP` (syscall entries; the value `syscall` writes again) and one
`update_timestamp`, i.e. one clock reading (P1 FastLocalDecline's decline shapes); fl4-sync then
runs the general entry (`handle_syscall`, `handle_vm_fault`) from that state.

**The declined case relates to `tick σ`** (`Fl4Spec.fl4ClockTick`, Ext/Tick: an environment step
that only consumes one clock-oracle reading, the hardware clock advancing). With a clock
reading `n1` (`arI.now a = ok (n1, a')`), the general entry from the declined state runs exactly
as from the entry state `s` with the Arch value `a'` (P1 `handle_syscall_pre_same` /
`vm_pre_same`: its own timestamp update supersedes the prefix's), and `(s, a', tick σ)` is a
`JReachU17` state (`jreachU17_tick`): the joint relation reads the Arch value only through
`AR` (kept by `now`, `ARKeep`) and `MR` (`MachPlat.now`: `MR a' (gctState σ.ms)`, and
`tick σ`'s machine state is `gctState σ.ms`), and the invariants read the clock fields only
through `ValidMachineTime` (`vmt_tick`: the clock does not go back). So U29's clause for the
entry, at `(s, a', tick σ)`, is the postcondition of the general run from the declined state.
The spec event therefore starts from `tick σ`, not from `σ`: the general run reads the clock a
second time, and the spec's oracle counts readings (with `σ` itself the statement would ask the
two readings to agree, i.e. a clock that does not advance; KENTRY-PLAN `lcd`).

A decline before any write leaves `(s, a)`; there U29's clause at `σ` itself applies (`DeclAt`'s
first case).

* `vmt_tick`, `sinvA_tick`, `sinvX_tick`, `sinvIP_tick`: the spec invariants at `tick σ`.
* `jreachU17_tick`: `JReachU17 s a σ → arI.now a = ok (n1, a1) → JReachU17 s a1 (tick σ)`
  (through `JReachU3.start`; no premise).
* `SysClU29` / `SysUClU29` / `VmClU29`: U29's syscall / unknown-syscall / VM-fault clauses (their
  text, verbatim) for a given run; `DeclAt`, `DeclSysU29`, `DeclVmU29`: the declined case.
* `declSys_of`, `declVm_of`, and the top **`kernel_entry_reachU29D`**: U29's premises verbatim,
  nothing added.
-/
import Fl4Proofs.P3.XTopJointKEntryU29
import Fl4Proofs.P1.FastLocalDecline
import Fl4Spec.Ext.Tick
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.SInvR.G5
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4

noncomputable section

/-! ## The spec state after one clock reading -/

/-- `tick σ`'s machine state is the one `getCurrentTime` leaves. -/
theorem tick_eq (σ : Fl4Spec.State Unit) :
    Fl4Spec.fl4ClockTick σ = { σ with machineState := gctState σ.machineState } := rfl

/-- `getCurrentTime` from `σ`'s machine state ends at `tick σ`'s. -/
theorem getCurrentTime_tick (σ : Fl4Spec.State Unit) :
    Fl4Spec.getCurrentTime σ.machineState =
      ({(gctVal σ.machineState, (Fl4Spec.fl4ClockTick σ).machineState)}, False) :=
  getCurrentTime_eq σ.machineState

/-- **`ValidMachineTime` at `tick σ`**: the clock does not go back and stays below its cap. -/
theorem vmt_tick {σ : Fl4Spec.State Unit} (h : SInvV.ValidMachineTime σ) :
    SInvV.ValidMachineTime (Fl4Spec.fl4ClockTick σ) :=
  ⟨vmt_le_gct h, by show (gctVal σ.machineState).toNat ≤ _; rw [gctVal_toNat]; exact gctNat_le _⟩

/-- `SInvA` at `tick σ` (only `vmt` reads the clock fields). -/
theorem sinvA_tick {σ : Fl4Spec.State Unit} (h : SInvAll.SInvA σ) : SInvAll.SInvA (Fl4Spec.fl4ClockTick σ) :=
  { h with sg := { h.sg with }, dom := { h.dom with }, vmt := vmt_tick h.vmt }

/-- **`SInvX` at `tick σ`.** -/
theorem sinvX_tick {σ : Fl4Spec.State Unit} (h : SInvX σ) : SInvX (Fl4Spec.fl4ClockTick σ) := by
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hA, hCt⟩, hOI⟩, hEX, hRB, hT4⟩, hRS⟩, hBSA⟩, hVB⟩, hRdL⟩, hRP⟩ := h
  exact ⟨⟨⟨⟨⟨⟨⟨⟨sinvA_tick hA, hCt⟩, hOI⟩, hEX, hRB, hT4⟩, hRS⟩, { hBSA with }⟩, hVB⟩, hRdL⟩, hRP⟩

/-- `SInvIP` at `tick σ`. -/
theorem sinvIP_tick {σ : Fl4Spec.State Unit} (h : SInvIP σ) : SInvIP (Fl4Spec.fl4ClockTick σ) :=
  ⟨h.ioP, h.ioN, h.utZ⟩

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop}

/-- **A clock reading moves a reachable joint state to `tick σ`** (module docstring): the entry
state with the Arch value `now` left, at the spec state one oracle reading later. -/
theorem jreachU17_tick (hnd : Fl4Spec.numDomains = 1) (hARI : ARIface arI AR) (hM : MachPlat arI MR)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hJ : JReachU17 (L := L) arI AR MR s a σ)
    {n1 : U64} {a1 : A} (hn : arI.now a = ok (n1, a1)) :
    JReachU17 (L := L) arI AR MR s a1 (Fl4Spec.fl4ClockTick σ) := by
  obtain ⟨hJ3, hG, hIV, hD⟩ := hJ
  obtain ⟨Z, H, Cs, Ac, Lst, D, J, hX, -, hI, -, hR, -, hPg, hvx⟩ := jreach_invU3 hnd hJ3
  have hR' : MR a1 (gctState σ.machineState) := by
    have h := hM.now a σ.machineState hR
    rw [hn, WP.spec_ok] at h
    exact h.2
  obtain ⟨Lst', J'⟩ := J.msArJ (gctState σ.machineState) a1 rfl (fun hc => by
    have h := hARI.toARKeep.now a _ hc
    rw [hn, WP.spec_ok] at h
    exact h)
  have J'' : JAtZ (L := L) arI AR Z H Cs Ac Lst' D s a1 (Fl4Spec.fl4ClockTick σ) := by
    rw [tick_eq]; exact J'
  exact ⟨JReachU3.start J'' hvx (sinvX_tick hX) (sinvIP_tick hI) hR' hPg, hG, hIV, hD⟩

end

/-! ## U29's clauses for a given run, and the declined case -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)

/-- **U29's syscall clause** (its text) at the joint state `(s, a, σ)` with the ghosts
`Z H Cs`, for the run `R`. -/
def SysClU29 (Z : XSets) (H : P1.Heap) (Cs : Set U64) (s : S) (a : A) (σ : Fl4Spec.State Unit) (n : I64)
    (c : Fl4Spec.Syscall) (R : Result (S × A)) : Prop :=
  σ.curThread ≠ σ.idleThread → NativeSys n c →
    (∀ ct v, sched.cur_thread st s = ok ct → obj.Tcb.flags st ct (L.wr s (regA ct layout.reg.FAULT_IP) v)
      ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄) →
    (∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64)
      (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
        JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
        KDispHypsKVU29 (L := L) arI AR (Z.mv Z.G V') H Cs D' s' a' σb n c) →
    (∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64)
      (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
        JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
        ∀ ct', sched.cur_thread st s' = ok ct' →
          JDecMRLK (L := L) arI VtxK AR MR (Z.mv Z.G V') H Cs D' s' a' σb ct') →
    (∀ x ∈ (specFront c σ).1, ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64)
      (D' : Set U64) (s' : S) (a' : A), KFrontF (L := L) arI n s a s' a' →
        JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 →
        KFinAtR13 (L := L) arI AR Z' H' Cs' s' a' x.2) →
    R ⦃ r =>
      ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧
        RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
        SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ SInvUZ.UtPgR σ' ∧ JReachU17 (L := L) arI AR MR r.1 r.2 σ' ⦄

/-- **U29's unknown-syscall clause** (its text) at `(s, a, σ)`, for the run `R`. -/
def SysUClU29 (s : S) (a : A) (σ : Fl4Spec.State Unit) (n : I64) (R : Result (S × A)) : Prop :=
  σ.curThread ≠ σ.idleThread → UnkSys (L := L) n s → NoDbgSys (L := L) arI n s a →
    (∀ ev, KEvSpec (.sysU n) true ev → ∀ w ∈ (Fl4Spec.fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
      KFinEv13 (L := L) arI AR ev (KFrontSysU (st := st) arI n s a) w.2) →
    R ⦃ r => ∃ ev σ', KEvSpec (.sysU n) true ev ∧ EvOut true ev σ σ' ∧
      RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
      SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU17 (L := L) arI AR MR r.1 r.2 σ' ⦄

/-- **U29's VM-fault clause** (its text) at `(s, a, σ)`, for the run `R`. -/
def VmClU29 (s : S) (a : A) (σ : Fl4Spec.State Unit) (ad c : U64) (ft : Fl4Spec.VMFaultType)
    (R : Result (S × A)) : Prop :=
  σ.curThread ≠ σ.idleThread → VmfHw ad c ft σ →
    KFinEv13 (L := L) arI AR (.vmFaultEvent ft) (KFrontF2 (st := st) arI (brV (st := st) arI ad c) s a) σ →
    R ⦃ r => ∃ σ', EvOut false (.vmFaultEvent ft) σ σ' ∧
      RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
      SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU17 (L := L) arI AR MR r.1 r.2 σ' ⦄

/-- **The joint state a declined local entry leaves the general entry**: the entry state
`(s, a)` at `σ` (declined before any write), or the entry state with the Arch value a clock
reading left (`arI.now a = ok (n1, a')`) at **`tick σ`** (`Fl4Spec.fl4ClockTick`: one consumed
clock-oracle reading). -/
def DeclAt (s : S) (a : A) (σ : Fl4Spec.State Unit) (s' : S) (a' : A) (σ0 : Fl4Spec.State Unit) : Prop :=
  (s' = s ∧ a' = a ∧ σ0 = σ) ∨ (∃ n1, arI.now a = ok (n1, a') ∧ σ0 = Fl4Spec.fl4ClockTick σ)

/-- **A declined syscall-type local entry ending at `(s', a')`**: at the joint state `DeclAt`
gives (`σ0 = σ` or `tick σ`), with ghosts relating it, the general entry
`handle_syscall … s' a' n` has U29's syscall clause (every `c`) and its unknown-syscall clause. -/
def DeclSysU29 (s : S) (a : A) (σ : Fl4Spec.State Unit) (n : I64) (s' : S) (a' : A) : Prop :=
  ∃ σ0, DeclAt arI s a σ s' a' σ0 ∧
    ∃ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a' σ0 ∧
      (∀ c, SysClU29 (L := L) arI AR MR Z H Cs s a' σ0 n c (syscall.handle_syscall st arI s' a' n)) ∧
      SysUClU29 (L := L) arI AR MR s a' σ0 n (syscall.handle_syscall st arI s' a' n)

/-- **A declined `handle_vm_fault_local` ending at `(s', a')`**: at the joint state `DeclAt`
gives, the general entry `handle_vm_fault … s' a'` has U29's VM-fault clause. -/
def DeclVmU29 (s : S) (a : A) (σ : Fl4Spec.State Unit) (ad c : U64) (s' : S) (a' : A) : Prop :=
  ∃ σ0, DeclAt arI s a σ s' a' σ0 ∧
    ∀ ft, VmClU29 (L := L) arI AR MR s a' σ0 ad c ft (syscall.handle_vm_fault st arI s' a' ad c)

set_option maxHeartbeats 8000000 in
/-- **A declined syscall-type entry** (the entry state, or the prefix with `RoT`): `DeclSysU29`. -/
theorem declSys_of [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR) (hIo : MRKeepIo arI MR) (hIoa : MRKeepIoapic arI MR)
    (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hPI : PortInValMR arI MR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hJ : JReachU17 (L := L) arI AR MR s a σ)
    {n : I64} {s' : S} {a' : A}
    (hd : (s' = s ∧ a' = a) ∨ (P1.LocalPre (st := st) arI s a (s', a') ∧ P1.RoT st s n)) :
    DeclSysU29 (L := L) arI AR MR s a σ n s' a' := by
  rcases hd with ⟨rfl, rfl⟩ | ⟨hP, hR⟩
  · obtain ⟨Z, H, Cs, Ac, Lst, D, J, -, -, -, -, -, -, -, hSys, -, -, -, -, hSU⟩ :=
      kernel_entry_reachU29 arI AR MR hARI hA hnd hM hKD hIo hIoa hPA hIA hT hmax htu hRef hPI hSX hDR hJ
    exact ⟨σ, Or.inl ⟨rfl, rfl, rfl⟩, Z, H, Cs, Ac, Lst, D, J, fun c => hSys n c, hSU n⟩
  · obtain ⟨Z0, H0, Cs0, Ac0, Lst0, D0, J0, -⟩ := jreach_invU3 hnd hJ.1
    obtain ⟨hTP, hN, hcT⟩ := P1.BXI.tcbNode J0.bxi
    obtain ⟨n1, hn⟩ := P1.localPre_now arI hA hTP hN hcT hP
    have hJ' := jreachU17_tick hnd hARI hM hJ hn
    obtain ⟨Z, H, Cs, Ac, Lst, D, J, -, -, -, -, -, -, -, hSys, -, -, -, -, hSU⟩ :=
      kernel_entry_reachU29 arI AR MR hARI hA hnd hM hKD hIo hIoa hPA hIA hT hmax htu hRef hPI hSX hDR hJ'
    have e := P1.handle_syscall_pre_same arI hSX hA hTP hN hcT hP hR
    dsimp only at e
    refine ⟨_, Or.inr ⟨n1, hn, rfl⟩, Z, H, Cs, Ac, Lst, D, J, fun c => ?_, ?_⟩
    · rw [e]; exact hSys n c
    · rw [e]; exact hSU n

set_option maxHeartbeats 8000000 in
/-- **A declined `handle_vm_fault_local`** (one `update_timestamp`): `DeclVmU29`. -/
theorem declVm_of [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR) (hIo : MRKeepIo arI MR) (hIoa : MRKeepIoapic arI MR)
    (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hPI : PortInValMR arI MR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hJ : JReachU17 (L := L) arI AR MR s a σ)
    {ad c : U64} {s' : S} {a' : A} (hd : sched.update_timestamp st arI s a = ok (s', a')) :
    DeclVmU29 (L := L) arI AR MR s a σ ad c s' a' := by
  obtain ⟨Z0, H0, Cs0, Ac0, Lst0, D0, J0, -⟩ := jreach_invU3 hnd hJ.1
  obtain ⟨-, hN, -⟩ := P1.BXI.tcbNode J0.bxi
  obtain ⟨n1, hn, -⟩ := P1.ut_now arI hA hN hd
  have hJ' := jreachU17_tick hnd hARI hM hJ hn
  obtain ⟨_, _, _, _, _, _, _, -, -, -, -, -, -, -, -, -, -, hVm, -, -⟩ :=
    kernel_entry_reachU29 arI AR MR hARI hA hnd hM hKD hIo hIoa hPA hIA hT hmax htu hRef hPI hSX hDR hJ'
  have e := P1.vm_pre_same arI hSX hA hN hd ad c
  dsimp only at e
  refine ⟨_, Or.inr ⟨n1, hn, rfl⟩, fun ft => ?_⟩
  rw [e]; exact hVm ad c ft

set_option maxHeartbeats 8000000 in
/-- **`kernel_entry_reachU29` for the local entries' declined runs** (module docstring): from a
`JReachU17` state and U29's premises (verbatim, nothing added), each of fl4-sync's five local
entries, where it returns `false`, leaves a state from which the general entry fl4-sync then
runs has the postcondition of U29's clause for that entry: the syscall and unknown-syscall
clauses for `handle_syscall` after `handle_syscall_local`, `handle_reply_recv_vm_local`,
`handle_ioport_local`, `handle_invocation_local`, the VM-fault clause for `handle_vm_fault` after
`handle_vm_fault_local`. **The declined case relates to `tick σ`**: where the local entry read
the clock (`arI.now a = ok (n1, a')`), the clause holds at the joint state `(s, a', tick σ)`
(`Fl4Spec.fl4ClockTick`: one consumed clock-oracle reading), so the spec event starts from
`tick σ`; where it declined before writing, at `(s, a, σ)` (`DeclAt`). -/
theorem kernel_entry_reachU29D [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR) (hIo : MRKeepIo arI MR) (hIoa : MRKeepIoapic arI MR)
    (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hPI : PortInValMR arI MR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hJ : JReachU17 (L := L) arI AR MR s a σ) :
    (∀ (ad c : U64), syscall.handle_vm_fault_local st arI s a ad c ⦃ r =>
      r.1 = false → DeclVmU29 (L := L) arI AR MR s a σ ad c r.2.1 r.2.2 ⦄) ∧
    (∀ (n : I64) (found : U64 × U64), syscall.handle_syscall_local st arI s a n found ⦃ r =>
      r.1 = false → DeclSysU29 (L := L) arI AR MR s a σ n r.2.1 r.2.2 ⦄) ∧
    (∀ (found : U64 × U64), syscall.handle_reply_recv_vm_local st arI s a found ⦃ r =>
      r.1 = false → DeclSysU29 (L := L) arI AR MR s a σ fl4_abi.syscall.SysReplyRecv r.2.1 r.2.2 ⦄) ∧
    (∀ (n : I64), syscall.handle_ioport_local st arI s a n ⦃ r =>
      r.1 = false → DeclSysU29 (L := L) arI AR MR s a σ n r.2.1 r.2.2 ⦄) ∧
    (∀ (n : I64) (p : localinv.Plan), syscall.handle_invocation_local st arI s a n p ⦃ r =>
      r.1 = false → DeclSysU29 (L := L) arI AR MR s a σ n r.2.1 r.2.2 ⦄) := by
  refine ⟨fun ad c => ?_, fun n found => ?_, fun found => ?_, fun n => ?_, fun n p => ?_⟩
  · obtain ⟨⟨b, s', a'⟩, e, -⟩ := P1.spec_ex_fd (P0.syscall.handle_vm_fault_local.p0 st arI s a ad c L.total hA)
    rw [e, WP.spec_ok]
    intro hb
    simp only at hb
    subst hb
    exact declVm_of arI AR MR hARI hA hnd hM hKD hIo hIoa hPA hIA hT hmax htu hRef hPI hSX hDR hJ
      (P1.vm_local_decline arI e)
  · obtain ⟨⟨b, s', a'⟩, e, -⟩ :=
      P1.spec_ex_fd (P0.syscall.handle_syscall_local.p0 st arI s a n found L.total hA)
    rw [e, WP.spec_ok]
    intro hb
    simp only at hb
    subst hb
    exact declSys_of arI AR MR hARI hA hnd hM hKD hIo hIoa hPA hIA hT hmax htu hRef hPI hSX hDR hJ
      (P1.syscall_local_decline arI e)
  · obtain ⟨⟨b, s', a'⟩, e, -⟩ :=
      P1.spec_ex_fd (P0.syscall.handle_reply_recv_vm_local.p0 st arI s a found L.total hA)
    rw [e, WP.spec_ok]
    intro hb
    simp only at hb
    subst hb
    exact declSys_of arI AR MR hARI hA hnd hM hKD hIo hIoa hPA hIA hT hmax htu hRef hPI hSX hDR hJ
      (P1.rr_vm_local_decline arI e)
  · obtain ⟨⟨b, s', a'⟩, e, -⟩ :=
      P1.spec_ex_fd (P0.syscall.handle_ioport_local.p0 st arI s a n L.total hA)
    rw [e, WP.spec_ok]
    intro hb
    simp only at hb
    subst hb
    exact declSys_of arI AR MR hARI hA hnd hM hKD hIo hIoa hPA hIA hT hmax htu hRef hPI hSX hDR hJ
      (P1.ioport_local_decline arI e)
  · obtain ⟨⟨b, s', a'⟩, e, -⟩ :=
      P1.spec_ex_fd (P0.syscall.handle_invocation_local.p0 st arI s a n p L.total hA)
    rw [e, WP.spec_ok]
    intro hb
    simp only at hb
    subst hb
    exact declSys_of arI AR MR hARI hA hnd hM hKD hIo hIoa hPA hIA hT hmax htu hRef hPI hSX hDR hJ
      (P1.invocation_local_decline arI e)

end

end

end Fl4Proofs.P3.SInvR.G5
