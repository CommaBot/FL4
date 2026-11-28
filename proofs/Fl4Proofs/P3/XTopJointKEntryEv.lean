/-
P3 (DESIGN.md §9), invariant line G4 (g4e, KENTRY-PLAN g4e; g4c's handoff
"`fl4CallKernel` for the other events"): **the induction with event steps**,
and the syscall top with both g4c's no-fail post and g4b's `MR` carry.

* `KPostMS` / `KPostXMS`: an outcome σ' of the spec syscall entry (no
  spec-fails disjunct, g4c) with `RJ` and `MR` (g4b), and `SInvX σ'`.
* `kPreFinAtGMS` / `kernel_entryJ13PUGMS`: g4b's `kPreFinAtGM` /
  `kernel_entryJ13PUGM` (same bodies) with the post `KPostMS`. As g4c found
  for `kernel_entryJ13PUG`, the fail disjunct was produced only at the
  preemption branch, from `kPreFinAtGM`'s left disjunct, which its own proof
  never produces.
* **`kernel_entryJ37N`**: `kernel_entryJ37`'s premises (`hDM : JDispMRI`
  [W]), `hFast` [P] at `KPostMS`, post `KPostXMS`.
* Events. No joint refinement theorem exists for any non-syscall FL4 entry
  (`handle_interrupt_entry`, `handle_user_exception`, `handle_vm_fault`, the
  unknown-syscall arm of `handle_syscall`, `handle_trap_syscall`; KENTRY-PLAN
  g4e (1)): only pieces (`JAtZ.handleIrqJIN`, `JAtZ.budgetOkB`, the
  cap-fault `faultHypJZ*` family, `jat_finishJRNM`). `KEv` names those FL4
  entries, `KEvSpec` the spec event each refines (with `fip` when the spec
  event follows the FaultIP write of the current thread: the unknown syscall
  and `int $N` entries, as FL4 writes `FAULT_IP` before deciding), `EvOut` the
  spec outcome. **`JEvRef` [W]** is the named per-step premise: the FL4 entry
  at this state returns and is related (`RJM := RJ ∧ MR`, no spec-fails
  disjunct) to an outcome of the spec event. **`SInvXFip` [W]** (only for
  the two `fip` entries): `SInvX` after the FaultIP write at this state
  (`kcall_sinvX` covers `fl4CallKernel` only; the FaultIP prefix is carried
  for the syscall events inside `kentry_sinvX`, not as a separate lemma).
* **`JReachE`**: `start` (any `JAtZ ∧ SInvX ∧ MR` state), `step` (a native
  syscall along `RJM`, as `JReachM`), `event` (an FL4 event entry along
  `RJM` to an `EvOut` outcome). **`jreach_invE`**: `JAtZ ∧ SInvX ∧ MR` at
  every reachable state (`kentry_sinvX` / `kcall_sinvX`). **`kernel_entry_reachE`**:
  at a reachable state, the syscall entry (via `kernel_entryJ37N`) and every
  event entry with its `JEvRef` end in a related outcome with `SInvX`, `MR`,
  reachable again: one induction for `JAtZ ∧ SInvX ∧ MR`, no spec-fails case,
  no `MR` premise in any step.
-/
import Fl4Proofs.P3.XTopJointKEntryNF
import Fl4Proofs.P3.XTopJointKEntry37
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.G4

noncomputable section

/-! ## The posts -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **`KPostM` without the spec-fails disjunct** (module docstring). -/
def KPostMS (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop) (c : Fl4Spec.Syscall)
    (σ : Fl4Spec.State Unit) (r : S × A) : Prop :=
  ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧ RJ (L := L) arI AR r.1 r.2 σ' ∧
    MR r.2 σ'.machineState

/-- **`KPostXM` without the spec-fails disjunct**: the post of `kernel_entryJ37N`. -/
def KPostXMS (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop) (c : Fl4Spec.Syscall)
    (σ : Fl4Spec.State Unit) (r : S × A) : Prop :=
  ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧ RJ (L := L) arI AR r.1 r.2 σ' ∧
    MR r.2 σ'.machineState ∧ SInvX σ'

variable {arI}

theorem KPostMS.toM {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop} {c : Fl4Spec.Syscall}
    {σ : Fl4Spec.State Unit} {r : S × A} (h : KPostMS (L := L) arI AR MR c σ r) : KPostM (L := L) arI AR MR c σ r :=
  Or.inr h

theorem KPostXMS.toXM {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop} {c : Fl4Spec.Syscall}
    {σ : Fl4Spec.State Unit} {r : S × A} (h : KPostXMS (L := L) arI AR MR c σ r) :
    KPostXM (L := L) arI AR MR c σ r :=
  Or.inr h

theorem KPostXMS.toXS {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop} {c : Fl4Spec.Syscall}
    {σ : Fl4Spec.State Unit} {r : S × A} (h : KPostXMS (L := L) arI AR MR c σ r) :
    KPostXS (L := L) arI AR c σ r :=
  let ⟨σ', h1, h2, _, h4⟩ := h; ⟨σ', h1, h2, h4⟩

end

/-! ## `kernel_entryJ13PUGM` without the spec-fails disjunct -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {MR : A → Fl4Spec.MachineState → Prop}

/-- **`kPreFinAtGM` without the spec-fails disjunct** (module docstring). -/
theorem kPreFinAtGMS {c : Fl4Spec.Syscall} {σ : Fl4Spec.State Unit} {r : S × A}
    (hFin : ∀ x ∈ (specFront c σ).1, ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64)
      (D' : Set U64), JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' r.1 r.2 x.2 →
        KFinAtR (L := L) arI AR Z' H' Cs' r.1 r.2 x.2)
    (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hNS0 : NativeScope σ)
    (hT : TimeAgree arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hM : MachPlat arI MR) (hKD : MRKeepD arI MR)
    (σ1 : Fl4Spec.State Unit) (hPA : PreemptedAt c σ σ1) (hQ : PPQJIM (L := L) arI AR MR σ1 r) :
    syscall.finish st arI r.1 r.2 ⦃ r' =>
      ∃ z ∈ (Fl4Spec.preemptionPath (Z := Unit) σ1).1, ∃ σ',
        ((), σ') ∈ ((Fl4Spec.fl4Awaken (Z := Unit) >>= fun _ => Fl4Spec.schedule >>= fun _ => Fl4Spec.activateThread) z.2).1 ∧
        RJ (L := L) arI AR r'.1 r'.2 σ' ∧ MR r'.2 σ'.machineState ⦄ := by
  obtain ⟨z, hz, ⟨Zm, Hm, Csm, Acm, Lstm, Dm, Jm, _⟩, hMz⟩ := hQ
  obtain ⟨σb, ⟨σ0, hF, hb⟩, hy⟩ := hPA
  have hx : ((.ok z.1, z.2) : Except Unit Unit × Fl4Spec.State Unit) ∈ (specFront c σ).1 :=
    mem_specFront hF (mem_handleE_err (mem_fl4HandleEvent hb (mem_whenE_true hy)) (mem_liftE hz))
  have F := hFin _ hx Zm Hm Csm Acm Lstm Dm Jm.toR
  exact WP.spec_mono (jat_finishJRNM r.1 r.2 z.2 Jm.toR (SInvN.ns_front true c hNS0 _ hx) F.hd hnd hA F.vt hmb
      F.arch F.archNd F.fo F.sni F.send hT F.tail hmax htu hM hKD hMz)
      fun r' ⟨σ', hmem, hRJ, hM'⟩ => ⟨z, hz, σ', hmem, hRJ, hM'⟩

end

/-! ## The syscall top: no spec-fails disjunct and `MR` at the exit -/

/-! ## The non-syscall entries -/

/-- **The non-syscall FL4 entries** (module docstring): an interrupt
(`handle_interrupt_entry`), a user exception (`handle_user_exception`), a
user page fault (`handle_vm_fault`), a syscall number `handle_syscall` treats
as unknown (out of range, or trapped by `TRAP_SYSCALLS`), and x86 `int $N`
(`handle_trap_syscall`). Not here: `handle_debug_exception` (the hardware
debug API has no spec event) and `handle_vcpu_exit` (VT-x), both [S]. -/
inductive KEv where
  | irq (w : U64)
  | user (number code : U64)
  | vmf (addr code : U64)
  | sysU (n : I64)
  | trap (vector : U64)

/-- The FL4 function each `KEv` runs. -/
def KEv.run {S A : Type} (st : machine.Store S) (arI : machine.Arch A) : KEv → S → A → Result (S × A)
  | .irq w, s, a => syscall.handle_interrupt_entry st arI s a w
  | .user n c, s, a => syscall.handle_user_exception st arI s a n c
  | .vmf ad c, s, a => syscall.handle_vm_fault st arI s a ad c
  | .sysU n, s, a => syscall.handle_syscall st arI s a n
  | .trap v, s, a => syscall.handle_trap_syscall st arI s a v

/-- **The spec event each FL4 entry refines** and whether the FaultIP write
comes first (`fip`): l4v's `Interrupt`, `UserLevelFault`, `VMFaultEvent`
(the fault kind from the error code), `UnknownSyscall` (the number FL4
reports, trapped or not); `int $N` is an unknown syscall, or under
`TRAP_SYSCALLS` the #GP user exception FL4 raises. The exact argument
values are part of the per-step premise `JEvRef`. -/
inductive KEvSpec : KEv → Bool → Fl4Spec.Event → Prop
  | irq (w : U64) : KEvSpec (.irq w) false .interrupt
  | user (n c : U64) : KEvSpec (.user n c) false (.userLevelFault n.bv c.bv)
  | vmf (ad c : U64) (ft : Fl4Spec.VMFaultType) : KEvSpec (.vmf ad c) false (.vmFaultEvent ft)
  | sysU (n : I64) (m : Nat) : KEvSpec (.sysU n) true (.unknownSyscall m)
  | trapU (v : U64) (m : Nat) : KEvSpec (.trap v) true (.unknownSyscall m)
  | trapF (v : U64) (w1 w2 : Fl4Spec.Word) : KEvSpec (.trap v) true (.userLevelFault w1 w2)

/-- A `KEvSpec` event is not a syscall event. -/
theorem KEvSpec.not_sys {e : KEv} {fip : Bool} {ev : Fl4Spec.Event} (h : KEvSpec e fip ev) :
    ∀ c, ev ≠ .syscallEvent c := by
  cases h <;> intro c e <;> cases e

/-- **An outcome of the spec event**, after the FaultIP write of the current
thread when `fip`. -/
def EvOut (fip : Bool) (ev : Fl4Spec.Event) (σ σ' : Fl4Spec.State Unit) : Prop :=
  match fip with
  | false => ((), σ') ∈ (Fl4Spec.fl4CallKernel (Z := Unit) true ev σ).1
  | true => ∃ w ∈ (Fl4Spec.fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
      ((), σ') ∈ (Fl4Spec.fl4CallKernel (Z := Unit) true ev w.2).1

/-- **[W] `SInvX` after the FaultIP write at this state** (module docstring;
asked only for the `fip` entries, at their entry state). -/
def SInvXFip (σ : Fl4Spec.State Unit) : Prop :=
  ∀ w ∈ (Fl4Spec.fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1, SInvX w.2

/-- **`SInvX` at every event outcome** (`kcall_sinvX`; across the FaultIP
write by `SInvXFip`, which keeps the current and idle thread). -/
theorem sinvX_evOut (hnd : Fl4Spec.numDomains = 1) {fip : Bool} {ev : Fl4Spec.Event} {σ σ' : Fl4Spec.State Unit}
    (hX : SInvX σ) (hev : ev ≠ .interrupt → σ.curThread ≠ σ.idleThread) (hF : fip = true → SInvXFip σ)
    (h : EvOut fip ev σ σ') : SInvX σ' := by
  cases fip with
  | false => exact kcall_sinvX hnd true ev hX hev _ h
  | true =>
    obtain ⟨w, hw, hy⟩ := h
    have hc := SInvR.A8.cfk_fip σ.curThread σ w hw
    have ect : w.2.curThread = σ.curThread := congrArg (fun p => p.2.2.1) hc
    have eid : w.2.idleThread = σ.idleThread := congrArg (fun p => p.2.2.2.1) hc
    exact kcall_sinvX hnd true ev (hF rfl w hw) (fun he => by rw [ect, eid]; exact hev he) _ hy

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **[W] The per-step premise of an event** (module docstring): the FL4
entry `e` at this state returns, related (`RJM`: `RJ ∧ MR`) to an outcome
of the spec event. Missing as a theorem for every `KEv` (KENTRY-PLAN g4e
(1)); its [P] part is that the entry's arguments are the ones the spec
reads from the machine (the pending line, the fault address and kind). -/
def JEvRef (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop) (e : KEv) (fip : Bool)
    (ev : Fl4Spec.Event) (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop :=
  e.run st arI s a ⦃ r => ∃ σ', EvOut fip ev σ σ' ∧ RJM (L := L) arI AR MR r.1 r.2 σ' ⦄

end

/-! ## The induction with event steps -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)

/-- **The reachable joint states with syscall and event steps** (module
docstring). `event`'s `fip = true → SInvXFip σ` is the [W] carry of the two
`fip` entries, asked at the step. -/
inductive JReachE : S → A → Fl4Spec.State Unit → Prop
  | start {s : S} {a : A} {σ : Fl4Spec.State Unit} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
      {Lst : U64 → List U64} {D : Set U64} :
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → SInvX σ → MR a σ.machineState → JReachE s a σ
  | step {s : S} {a : A} {σ : Fl4Spec.State Unit} {s' : S} {a' : A} {σ' : Fl4Spec.State Unit} (n : I64)
      (c : Fl4Spec.Syscall) :
      JReachE s a σ → σ.curThread ≠ σ.idleThread → NativeSys n c →
      syscall.handle_syscall st arI s a n = ok (s', a') →
      ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 →
      RJM (L := L) arI AR MR s' a' σ' → JReachE s' a' σ'
  | event {s : S} {a : A} {σ : Fl4Spec.State Unit} {s' : S} {a' : A} {σ' : Fl4Spec.State Unit} (e : KEv)
      (fip : Bool) (ev : Fl4Spec.Event) :
      JReachE s a σ → KEvSpec e fip ev → (ev ≠ .interrupt → σ.curThread ≠ σ.idleThread) →
      (fip = true → SInvXFip σ) → e.run st arI s a = ok (s', a') → EvOut fip ev σ σ' →
      RJM (L := L) arI AR MR s' a' σ' → JReachE s' a' σ'

variable {arI AR MR}

/-- Every `JReachM` state is a `JReachE` state. -/
theorem JReachM.toE {s : S} {a : A} {σ : Fl4Spec.State Unit} (h : JReachM (L := L) arI AR MR s a σ) :
    JReachE (L := L) arI AR MR s a σ := by
  induction h with
  | @start s a σ Z H Cs Ac Lst D J hvx hX hR => exact JReachE.start J hvx hX hR
  | @step s a σ s' a' σ' n c _ hct hn hv hy hRJ ih => exact JReachE.step n c ih hct hn hv hy hRJ

end

end

end Fl4Proofs.P3
