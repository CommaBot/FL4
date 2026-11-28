/-
P3 (DESIGN.md §9), invariant line G4 (g4b, KENTRY-PLAN g4b; g4a's handoff
(G-b)): **`MR` at the exit of the syscall entry**, and the induction
`JReachM` / `jreach_invM` / `kernel_entry_reachM` whose step relation is the
one the refinement now delivers (`RJ ∧ MR`).

* `jat_finishJRNM`: FL4's `finish` from `JAtZR` with `MR a σ.ms` ends related
  (`RJ`) to an outcome of the spec's `fl4Awaken; schedule; activateThread` and
  `MR` holds there: `jat_finishJRN` with the FL4 walk `MKD.syscall_finish`
  (MachKeepF: every arch operation reached keeps `MR` at a fixed machine
  state, `MRKeepD`) and the spec frame `MachT.mtk_finish` (MachFieldFamS: the
  four machine fields `MR` reads are kept), by `MachPlat.frame`.
* `PPQJIM` / `DispPostRM`: `PPQJI` / `DispPostR` with `MR` at the chosen
  outcome. `JDispMR` [W] (the one carry left open, narrowed from g4a's "MR at
  the exit"): at a dispatch state with `MR`, every run of `dispatch_syscall`
  that `DispPostR` relates to some spec outcome is related (`DispPostRM`) to
  an outcome where `MR` holds. Pointwise and existential on purpose: the spec
  at `State Unit` is nondeterministic in the oracle positions (`orChoiceE`
  of `preemptionPoint` is a free choice there, `StateExt.wrapExtBool`), so
  "every related outcome has `MR`" is false (two outcomes differing only in
  `timeState` / `irqState`); only the outcome the FL4 run matches has it.
  l4v: the machine state is shared, every `do_machine_op` of the abstract
  run is matched by the concrete one (`corres` of `preemption_point`,
  `maskInterrupt`, ...).
* `kernel_entryJ13PUGM` = `kernel_entryJ13PUG` (same body) with `MR` carried
  to every exit: the stopping budget check (`budget_mr_at` at `false`), the
  dispatch's ok outcomes and its preempted outcomes (`JDispMR`), then
  `finish` (`jat_finishJRNM`, `kPreFinAtGM`). Post `KPostM` = `KPost` with
  `MR r.2 σ'.ms`.
* **`kernel_entryJ36`** = `kernel_entryJ35` with post `KPostXM` (`KPostX` and
  `MR`), one more per-state premise `hDM` (`JDispMR`, asked at the same
  dispatch states as `hK`), `hFast` asked for `KPostM`.
* `JReachM`: `start` as `JReach`; `step` along `RJM := RJ ∧ MR`, the exit
  relation `kernel_entryJ36` delivers. `jreach_invM`, and
  **`kernel_entry_reachM`**: every related exit is again reachable (no `MR →`
  left: g4a's gap (G-b) is closed up to `JDispMR`).
-/
import Fl4Proofs.P3.XTopJointKEntry35
import Fl4Proofs.P3.MachKeepF
import Fl4Proofs.P3.MachFieldFamS
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.G4

noncomputable section

/-! ## The finish with `MR` -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 4000000 in
/-- **`jat_finishJRN` with `MR` after** (module docstring). -/
theorem jat_finishJRNM {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ) [VxE Z] (hN : NativeScope σ)
    (hd : σ.domainTime ≠ 0 ∨ NdOK (L := L) s σ)
    (hnd : Fl4Spec.numDomains = 1) (hAT : P0.ArchTotal arI)
    (hVt : ∀ (V1 : XVs) (s1 : S) (a1 : A) (σ1 : Fl4Spec.State Unit) (Ac1 : Set U64) (Lst1 : U64 → List U64)
      (D1 : Set U64), JAtZR (L := L) arI AR (Z.mv Z.G V1) H Cs Ac1 Lst1 D1 s1 a1 σ1 → ∀ t ∈ Z.T,
        Z.th t = some .tcb ∧ ∀ p asid, capAt (L.mem s1) (slotOf t 1) = ok (.Pml4 p true asid) → asid ≠ 0#u64)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hA : ArchSwF st arI Z.N Z.T Z.C Z.c) (hAN : ArchNdF st Z.N Z.T Z.C Z.c) (hFO : FinRootI arI AR σ)
    (hsni : SniHyp st arI Z.N Z.T Z.C Z.c) (hsend : SendHyp st arI Z.N Z.T Z.C Z.c) (hT : TimeAgree arI)
    (hTail : sched.schedule st arI s a ⦃ r => ∀ (rf : S × A) σ1 σ' (D1 : Set U64), Fires σ σ1 →
      timer.fire st arI s a = ok rf →
      ((∃ (V1 : XVs) (Ac1 : Set U64) (Lst1 : U64 → List U64) (D2 : Set U64),
        JAtZR (L := L) arI AR (Z.mv Z.G V1) H Cs Ac1 Lst1 D2 rf.1 rf.2 σ1) ∨
       ∃ (V1 : XVs) (Ac1 : Set U64) (Lst1 : U64 → List U64) (D2 : Set U64),
        JAtZ (L := L) arI AR (Z.mv Z.G V1) H Cs Ac1 Lst1 D2 rf.1 rf.2 σ1) →
      Fl4Spec.schedule (Z := Unit) σ1 = ({((), σ')}, False) →
      P1.WritesIn st rf.1 r.1 (KFootN st Z.T Z.N Z.C Z.c rf.1 σ1) →
      SchedRel st Z.N Z.T Z.C Z.c r.1 σ' → Inv σ' → CurInv σ' → ActIdle σ' →
      SchTailHypsR AR Z H D1 r.1 r.2 σ' ⦄)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hM : MachPlat arI MR) (hKD : MRKeepD arI MR) (hR : MR a σ.machineState) :
    syscall.finish st arI s a ⦃ r => ∃ σ',
      ((), σ') ∈ ((Fl4Spec.fl4Awaken (Z := Unit) >>= fun _ => Fl4Spec.schedule >>= fun _ => Fl4Spec.activateThread) σ).1 ∧
      RJ (L := L) arI AR r.1 r.2 σ' ∧ MR r.2 σ'.machineState ⦄ := by
  refine WP.spec_mono (WP.spec_and (jat_finishJRN s a σ J hN hd hnd hAT hVt hmb hA hAN hFO hsni hsend hT hTail hmax
    htu) (MKD.syscall_finish L.total hAT hKD hR)) ?_
  rintro r ⟨⟨_, σ', _, _, hmem, hRJ, _⟩, hMR⟩
  exact ⟨σ', hmem, hRJ, msF_mr hM hMR (congrArg Prod.fst (MachT.mtk_finish hmem))⟩

end

/-! ## The dispatch posts with `MR` and the open carry -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **`PPQJI` with `MR` at the path's outcome.** -/
def PPQJIM (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop) (σ1 : Fl4Spec.State Unit)
    (r : S × A) : Prop :=
  ∃ z ∈ (Fl4Spec.preemptionPath (Z := Unit) σ1).1, JAt (L := L) arI AR r.1 r.2 z.2 ∧ MR r.2 z.2.machineState

/-- **`DispPostR` (at `PPQJI`) with `MR` at the chosen outcome.** -/
def DispPostRM (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)
    (m : Fl4Spec.PMonad Unit Unit) (σ : Fl4Spec.State Unit) (r : S × A) : Prop :=
  ∃ y ∈ (m.run σ).1,
    (y.1 = .ok () ∧ RelTopM (L := L) r.1 y.2 ∧ (∃ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64)
      (Lst : U64 → List U64) (D : Set U64), JAtZR (L := L) arI AR Z H Cs Ac Lst D r.1 r.2 y.2 ∧ VxE Z) ∧
      MR r.2 y.2.machineState) ∨
    (y.1 = .error () ∧ PPQJIM (L := L) arI AR MR y.2 r)

/-- **[W] The dispatch's `MR` completion** (module docstring): at a dispatch
state with `MR`, a run of `dispatch_syscall` related by `DispPostR` is
related by `DispPostRM`. -/
def JDispMR (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) (n : I64) (c : Fl4Spec.Syscall) : Prop :=
  MR a σ.machineState → syscall.dispatch_syscall st arI s a n ⦃ r =>
    DispPostR (L := L) arI AR (PPQJI (L := L) arI AR) (Fl4Spec.fl4HandleSyscall true c) σ r →
    DispPostRM (L := L) arI AR MR (Fl4Spec.fl4HandleSyscall true c) σ r ⦄

/-- **`KPost` with `MR` at the chosen outcome.** -/
def KPostM (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop) (c : Fl4Spec.Syscall)
    (σ : Fl4Spec.State Unit) (r : S × A) : Prop :=
  (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).2 ∨
  ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧ RJ (L := L) arI AR r.1 r.2 σ' ∧
    MR r.2 σ'.machineState

/-- **`KPostX` with `MR`**: the post of `kernel_entryJ36`. -/
def KPostXM (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop) (c : Fl4Spec.Syscall)
    (σ : Fl4Spec.State Unit) (r : S × A) : Prop :=
  (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).2 ∨
  ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧ RJ (L := L) arI AR r.1 r.2 σ' ∧
    MR r.2 σ'.machineState ∧ SInvX σ'

variable {arI}

theorem KPostM.toK {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop} {c : Fl4Spec.Syscall}
    {σ : Fl4Spec.State Unit} {r : S × A} (h : KPostM (L := L) arI AR MR c σ r) : KPost (L := L) arI AR c σ r :=
  h.imp id fun ⟨σ', h1, h2, _⟩ => ⟨σ', h1, h2⟩

end

/-! ## `kernel_entryJ13PUG` with `MR` at every exit -/

/-! ## The top -/

/-! ## The induction along `RJ ∧ MR` -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)

/-- **The exit relation `kernel_entryJ36` delivers**: `RJ` and `MR`. -/
abbrev RJM (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop :=
  RJ (L := L) arI AR s a σ ∧ MR a σ.machineState

/-- **The reachable joint states along `RJM`** (module docstring): `start` as
`JReach`; `step` a native syscall from a non-idle thread whose FL4 entry
returns `(s', a')`, with a spec outcome `σ'` of the entry related to it by
the refinement's exit relation `RJM` (which `kernel_entry_reachM` produces;
a related outcome without `MR` need not be reachable, module docstring). -/
inductive JReachM : S → A → Fl4Spec.State Unit → Prop
  | start {s : S} {a : A} {σ : Fl4Spec.State Unit} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
      {Lst : U64 → List U64} {D : Set U64} :
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → SInvX σ → MR a σ.machineState → JReachM s a σ
  | step {s : S} {a : A} {σ : Fl4Spec.State Unit} {s' : S} {a' : A} {σ' : Fl4Spec.State Unit} (n : I64)
      (c : Fl4Spec.Syscall) :
      JReachM s a σ → σ.curThread ≠ σ.idleThread → NativeSys n c →
      syscall.handle_syscall st arI s a n = ok (s', a') →
      ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 →
      RJM (L := L) arI AR MR s' a' σ' → JReachM s' a' σ'

variable {arI AR MR}

end

end

end Fl4Proofs.P3
