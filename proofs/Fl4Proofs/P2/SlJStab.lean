/-
# P2 (line lstab): the layout of a local path's start, threaded from the last serial exit

Line lay (P2/SlJLay.lean) reduced the syscall local path's layout requirement to
`Fl4Step.start`'s `StartAt` [P] at each body start: `SlJAt K σ` for the execution's layout
`K`, which is the layout the last serial entry's `ser` installed (`Fl4Step.keep`). By
`slJAt_of_JAtZ_stable` that holds once `JAtZ` at the start state has the same typed heap `H`,
`Zx.th`, `Zx.B`, kernel-state base and core set `Cs` as the exit's.

## What P3 states (finding of this line)

P3 has no local step of its own: an accepted local entry *is* the general entry
(P1 `syscall_local_same`; `kernel_entry_reachU29S` / `U29Vm` / `U29T`), and every entry of
`JReachU3` / `JReachU17` (serial or local) ends in `RJ` / `RJM` / `JReachU17`, whose ghosts are
existential (`JAt := ∃ Z H Cs Ac Lst D, JAtZ … ∧ VxE Z`). The fixed-ghost shape
`JAtZ (Z.mv Z.G V') H Cs …` in `kernel_entry_reachU17V` / `kernel_entry_reachU29`'s syscall
clause is an *input* of the clause at the dispatch state (after the entry's front `KFrontB`,
inside one entry: `KDispHypsKVU29` / `JDecMRLK` are asked there), not a postcondition of a run;
the finish (`KFinAtR13`) is asked at fresh `Z' H' Cs'`, and the exit is `RJ`. So no top fixes
`H`/`Zx.th`/`Zx.B`/`Cs` across an entry, and the old premises do not imply the new one: the
posts only say *some* ghosts fit the exit state, and `H` is not a function of the state
(`SpecCover` is one-directional, `H` may hold extra `other` objects; `Cs` is any `{c < n}`
with `JKern.csN`, `n` not tied to a state word), so ghosts fitting the exit cannot be
identified with the entry's after the fact. (Internally the IPC steps' posts *are* at
`Z.mv G' V'` with `H`, `Cs` kept, `QX`/`QJ`/`FinXPost`/`WXZ`; they are packaged into `RJ`
before reaching any top.)

## This file
* `JAtSt th B H Cs k`: `JAtZ` at some `Z` with `Z.th = th`, `Z.B = B`, `L.ksb s = k`, the
  given `H`, `Cs` and `VxE Z` (as at every `JReachU17` exit, `jreach_invU3`; line stpost: the
  stable-ghost entry theorems ask it), the other ghosts free.
* `LocRunMv Loc` [J]: the stable-ghost local-run premise, in lay's shape: a local run
  (`Loc`) from `JAtZ Z H Cs …` ends in `JAtZ (Z.mv G' V') H Cs …` with the kernel-state base
  kept. `LocSys`: the accepted `handle_syscall_local` runs with their spec outcomes (U29S's
  two clauses), the instance `sl_pathsK` itself needs.
* `JReachSt Loc th B H Cs k`: the reachability variant with fixed stable ghosts: a
  `JReachU17` state with `JAtSt` (a serial exit, `exit`), closed under `Loc` steps ending in
  `JReachU17` (`loc`). `JReachSt.atSt`: under `LocRunMv`, `JAtSt` at every such state.
* `jreachSt_exit`: at every `JReachU17` state (a serial exit), one choice of ghosts gives both
  `Fl4Step.ser`'s conclusion for `layoutJ Z H (L.ksb s) n` (SerExit's `ser_of_JAtZN`) and the
  start of `JReachSt` at `Z.th`, `Z.B`, `H`, `Cs`, `L.ksb s` — the same ghosts.
* `slJAt_of_jreachSt`, `slJAt_layoutJ_of_jreachSt`: `SlJAt` at every `JReachSt` state for the
  exit's layout (only `numDomains = 1` and `LocRunMv`; no top needed: `jreach_invU3`).
* `jreachSt_sysLoc`: under U29's top premises, `JReachSt` is closed under accepted
  `handle_syscall_local` runs (U29S's two clauses, inputs verbatim): its `JReachU17` side is
  P3's; only the ghost side needs `LocRunMv`.
* `sl_pathsK_startAt_stab`: **`StartAt` for `sl_pathsK` at the exit's layout** at every
  `JReachSt` start state: no layout premise but `LocRunMv` [J].

## What remains
* `LocRunMv` [J] for every local entry that runs between two serial entries (on any core):
  accepted `handle_syscall_local` (`LocSys`: the trap arm's `fastpath.fault` and the ReplyRecv
  fast path), `handle_vm_fault_local`, `handle_reply_recv_vm_local`, the I/O-port and
  invocation local paths, `TCB_SetTimer` and the timer interrupt; declined runs (FAULT_IP and
  one `update_timestamp`, P1 FastLocalDecline). Discharging it means re-threading the
  corresponding P3 entry proofs with posts at `Z.mv G' V'`, `H`, `Cs` (their IPC/fault/timer
  steps never retype or delete), instead of `RJ`.
* User steps between entries (user-word writes): not in P3's reachability either
  (`JReachU3` has no user step); `JAtZ.userWrJ` (P3/XTopJointData) keeps every ghost for an
  IPC-buffer word write, so a user step is a `Loc` step of the same shape.
* The glue identifying an execution's body start with a `JReachSt` state at the exit's ghosts
  (the `StartAt` store state, `Fl4Step.start` [P]), as before.
-/
import Fl4Proofs.P2.SlJLay
import Fl4Proofs.P2.SerExit
import Fl4Proofs.P3.XTopJointKEntryU29S
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2.OwnMap
open Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P3.Vs Fl4Proofs.P3.SInvR.G4 Fl4Proofs.P3.SInvR.G5

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)

/-- **The joint invariant at fixed stable ghosts** (module docstring): `JAtZ` at some `Z`
whose `th` and `B` are the given ones, the typed heap `H` and core set `Cs` given, the
kernel-state base `k`. -/
def JAtSt (th : TypedHeap) (B : Set (U64 × Fl4Spec.Word)) (H : Heap) (Cs : Set U64) (k : U64)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop :=
  ∃ (Z : XSets) (Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
    Z.th = th ∧ Z.B = B ∧ L.ksb s = k ∧ JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ ∧ VxE Z

/-- **[J] A local run keeps the stable ghosts** (module docstring; lay's shape): a run `Loc`
from `JAtZ Z H Cs …` ends in `JAtZ (Z.mv G' V') H Cs …` (only the MDB ghost and the VSpace
sets may change, as P3's XTop step posts), the kernel-state base kept. Not stated by P3
(its entry posts are `RJ`, ghosts existential). -/
def LocRunMv (Loc : S → A → Fl4Spec.State Unit → S → A → Fl4Spec.State Unit → Prop) : Prop :=
  ∀ (Z : XSets) (H : Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) (s' : S) (a' : A) (σ' : Fl4Spec.State Unit),
    JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → Loc s a σ s' a' σ' →
    L.ksb s' = L.ksb s ∧ ∃ (G : MdbGhost) (V : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
      JAtZ (L := L) arI AR (Z.mv G V) H Cs Ac' Lst' D' s' a' σ'

/-- **The accepted syscall local runs** with their spec outcomes (U29S's native and
unknown-syscall clauses). -/
def LocSys (s : S) (a : A) (σ : Fl4Spec.State Unit) (s' : S) (a' : A) (σ' : Fl4Spec.State Unit) : Prop :=
  ∃ (n : I64) (found : U64 × U64), syscall.handle_syscall_local st arI s a n found = ok (true, s', a') ∧
    ((∃ c : Fl4Spec.Syscall, NativeSys n c ∧ ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1) ∨
      (∃ ev, KEvSpec (.sysU n) true ev ∧ EvOut true ev σ σ'))

/-- **The reachable states with fixed stable ghosts** (module docstring): a reachable state
(a serial exit) at the ghosts, then local runs `Loc` ending in reachable states. -/
inductive JReachSt (Loc : S → A → Fl4Spec.State Unit → S → A → Fl4Spec.State Unit → Prop)
    (th : TypedHeap) (B : Set (U64 × Fl4Spec.Word)) (H : Heap) (Cs : Set U64) (k : U64) :
    S → A → Fl4Spec.State Unit → Prop
  | exit {s : S} {a : A} {σ : Fl4Spec.State Unit} :
      JReachU17 (L := L) arI AR MR s a σ → JAtSt (L := L) arI AR th B H Cs k s a σ → JReachSt Loc th B H Cs k s a σ
  | loc {s : S} {a : A} {σ : Fl4Spec.State Unit} {s' : S} {a' : A} {σ' : Fl4Spec.State Unit} :
      JReachSt Loc th B H Cs k s a σ → Loc s a σ s' a' σ' → JReachU17 (L := L) arI AR MR s' a' σ' →
        JReachSt Loc th B H Cs k s' a' σ'

variable {arI AR MR}

/-- Every `JReachSt` state is reachable. -/
theorem JReachSt.reach {Loc : S → A → Fl4Spec.State Unit → S → A → Fl4Spec.State Unit → Prop}
    {th : TypedHeap} {B : Set (U64 × Fl4Spec.Word)} {H : Heap} {Cs : Set U64} {k : U64} {s : S} {a : A}
    {σ : Fl4Spec.State Unit} (h : JReachSt (L := L) arI AR MR Loc th B H Cs k s a σ) :
    JReachU17 (L := L) arI AR MR s a σ := by
  cases h with
  | exit hR _ => exact hR
  | loc _ _ hR => exact hR

/-- **`JAtSt` at every `JReachSt` state** under `LocRunMv` [J]. -/
theorem JReachSt.atSt {Loc : S → A → Fl4Spec.State Unit → S → A → Fl4Spec.State Unit → Prop}
    (hK : LocRunMv (L := L) arI AR Loc)
    {th : TypedHeap} {B : Set (U64 × Fl4Spec.Word)} {H : Heap} {Cs : Set U64} {k : U64} {s : S} {a : A}
    {σ : Fl4Spec.State Unit} (h : JReachSt (L := L) arI AR MR Loc th B H Cs k s a σ) :
    JAtSt (L := L) arI AR th B H Cs k s a σ := by
  induction h with
  | exit _ hS => exact hS
  | loc _ hL _ ih =>
    obtain ⟨Z, Ac, Lst, D, hth, hB, hk, J, hvx⟩ := ih
    obtain ⟨hk', G, V, Ac', Lst', D', J'⟩ := hK _ _ _ _ _ _ _ _ _ _ _ _ J hL
    exact ⟨Z.mv G V, Ac', Lst', D', hth, hB, hk'.trans hk, J', ⟨hvx.eq⟩⟩

/-- **The exit's ghosts start a `JReachSt` and give `Fl4Step.ser`** (module docstring): at
every reachable state, one choice of ghosts and core count `n` gives SerExit's
`ser_of_JAtZN` conclusion for `layoutJ Z H (L.ksb s) n` and `JReachSt` at the same ghosts. -/
theorem jreachSt_exit (Loc : S → A → Fl4Spec.State Unit → S → A → Fl4Spec.State Unit → Prop)
    (hnd : Fl4Spec.numDomains = 1) {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (h : JReachU17 (L := L) arI AR MR s a σ) :
    ∃ (Z : XSets) (H : Heap) (Cs : Set U64) (n : Nat), (∀ c : U64, c ∈ Cs ↔ c.val < n) ∧
      OwnMap.RegionOK (layoutJ Z H (L.ksb s) n) ∧ E2E.UserOK (layoutJ Z H (L.ksb s) n) ∧
      (∀ c : Serial.Cfg U64 U64 U64 U64, SerExit.ExitGhost (L := L) (layoutJ Z H (L.ksb s) n) s c →
        E2E.Maps (layoutJ Z H (L.ksb s) n) c) ∧
      JReachSt (L := L) arI AR MR Loc Z.th Z.B H Cs (L.ksb s) s a σ := by
  obtain ⟨Z, H, Cs, Ac, Lst, D, J, -, -, -, -, -, -, -, hvx⟩ := jreach_invU3 hnd h.1
  obtain ⟨n, hn, h1, h2, h3⟩ := SerExit.ser_of_JAtZN J
  exact ⟨Z, H, Cs, n, hn, h1, h2, h3, .exit h ⟨Z, Ac, Lst, D, rfl, rfl, rfl, J, hvx⟩⟩

/-- **`SlJAt` at every `JReachSt` state for every layout matching the fixed ghosts**
(`numDomains = 1` and `LocRunMv` [J] only). -/
theorem slJAt_of_jreachSt {Loc : S → A → Fl4Spec.State Unit → S → A → Fl4Spec.State Unit → Prop}
    (hnd : Fl4Spec.numDomains = 1) (hK : LocRunMv (L := L) arI AR Loc)
    {th : TypedHeap} {B : Set (U64 × Fl4Spec.Word)} {H : Heap} {Cs : Set U64} {k : U64} {s : S} {a : A}
    {σ : Fl4Spec.State Unit} (h : JReachSt (L := L) arI AR MR Loc th B H Cs k s a σ)
    (K : KLayout) (hH : K.heap = H) (hS : K.slots = {x | IsSlot th x})
    (hU : K.user = {b | ∃ wp ∈ B, wp.1 = b}) (hk : K.ksb = k) (hn : ∀ c : U64, c ∈ Cs ↔ c.val < K.ncores) :
    SlJAt (L := L) K s := by
  obtain ⟨Z, Ac, Lst, D, hth, hB, hk', J, -⟩ := h.atSt hK
  obtain ⟨-, -, -, -, -, -, -, hX, -⟩ := jreach_invU3 hnd h.reach.1
  subst hth hB
  exact slJAt_of_JAtZ_stable J hX.cr.2 K hH hS hU (hk.trans hk'.symm) hn

/-- **`SlJAt` for the exit's layout** `layoutJ Z H k n` at every `JReachSt` state at `Z.th`,
`Z.B`, `H`, `Cs`, `k`. -/
theorem slJAt_layoutJ_of_jreachSt {Loc : S → A → Fl4Spec.State Unit → S → A → Fl4Spec.State Unit → Prop}
    (hnd : Fl4Spec.numDomains = 1) (hK : LocRunMv (L := L) arI AR Loc)
    {Z : XSets} {H : Heap} {Cs : Set U64} {k : U64} {n : Nat} (hn : ∀ c : U64, c ∈ Cs ↔ c.val < n)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (h : JReachSt (L := L) arI AR MR Loc Z.th Z.B H Cs k s a σ) :
    SlJAt (L := L) (layoutJ Z H k n) s :=
  slJAt_of_jreachSt hnd hK h _ rfl rfl rfl rfl hn

set_option maxHeartbeats 8000000 in
/-- **Accepted syscall local runs keep `JReachSt`, under U29's tops** (module docstring): the
`JReachU17` side is `kernel_entry_reachU29S`'s (its two clauses, inputs verbatim, at the
ghosts it picks); the `Loc` step is the run itself (`LocSys`, inside `Loc`). -/
theorem jreachSt_sysLoc [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR) (hIo : MRKeepIo arI MR) (hIoa : MRKeepIoapic arI MR)
    (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hPI : PortInValMR arI MR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    {Loc : S → A → Fl4Spec.State Unit → S → A → Fl4Spec.State Unit → Prop}
    (hsub : ∀ s a σ s' a' σ', LocSys (st := st) arI s a σ s' a' σ' → Loc s a σ s' a' σ')
    {th : TypedHeap} {B : Set (U64 × Fl4Spec.Word)} {H0 : Heap} {Cs0 : Set U64} {k : U64}
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hJ : JReachSt (L := L) arI AR MR Loc th B H0 Cs0 k s a σ) :
    ∃ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ ∧
      (∀ (n : I64) (c : Fl4Spec.Syscall) (found : U64 × U64), σ.curThread ≠ σ.idleThread → NativeSys n c →
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
        (∀ t f, sched.cur_thread st s = ok t → obj.Tcb.flags st t s = ok f →
          (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 → n = fl4_abi.syscall.SysReplyRecv →
          fastpath.reply_caps st s t = ok (some found)) →
        ∀ s' a', syscall.handle_syscall_local st arI s a n found = ok (true, s', a') →
          ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧
            JReachSt (L := L) arI AR MR Loc th B H0 Cs0 k s' a' σ') ∧
      (∀ (n : I64) (found : U64 × U64), σ.curThread ≠ σ.idleThread → UnkSys (L := L) n s →
        NoDbgSys (L := L) arI n s a →
        (∀ ev, KEvSpec (.sysU n) true ev → ∀ w ∈ (Fl4Spec.fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
          KFinEv13 (L := L) arI AR ev (KFrontSysU (st := st) arI n s a) w.2) →
        ∀ s' a', syscall.handle_syscall_local st arI s a n found = ok (true, s', a') →
          ∃ ev σ', KEvSpec (.sysU n) true ev ∧ EvOut true ev σ σ' ∧
            JReachSt (L := L) arI AR MR Loc th B H0 Cs0 k s' a' σ') := by
  obtain ⟨Z, H, Cs, Ac, Lst, D, J, hSys, hSU⟩ :=
    kernel_entry_reachU29S arI AR MR hARI hA hnd hM hKD hIo hIoa hPA hIA hT hmax htu hRef hPI hSX hDR hJ.reach
  refine ⟨Z, H, Cs, Ac, Lst, D, J, fun n c found hct hn hfl hK hDL hFin hfd s' a' hrun => ?_,
    fun n found hct hU hND hFin s' a' hrun => ?_⟩
  · have hT' := hSys n c found hct hn hfl hK hDL hFin hfd
    rw [hrun, WP.spec_ok] at hT'
    obtain ⟨σ', hσ', -, -, -, -, -, -, -, hR'⟩ := hT' rfl
    exact ⟨σ', hσ', .loc hJ (hsub _ _ _ _ _ _ ⟨n, found, hrun, Or.inl ⟨c, hn, hσ'⟩⟩) hR'⟩
  · have hT' := hSU n found hct hU hND hFin
    rw [hrun, WP.spec_ok] at hT'
    obtain ⟨ev, σ', hev, hO, -, -, -, -, -, -, hR'⟩ := hT' rfl
    exact ⟨ev, σ', hev, hO, .loc hJ (hsub _ _ _ _ _ _ ⟨n, found, hrun, Or.inr ⟨ev, hev, hO⟩⟩) hR'⟩

end

/-! ## `StartAt` for the syscall local path at the exit's layout -/

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {Locks : S → U64 → Prop}
variable {A : Type}
variable {n : I64} {found : U64 × U64} {Cs Ω Sg Ac : Set U64}

/-- **`StartAt` for `sl_pathsK` at the exit's layout** (module docstring): at a body start
state `σ` that is a `JReachSt` state at the last serial exit's ghosts (`jreachSt_exit`), the
execution's layout `layoutJ Z H k nc` (what that exit's `ser` installed and `Fl4Step.keep`
kept) meets `StartAt`, given `Q` and the glue's core / locks / memory link at `σ`. Layout
premises: `numDomains = 1` and `LocRunMv` [J] only. -/
theorem sl_pathsK_startAt_stab {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop}
    {MR : A3 → Fl4Spec.MachineState → Prop}
    {Loc : S → A3 → Fl4Spec.State Unit → S → A3 → Fl4Spec.State Unit → Prop}
    (hnd : Fl4Spec.numDomains = 1) (hKL : LocRunMv (L := L) arI AR Loc)
    (ar : machine.Arch A) (hSt : P0.StoreTotal st) (hA : P0.ArchTotal ar)
    (hm : Fl4Proofs.P2.E2E.MasksWr st) (a0 : A) (Q : KLayout → (U64 → U64) → S → Prop)
    (hPE : ∀ K m s, SlJAt (L := L) K s → Q K m s →
      SlPreB (st := st) ar K Locks m n found K.heap.tcbs Cs Ω K.user Sg K.heap.replies
        K.heap.scs K.heap.ntfns Ac K.heap K.heap.scBits s)
    (hEr : ∀ K m s, SlJAt (L := L) K s → Q K m s → SlEntR (st := st) K Locks found s)
    (hHr : ∀ K m s, SlJAt (L := L) K s → Q K m s → SlHereR (st := st) K found s)
    (hAr : ∀ K m s, SlJAt (L := L) K s → Q K m s → SlAccR (st := st) ar K Locks found s)
    (huf : ∀ K m s b v, SlJAt (L := L) K s → Q K m s → b ∈ K.user → Aligned b →
      (SlJAt (L := L) K (L.wr s b v) ∧ Q K m (L.wr s b v)) ∧ Locks (L.wr s b v) = Locks s ∧
        SlRS (st := st) K Locks (L.wr s b v) = SlRS (st := st) K Locks s ∧
        SlWS (st := st) K Locks (L.wr s b v) = SlWS (st := st) K Locks s ∧
        SlDS (L := L) (L.wr s b v) = SlDS (L := L) s)
    (hpz : ∀ K m, ∃ p : SProg Bool, IsProg (slBody S n found) p ∧ NoZero p ∧
      Fl4Proofs.P2.E2E.ReadOnce st ar p (OwnMap.cls K) (OwnMap.ko K m) (· ∈ K.user)
        (fun s => SlJAt (L := L) K s ∧ Q K m s) (SlRS (st := st) K Locks))
    {Z : XSets} {H : Heap} {Cx : Set U64} {k : U64} {nc : Nat} (hn : ∀ c : U64, c ∈ Cx ↔ c.val < nc)
    (m : U64 → U64) (hK : RegionOK (layoutJ Z H k nc)) (hU : Fl4Proofs.P2.E2E.UserOK (layoutJ Z H k nc))
    {σ : S} {a3 : A3} {τ : Fl4Spec.State Unit}
    (hR : JReachSt (L := L) arI AR MR Loc Z.th Z.B H Cx k σ a3 τ)
    (a : A) (hQ : Q (layoutJ Z H k nc) m σ) {c : U64} {hs : U64 → Prop}
    (hc : L.cpu σ = c) (hl : Locks σ = hs) {μ : U64 → U64}
    (hμ : ∀ x, Aligned x → x ∉ (layoutJ Z H k nc).user → L.mem σ x = μ x) :
    Fl4Proofs.P2.E2E.StartAt
      (sl_pathsK (Locks := Locks) ar hSt hA hm a0 Q hPE hEr hHr hAr huf hpz () (layoutJ Z H k nc) m hK hU) c hs μ
      ((sl_pathsK (Locks := Locks) ar hSt hA hm a0 Q hPE hEr hHr hAr huf hpz () (layoutJ Z H k nc) m hK hU).body
        σ a) :=
  sl_pathsK_startAt ar hSt hA hm a0 Q hPE hEr hHr hAr huf hpz (layoutJ Z H k nc) m hK hU a
    (slJAt_layoutJ_of_jreachSt hnd hKL hn hR) hQ hc hl hμ

end

end Fl4Proofs.P2.PathObl
