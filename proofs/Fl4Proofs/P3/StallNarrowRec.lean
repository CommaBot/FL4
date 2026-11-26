/-
P3 (p3P gen 2, finding (c) fix): **the entry records with `stall` narrowed to `Z.T`.**

`JEntryAt`, `JEntryAtR`, `JEntryAtR2`, `JEntryAtR3`, `JEntryAtR5`, `SInvR.G5.JEntryAtR6`,
`SInvR.G5.JEntryAtR7` copied verbatim as `…N` except the field
`stall : ∀ q, remote_tcb_stall st arI s ar q = ok (s, ar)` (false at reachable states,
`StallFinding`), which becomes `stall : ∀ q ∈ Z.T, …` (the TCBs of the joint sets; true at every
`JAtZ` state, `JAtZ.stallT`). Field order and every other field unchanged, so StallNarrowGen
can transport `kernel_entry_reachU30`'s proof term onto these records.
* `decode_invocation_threadJ_stepMMN`, `decode_invocation_threadJ_stepMN`: the statements of
  `decode_invocation_threadJ_stepMM` / `…stepM` with `hstall'` narrowed (proved by the `…T`
  versions, which need no stall).
-/
import Fl4Proofs.P3.StallNarrowTcb
import Fl4Proofs.P3.XTopJointKEntryU30
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **Narrowed copy of `JEntryAt`** (p3P gen 2): `stall` only at the TCBs of `Z.T`.
 **The premises at the entry state**, each exactly as a J decode takes it (the
kernel-global placement facts `hcw`, `hact2`, `hact3`, `hksO`, `hactK` and
`DomPlaced` are proved from `JAtZ`: JEntryKs). -/
structure JEntryAtN (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs : Set U64)
    (s : S) (ar : A) (σ : Fl4Spec.State Unit) : Prop where
  /-- [J] no reschedule or switch pending at the invocation (`Entered`). -/
  ni : Entered σ
  /-- [J] the current thread in no ready queue at the invocation (l4v
  `ct_not_in_q`, part of `valid_sched`, under `scheduler_action =
  resume_cur_thread`, `ni`; FL4's `switch_to_thread` dequeues the thread it
  switches to): the Endpoint cap's blocking send blocks it (`sendLeafJ`,
  `JAtZ.sendBlockJ`: P1's `CanBlock.nq` and the spec's `NotQueued`). -/
  ctnq : ∀ d q, σ.curThread ∉ σ.readyQueues d q
  /-- [J] the spec's global references at the invocation (SpecGlob: the IRQ
  node's slots null or notification caps, no cap but a frame cap naming an
  IRQ node CNode or the idle thread; l4v `valid_irq_node`,
  `valid_global_refs`), carried by the deletion loop. -/
  sg : SpecGlob σ
  /-- [J] `hRd0`: at a zero consumed time the current SC's head ready (l4v
  `cur_sc_offset_ready 0`; ScEntryRd's `OffReady.rd0` from `OffReady` at
  the invocation, which `budget_ok_offReady` gives from `OffReady` at
  kernel entry). -/
  rd0 : σ.consumedTime = 0 → ∀ y n, σ.kheap σ.curSc = some (.schedContext y n) → Fl4Spec.scActive y = true →
    Fl4Spec.refillReady σ.curTime (Fl4Spec.refillHd y) = true
  /-- [P] the Thread decode's `hstall'` (the remote stall a no-op, one core). -/
  stall : ∀ q ∈ Z.T, smp.remote_tcb_stall st arI s ar q = ok (s, ar)
  /-- [J] the Thread decode's `hFl` (SetFlags): FL4's flags word of every TCB
  of `T` against the spec's `tcb_flags` at the invocation (l4v `tcb_relation`'s
  `tcbFlags`; framed across the caller's restart by `JAtZ.flagsRestart`). -/
  flags : FlagsRel Z.T (L.mem s) σ
  /-- [J] the CNode decode's `hQ` (the endpoint queues' precondition). -/
  epQ : ∀ e, Sched.EpQPre σ e
  /-- [J] the IRQ control decode's `hHA`. -/
  handlers : HandlersActive (L.mem s) (L.ksb s) Z.G
  /-- [J] the IO port control decode's `hPA`. -/
  ports : IoPortsAlloc (L.mem s) (L.ksb s) Z.G
  /-- [P] the IRQ control decode's `hnum`, `hnA` (the IOAPIC count). -/
  ioapics : ∃ nA, arI.num_ioapics ar = ok nA ∧ nA.bv = σ.archState.x64NumIoapics
  /-- [P] the IRQ control decode's `hAR`. -/
  archIrq : ArchIrqRel arI ar σ
  /-- [J] the current thread's fault handler is null or an endpoint cap with
  send and grant or grant-reply rights (l4v `valid_objs`' `valid_tcb`, the
  `tcb_cap_cases` entry of `tcb_fault_handler`: `valid_fault_handler`; FL4's
  TCB SetSpace/Configure/SetSchedParams check `valid_fault_handler`
  before installing, a retyped TCB's slots are null, deletion nulls); for a
  fault (`JAtZ.faultHypJZ`: any other cap is a spec `fail`). -/
  vfh : ∀ x, σ.kheap σ.curThread = some (.tcb x) → Fl4Spec.validFaultHandler x.tcbFaultHandler
  /-- [J] the current thread has no fault at the invocation (l4v MCS
  `fault_tcbs_valid_states`: a thread with a fault is not active; the spec
  sets a fault only in `send_fault_ipc`, whose sender then blocks on the
  endpoint or on a reply or goes `Inactive`, and `cancel_ipc` (restart,
  suspend) and the fault reply clear it, `restart_thread_if_no_fault` leaves
  a faulted thread `Inactive`): the Endpoint cap's send is a normal transfer
  (`sendLeafJ2`'s `hnf`). -/
  cnf : ∀ x, σ.kheap σ.curThread = some (.tcb x) → x.tcbFault = none
  /-- [J] a mapped page-table, page-directory or PDPT cap whose table is in
  no set of `Z` (a detype pruned it while the cap still says mapped,
  handoff/vsreach.md): the spec's table of that kind at its address (l4v
  `valid_cap`'s `typ_at` for the cap's table; `valid_objs`) and the table's
  frame 4 KiB-aligned and apart from the sets' objects and the typed heap
  (l4v `pspace_aligned`, `pspace_distinct`: the frame is one spec object, an
  arch object, so no TCB, CNode, endpoint, notification, reply, SC or
  kernel-global word, and no table or pool of the sets); XTopJointVsOff's
  `OffTabOK`, what the Unmap of such a cap reads (`decode_invocation_page_tableJO`). -/
  vsTyp : ∀ y, IsSlot Z.th y → OffTabOK (L := L) Z s σ (capV (L.mem s) y)
  /-- [J] the liveness of FL4's caps at the invocation, at the entry's `JAtZ`
  ghost (XTopJointWJLRestart's `LiveDN`): `LiveJ` (l4v `if_unsafe_then_cap`
  and `if_live_then_nonz_cap` for the debug lists' TCBs; `zombies_final` and
  `cap_removeable` for a zombie's unused slots, a TCB zombie's TCB not
  `live`), `DbgWF` (the debug lists well formed: FL4's TCB debug list, as
  l4v's `valid_objs`/`valid_idle`-style list invariants) and `NullOrig` (a
  null slot carries no original bit: l4v `valid_nullcaps` of `valid_mdb'`).
  The deletion at `WJL` (CNode Revoke/Delete, the IRQ handler's
  SetIRQHandler/ClearIRQHandler, the Thread cap's SetTimeoutEndpoint,
  SetSpace, SetIPCBuffer, Configure and SetSchedParams installs) carries it
  from here across the caller's restart (`WJL.restart`) and the installs'
  inserts (XTopJointWJLIns' `LiveDN.insT`). -/
  live : LiveDN (L := L) Z.th H Cs Z.G s σ
  /-- [J] no non-device frame cap names the null pointer (`FrNZ`; l4v
  `pspace_in_kernel_window` / `cap_refs_in_kernel_window`: a non-device frame
  is RAM, in the kernel window; FL4's `UtW` puts RAM untypeds at or above
  `PPTR_BASE` and a non-device frame is retyped from one): SetIPCBuffer /
  Configure's frame install (`JAtZ.bokInstall`, the spec's `IpcBufCapOK`
  asks the IPC frame's pointer nonzero). -/
  fnz : FrNZ Z.th (L.mem s)
  /-- [J] the free part of every RAM untyped cap reads zero in the spec's
  memory (`UtZero`; l4v `untyped_ranges_zero`: true in reachable states, the
  spec's memory is written only by the IPC-buffer and frame stores (inside
  objects, so off every free part, `freeOut_of_obj`), `freeMemory` and
  `clearMemory`, both zeroing): the frame retype's new pages read zero
  (XTopJointUtEp's `UtFreeZ`, `B` grown at them, UtFrameAdd). The untyped decode runs at the
  entry state; the restart keeps the spec's memory. -/
  urz : UtZero (L.mem s) Z.G σ
  /-- [J] every RAM untyped region misses the 64 cores' node slots
  (XTopJointUtEp's `UtNodesJ`; l4v `kernel_window`/`valid_untyped`: FL4's
  kernel-state block, all `MAX_NODES` = 64 nodes, is static kernel data,
  never untyped memory; `JCovD.ks` names only `Cs`'s nodes): the frame
  retype's new `B` words miss every node (`JAtZ.nodeB`). -/
  utks : UtNodesJ (L.mem s) Z.G (L.ksb s)

/-- **Narrowed copy of `JEntryAtR`** (p3P gen 2): `stall` only at the TCBs of `Z.T`.
 **`JEntryAt` without the fields `SInvB`, `hQ` and `OffReady` supply** (module
docstring): `ni`, `ctnq`, `sg`, `rd0`, `vfh`, `cnf` removed; every other field as
`JEntryAt`'s (same tags). -/
structure JEntryAtRN (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs : Set U64)
    (s : S) (ar : A) (σ : Fl4Spec.State Unit) : Prop where
  /-- [P] `JEntryAt.stall`. -/
  stall : ∀ q ∈ Z.T, smp.remote_tcb_stall st arI s ar q = ok (s, ar)
  /-- [J] `JEntryAt.flags`. -/
  flags : FlagsRel Z.T (L.mem s) σ
  /-- [J] `JEntryAt.epQ`. -/
  epQ : ∀ e, Sched.EpQPre σ e
  /-- [J] `JEntryAt.handlers`. -/
  handlers : HandlersActive (L.mem s) (L.ksb s) Z.G
  /-- [J] `JEntryAt.ports`. -/
  ports : IoPortsAlloc (L.mem s) (L.ksb s) Z.G
  /-- [P] `JEntryAt.ioapics`. -/
  ioapics : ∃ nA, arI.num_ioapics ar = ok nA ∧ nA.bv = σ.archState.x64NumIoapics
  /-- [P] `JEntryAt.archIrq`. -/
  archIrq : ArchIrqRel arI ar σ
  /-- [J] `JEntryAt.vsTyp`. -/
  vsTyp : ∀ y, IsSlot Z.th y → OffTabOK (L := L) Z s σ (capV (L.mem s) y)
  /-- [J] `JEntryAt.live`. -/
  live : LiveDN (L := L) Z.th H Cs Z.G s σ
  /-- [J] `JEntryAt.fnz`. -/
  fnz : FrNZ Z.th (L.mem s)
  /-- [J] `JEntryAt.urz`. -/
  urz : UtZero (L.mem s) Z.G σ
  /-- [J] `JEntryAt.utks`. -/
  utks : UtNodesJ (L.mem s) Z.G (L.ksb s)

/-- **Narrowed copy of `JEntryAtR2`** (p3P gen 2): `stall` only at the TCBs of `Z.T`.
 **`JEntryAtR` without `epQ`** (module docstring); every other field as
`JEntryAt`'s (same tags). -/
structure JEntryAtR2N (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs : Set U64)
    (s : S) (ar : A) (σ : Fl4Spec.State Unit) : Prop where
  /-- [P] `JEntryAt.stall`. -/
  stall : ∀ q ∈ Z.T, smp.remote_tcb_stall st arI s ar q = ok (s, ar)
  /-- [J] `JEntryAt.flags`. -/
  flags : FlagsRel Z.T (L.mem s) σ
  /-- [J] `JEntryAt.handlers`. -/
  handlers : HandlersActive (L.mem s) (L.ksb s) Z.G
  /-- [J] `JEntryAt.ports`. -/
  ports : IoPortsAlloc (L.mem s) (L.ksb s) Z.G
  /-- [P] `JEntryAt.ioapics`. -/
  ioapics : ∃ nA, arI.num_ioapics ar = ok nA ∧ nA.bv = σ.archState.x64NumIoapics
  /-- [P] `JEntryAt.archIrq`. -/
  archIrq : ArchIrqRel arI ar σ
  /-- [J] `JEntryAt.vsTyp`. -/
  vsTyp : ∀ y, IsSlot Z.th y → OffTabOK (L := L) Z s σ (capV (L.mem s) y)
  /-- [J] `JEntryAt.live`. -/
  live : LiveDN (L := L) Z.th H Cs Z.G s σ
  /-- [J] `JEntryAt.fnz`. -/
  fnz : FrNZ Z.th (L.mem s)
  /-- [J] `JEntryAt.urz`. -/
  urz : UtZero (L.mem s) Z.G σ
  /-- [J] `JEntryAt.utks`. -/
  utks : UtNodesJ (L.mem s) Z.G (L.ksb s)

/-- **Narrowed copy of `JEntryAtR3`** (p3P gen 2): `stall` only at the TCBs of `Z.T`.
 **`JEntryAtR2` without `live`** (module docstring); every other field as
`JEntryAt`'s (same tags). -/
structure JEntryAtR3N (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (s : S) (ar : A) (σ : Fl4Spec.State Unit) :
    Prop where
  /-- [P] `JEntryAt.stall`. -/
  stall : ∀ q ∈ Z.T, smp.remote_tcb_stall st arI s ar q = ok (s, ar)
  /-- [J] `JEntryAt.flags`. -/
  flags : FlagsRel Z.T (L.mem s) σ
  /-- [J] `JEntryAt.handlers`. -/
  handlers : HandlersActive (L.mem s) (L.ksb s) Z.G
  /-- [J] `JEntryAt.ports`. -/
  ports : IoPortsAlloc (L.mem s) (L.ksb s) Z.G
  /-- [P] `JEntryAt.ioapics`. -/
  ioapics : ∃ nA, arI.num_ioapics ar = ok nA ∧ nA.bv = σ.archState.x64NumIoapics
  /-- [P] `JEntryAt.archIrq`. -/
  archIrq : ArchIrqRel arI ar σ
  /-- [J] `JEntryAt.vsTyp`. -/
  vsTyp : ∀ y, IsSlot Z.th y → OffTabOK (L := L) Z s σ (capV (L.mem s) y)
  /-- [J] `JEntryAt.fnz`. -/
  fnz : FrNZ Z.th (L.mem s)
  /-- [J] `JEntryAt.urz`. -/
  urz : UtZero (L.mem s) Z.G σ
  /-- [J] `JEntryAt.utks`. -/
  utks : UtNodesJ (L.mem s) Z.G (L.ksb s)

/-- **Narrowed copy of `JEntryAtR5`** (p3P gen 2): `stall` only at the TCBs of `Z.T`.
 **`JEntryAtR3` without `fnz`, `utks` (theorems of `JAtZ`) and `handlers`,
`ports`, `urz` (from `SInvI`)** (module docstring). -/
structure JEntryAtR5N (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (s : S) (ar : A) (σ : Fl4Spec.State Unit) :
    Prop where
  /-- [P] `JEntryAt.stall` (one core). -/
  stall : ∀ q ∈ Z.T, smp.remote_tcb_stall st arI s ar q = ok (s, ar)
  /-- [J] joint `JEntryAt.flags` (l4v `tcb_relation`'s flags). -/
  flags : FlagsRel Z.T (L.mem s) σ
  /-- [P] `JEntryAt.ioapics`. -/
  ioapics : ∃ nA, arI.num_ioapics ar = ok nA ∧ nA.bv = σ.archState.x64NumIoapics
  /-- [P] `JEntryAt.archIrq`. -/
  archIrq : ArchIrqRel arI ar σ
  /-- [J] joint `JEntryAt.vsTyp` (l4v `valid_cap` typ_at, `pspace_distinct`). -/
  vsTyp : ∀ y, IsSlot Z.th y → OffTabOK (L := L) Z s σ (capV (L.mem s) y)

end

end

end Fl4Proofs.P3

namespace Fl4Proofs.P3.SInvR.G5
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **Narrowed copy of `JEntryAtR6`** (p3P gen 2): `stall` only at the TCBs of `Z.T`.
 **`JEntryAtR5` without `flags`** (asked at the entry state and carried to
the dispatch state, `flags_front`): the three [P] fields and `vsTyp` [J]. -/
structure JEntryAtR6N (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (s : S) (ar : A) (σ : Fl4Spec.State Unit) :
    Prop where
  /-- [P] `JEntryAt.stall` (one core). -/
  stall : ∀ q ∈ Z.T, smp.remote_tcb_stall st arI s ar q = ok (s, ar)
  /-- [P] `JEntryAt.ioapics`. -/
  ioapics : ∃ nA, arI.num_ioapics ar = ok nA ∧ nA.bv = σ.archState.x64NumIoapics
  /-- [P] `JEntryAt.archIrq`. -/
  archIrq : ArchIrqRel arI ar σ
  /-- [J] joint `JEntryAt.vsTyp` (l4v `valid_cap` typ_at, `pspace_distinct`). -/
  vsTyp : ∀ y, IsSlot Z.th y → OffTabOK (L := L) Z s σ (capV (L.mem s) y)

/-- **Narrowed copy of `JEntryAtR7`** (p3P gen 2): `stall` only at the TCBs of `Z.T`.
 **`JEntryAtR6` without `vsTyp`** (C4, from `JAtZ.carry.vsTyp`, jc3). -/
structure JEntryAtR7N (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (s : S) (ar : A) (σ : Fl4Spec.State Unit) :
    Prop where
  /-- [P] `JEntryAt.stall` (one core). -/
  stall : ∀ q ∈ Z.T, smp.remote_tcb_stall st arI s ar q = ok (s, ar)
  /-- [P] `JEntryAt.ioapics`. -/
  ioapics : ∃ nA, arI.num_ioapics ar = ok nA ∧ nA.bv = σ.archState.x64NumIoapics
  /-- [P] `JEntryAt.archIrq`. -/
  archIrq : ArchIrqRel arI ar σ

end

end

end Fl4Proofs.P3.SInvR.G5

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {MR : A → Fl4Spec.MachineState → Prop}


/-- **`decode_invocation_threadJ_stepMM` with `hstall' : ∀ q ∈ Z.T, …`** (unused: the stalls
follow from `J`, `decode_invocation_threadJ_stepMMT`). -/
theorem decode_invocation_threadJ_stepMMN [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) [VxE Z] (hni : Entered σ)
    (hARI : ARIface arI AR) (hT : P0.ArchTotal arI)
    (hFl : FlagsRel Z.T (L.mem s) σ) (hfnz : FrNZ Z.th (L.mem s))
    (lbl length : U64) (p : U64)
    (blk call don fp : Bool) (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize) (ct : U64)
    (hct : sched.cur_thread st s = ok ct)
    (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = tcbLabelOf lbl)
    (argsU : List U64) (hlen : length.val = argsU.length)
    (hargs : ∀ (i : U64) x, argsU[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr) (hAs : AbsSlot Z.th sl)
    (hsc : capV (L.mem s) (cslotAddr sl) = .Thread p)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef)
    (hext : Fl4Spec.genInvocationType slbl = .invalidInvocation → Fl4Spec.fl4TcbExtLabelOf slbl = tcbExtOf lbl)
    (hstall' : ∀ q ∈ Z.T, smp.remote_tcb_stall st arI s ar q = ok (s, ar))
    (hNative : lbl ≠ fl4_abi.label.TCBSetEPTRoot)
    (hcw : OutsideObjects Z.th (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD))
    (hpI : p ≠ L.idleW s)
    (x0 x1 x2 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (hx1 : Aeneas.Std.Array.index_usize extra 1#usize = ok x1)
    (hx2 : Aeneas.Std.Array.index_usize extra 2#usize = ok x2)
    (hXc : XcRel Z.th (L.mem s) x0 x1 x2 excaps) (hnc : NcHyp (st := st) Z.th s σ x0 x1 x2)
    (hnc0 : ∀ sl : Fl4Spec.CslotPtr, AbsSlot Z.th sl → x0 = cslotAddr sl → isUt (capV (L.mem s) x0) = true →
      NoChildrenRel (st := st) s σ x0 sl)
    (hcapC : x1 ≠ 0#u64 → ∀ q b, capV (L.mem s) x1 = .SchedContext q b → q ∈ Z.C)
    (hA5 : ArgRel (st := st) s σ ct buf buffer 5) (hGb : GetBpHyp (st := st) s ct p)
    (hFJ : lbl = fl4_abi.label.TCBReadFPU → FpuFrameJHyp (L := L) Z s σ x0)
    (hmb : ∀ a, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hidS : ∀ (sl' : Fl4Spec.CslotPtr) q, AbsSlot Z.th sl' → capV (L.mem s) (cslotAddr sl') = .Thread q →
      q ≠ L.idleW s)
    (hbuf : msg.lookup_ipc_buffer st s false ct = ok buf) (hl : argsU.length ≤ 120)
    (hJDP : JDelParts (L := L) arI AR Z.th) (hsg : SpecGlob σ) (hLv : LiveDN (L := L) Z.th H Cs Z.G s σ)
    (hnd : Fl4Spec.numDomains = 1) (hMP : MachPlat arI MR) (hKD : MRKeepD arI MR)
    (hPA : PPPlatA arI AR) (hmv : MRV MR ar σ)
    (hRd0 : σ.consumedTime = 0 → ∀ y n, σ.kheap σ.curSc = some (.schedContext y n) → Fl4Spec.scActive y = true →
      Fl4Spec.refillReady σ.curTime (Fl4Spec.refillHd y) = true)
    (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    (hTA : TimeAgree arI) :
    XCapP (L := L) arI (JAtM (L := L) arI AR MR) (JAtPreMV (L := L) arI AR MR) s ar σ lbl length (cslotAddr sl) (.Thread p)
      blk call don fp buf extra slbl (argsU.map UScalar.bv) ci sl excaps buffer ct :=
  decode_invocation_threadJ_stepMMT arI s ar σ J hni hARI hT hFl hfnz lbl length p blk call don fp buf extra ct hct
    slbl hlbl argsU hlen hargs ci sl hAs hsc excaps buffer hext hNative hcw hpI x0 x1 x2 hx0 hx1 hx2 hXc hnc hnc0
    hcapC hA5 hGb hFJ hmb hidS hbuf hl hJDP hsg hLv hnd hMP hKD hPA hmv hRd0 hnq hTA


/-- **`decode_invocation_threadJ_stepM` with `hstall' : ∀ q ∈ Z.T, …`** (unused: the stalls
follow from `J`, `decode_invocation_threadJ_stepMT`). -/
theorem decode_invocation_threadJ_stepMN [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) [VxE Z] (hni : Entered σ)
    (hARI : ARIface arI AR) (hT : P0.ArchTotal arI)
    (hFl : FlagsRel Z.T (L.mem s) σ) (hfnz : FrNZ Z.th (L.mem s))
    (lbl length : U64) (p : U64)
    (blk call don fp : Bool) (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize) (ct : U64)
    (hct : sched.cur_thread st s = ok ct)
    (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = tcbLabelOf lbl)
    (argsU : List U64) (hlen : length.val = argsU.length)
    (hargs : ∀ (i : U64) x, argsU[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr) (hAs : AbsSlot Z.th sl)
    (hsc : capV (L.mem s) (cslotAddr sl) = .Thread p)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef)
    (hext : Fl4Spec.genInvocationType slbl = .invalidInvocation → Fl4Spec.fl4TcbExtLabelOf slbl = tcbExtOf lbl)
    (hstall' : ∀ q ∈ Z.T, smp.remote_tcb_stall st arI s ar q = ok (s, ar))
    (hNative : lbl ≠ fl4_abi.label.TCBSetEPTRoot)
    (hcw : OutsideObjects Z.th (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD))
    (hpI : p ≠ L.idleW s)
    (x0 x1 x2 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (hx1 : Aeneas.Std.Array.index_usize extra 1#usize = ok x1)
    (hx2 : Aeneas.Std.Array.index_usize extra 2#usize = ok x2)
    (hXc : XcRel Z.th (L.mem s) x0 x1 x2 excaps) (hnc : NcHyp (st := st) Z.th s σ x0 x1 x2)
    (hnc0 : ∀ sl : Fl4Spec.CslotPtr, AbsSlot Z.th sl → x0 = cslotAddr sl → isUt (capV (L.mem s) x0) = true →
      NoChildrenRel (st := st) s σ x0 sl)
    (hcapC : x1 ≠ 0#u64 → ∀ q b, capV (L.mem s) x1 = .SchedContext q b → q ∈ Z.C)
    (hA5 : ArgRel (st := st) s σ ct buf buffer 5) (hGb : GetBpHyp (st := st) s ct p)
    (hFJ : lbl = fl4_abi.label.TCBReadFPU → FpuFrameJHyp (L := L) Z s σ x0)
    (hmb : ∀ a, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hidS : ∀ (sl' : Fl4Spec.CslotPtr) q, AbsSlot Z.th sl' → capV (L.mem s) (cslotAddr sl') = .Thread q →
      q ≠ L.idleW s)
    (hbuf : msg.lookup_ipc_buffer st s false ct = ok buf) (hl : argsU.length ≤ 120)
    (hJDP : JDelParts (L := L) arI AR Z.th) (hsg : SpecGlob σ) (hLv : LiveDN (L := L) Z.th H Cs Z.G s σ)
    (hnd : Fl4Spec.numDomains = 1) (hMP : MachPlat arI MR) (hKD : MRKeepD arI MR)
    (hPA : PPPlatA arI AR) (hmv : MRV MR ar σ)
    (hRd0 : σ.consumedTime = 0 → ∀ y n, σ.kheap σ.curSc = some (.schedContext y n) → Fl4Spec.scActive y = true →
      Fl4Spec.refillReady σ.curTime (Fl4Spec.refillHd y) = true)
    (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    (hTA : TimeAgree arI) :
    XCapP (L := L) arI (JAt (L := L) arI AR) (JAtPreMV (L := L) arI AR MR) s ar σ lbl length (cslotAddr sl) (.Thread p)
      blk call don fp buf extra slbl (argsU.map UScalar.bv) ci sl excaps buffer ct :=
  decode_invocation_threadJ_stepMT arI s ar σ J hni hARI hT hFl hfnz lbl length p blk call don fp buf extra ct hct
    slbl hlbl argsU hlen hargs ci sl hAs hsc excaps buffer hext hNative hcw hpI x0 x1 x2 hx0 hx1 hx2 hXc hnc hnc0
    hcapC hA5 hGb hFJ hmb hidS hbuf hl hJDP hsg hLv hnd hMP hKD hPA hmv hRd0 hnq hTA

end

end

end Fl4Proofs.P3
