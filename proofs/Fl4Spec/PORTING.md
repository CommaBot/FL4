# Porting the seL4 abstract spec to Lean

`Fl4Spec` is the Lean port of seL4's Isabelle abstract specification, MCS
version (DESIGN.md §9, "The abstract spec"). Source: l4v branch `rt`,
checked out at `~/Projects/fl4-deps/l4v-rt` (commit f44de69), directories
`spec/abstract`, `spec/abstract/X64`, `spec/machine`, and the generated
executable-spec types these import (`spec/design/skel`, `spec/haskell`).

## Rules

- **Transliterate.** One Lean definition per Isabelle definition, in the
  same order, with the same structure. Do not optimise, merge or
  "improve". A reviewer must be able to compare the two side by side.
- **Cite the source.** Every definition's docstring starts with
  `l4v: <Theory>.<name>`. Every file starts with a comment naming the
  theories it ports.
- **Names.** Isabelle `snake_case` becomes Lean `camelCase` for functions
  (`set_thread_state` → `setThreadState`) and `UpperCamelCase` for types
  and constructors (`cap.EndpointCap` → `Cap.endpointCap`). Keep the
  Isabelle name recognisable.
- **Only what FL4 builds.** MCS paths only; x86_64 (X64) only. No IOMMU or
  IO page tables (`IOPageTable`, `IOSpace`, VT-d contexts), no VCPUs or
  EPT, no non-MCS definitions. Keep IO ports. Where an omission removes a
  case of a datatype, say so in a comment at the datatype.
- **FL4 differences** (per-core state, l4h extensions such as TCB timers,
  trapSyscalls, subframes) never go into ported modules. They go into
  `Fl4Spec/Ext/` later, on top of the port.
- **Monad.** `Fl4Spec.NonDet σ α` (l4v `nondet_monad`) and
  `Fl4Spec.NonDetE σ ε α` (l4v `('s, 'e + 'a) nondet_monad`), defined in
  `Fl4Spec/Monad.lean`. Add missing combinators there, each citing its
  l4v definition. `do` notation works for both.
- **Words.** `machine_word` / `word64` is `BitVec 64` (`Fl4Spec.Word`),
  `word32` is `BitVec 32`, etc. `nat` is `Nat`, `int` is `Int`. Isabelle
  `'a set` is `Set α`, `'a option` is `Option α`, partial maps
  `'a ⇀ 'b` are `α → Option β`, `'a list` is `List α`.
- **Underspecified machine operations** (l4v `MachineOps` with
  `machine_op_lift`, underlying machine state) stay underspecified: model
  them as nondeterministic or as fields of the machine state, as l4v does.
  Do not invent behaviour.
- **Records** become `structure`s; record update `s⦇f := v⦈` becomes
  `{ s with f := v }`.
- **Locales and arch overrides**: l4v's `Arch` locale and
  `arch_requalify` become plain definitions in the arch modules
  (`Fl4Spec/X64/*.lean`), imported where needed.
- **Every file must compile** with `lake env lean <file>` (after
  `lake build` of the modules it imports). No `sorry`, no `axiom`
  except for the underspecified machine (each such axiom/opaque with a
  comment saying which l4v constant it stands for).
- **Executable where deterministic.** Prefer computable definitions when
  the Isabelle one is deterministic and total; use `noncomputable` only
  when needed.

## Module map

| Lean module                  | l4v theories                                                         |
|------------------------------|----------------------------------------------------------------------|
| `Fl4Spec/Monad.lean`         | lib/Monads/nondet/Nondet_Monad                                       |
| `Fl4Spec/Machine.lean`       | Lib/Word_Lib helpers, Kernel_Config, spec/machine (X64/Platform, Time, MachineTypes, MachineMonad, X64/MachineOps), X64/Machine_A, MiscMachine_A |
| `Fl4Spec/Types.lean`         | CapRights_A, VMRights_A, ExceptionTypes_A, (Arch)InvocationLabels_H, InvocationLabels_A |
| `Fl4Spec/X64/Structs.lean`   | X64/ArchVMAttributes_A, Structs_B, X64/Arch_Structs_B, X64/Arch_Structs_A |
| `Fl4Spec/Structures.lean`    | Structures_A                                                         |
| `Fl4Spec/Deterministic.lean` | List_Lib helpers, Deterministic_A, Exceptions_A (KHeap_A imports them) |
| `Fl4Spec/KHeap.lean`         | KHeap_A, X64/ArchVSpaceAcc_A                                         |
| `Fl4Spec/CSpaceAcc.lean`     | CSpaceAcc_A, Sporadic_A                                              |
| `Fl4Spec/Invocations.lean`   | X64/ArchInvocation_A, Invocations_A                                  |
| `Fl4Spec/Retype.lean`        | X64/ArchRetype_A, X64/ArchIpcCancel_A, Retype_A                      |
| `Fl4Spec/X64/VSpace.lean`    | X64/FPU_A, X64/ArchVSpace_A, X64/ArchCSpace_A                        |
| `Fl4Spec/TcbAcc.lean`        | TcbAcc_A                                                             |
| `Fl4Spec/IpcCancel.lean`     | IpcCancel_A                                                          |
| `Fl4Spec/SchedContext.lean`  | SchedContext_A                                                       |
| `Fl4Spec/CSpace.lean`        | CSpace_A                                                             |
| `Fl4Spec/X64/Arch.lean`      | X64/Arch_A                                                           |
| `Fl4Spec/Schedule.lean`      | Schedule_A                                                           |
| `Fl4Spec/Tcb.lean`           | X64/ArchTcb_A, Tcb_A, X64/ArchFault_A                                |
| `Fl4Spec/Ipc.lean`           | Ipc_A (to do)                                                        |
| `Fl4Spec/Interrupt.lean`     | X64/ArchInterrupt_A, Interrupt_A (to do)                             |
| `Fl4Spec/Decode.lean`        | X64/ArchDecode_A, Decode_A (to do)                                   |
| `Fl4Spec/Init.lean`          | X64/Init_A, KernelInit_A (to do)                                     |
| `Fl4Spec/Syscall.lean`       | Syscall_A (to do)                                                    |

The order is the MCS import graph of l4v `rt` (taken from RISCV64, since
the X64 theories on `rt` still carry the non-MCS imports): KHeap_A →
CSpaceAcc_A → Sporadic_A → ArchInvocation_A/Invocations_A → ArchRetype_A,
ArchIpcCancel_A → Retype_A → FPU_A → ArchVSpace_A → ArchCSpace_A → TcbAcc_A
→ IpcCancel_A → SchedContext_A → CSpace_A → Arch_A → Schedule_A → ArchTcb_A
→ Tcb_A → ArchFault_A → Ipc_A → ArchInterrupt_A → Interrupt_A → ... X64
Init_A only needs Retype_A; nothing up to Tcb needs it (see Deviations).

Split a module into several files if it grows past about 1500 lines; keep
the theory order.

## Encodings

Conventions of the ported base layer that later modules rely on.

- **Namespace.** Everything is in `Fl4Spec`, flat: arch (`X64_A`, `X64_H`,
  `X64`) and generic names share it. Where a camelCase name would clash, the
  l4v name stays: `pptr_base` (Machine_A) vs `pptrBase` (Platform),
  `msg_info_register`, `msg_registers`, `cap_register`, `badge_register`,
  `frame_registers`, `gp_registers`, `exception_message`, `syscall_message`
  (Machine_A) vs the Haskell `msgInfoRegister` etc.; `Platform.Cr3`
  (Platform `cr3`) vs `Cr3` (Arch_Structs_A `cr3`); `parseTimeArgA`
  (Arch_Structs_A `parse_time_arg`) vs `parseTimeArg` (Arch_Structs_B).
  Datatype selectors that Isabelle generates (`acap_rights`, `pte_frame`,
  `ep_queue`, `the_arch_cap`, ...) are explicit functions in the type's
  namespace (`ArchCap.acapRights`, `Endpoint.epQueue`), `undefined` on the
  other constructors.
- **Decidability.** Every file has `open Classical` and `noncomputable
  section`; tests on `Set`s, `∃` and equality of caps use classical
  decidability. Isabelle `bool` functions are `Bool` when the spec computes
  with them (`runnable`, `schedulable`, `scActive`, `refillReady`,
  `isCnodeCap`, `inReleaseQueue`, `isCurDomainExpired`) and `Prop` when they
  are quantified statements (`isBlockedOnReceive`, `wellFormedCnodeN`,
  `validSchedContextSize`, `isSimpleType`, `validList2`).
- **Partiality.** Isabelle `undefined`, `the`, `THE`, `partial_inv`,
  nonexhaustive `primrec`/`case` are `Fl4Spec.undefined` (a fixed
  unspecified value, `Classical.choice`), `Fl4Spec.the`, `Fl4Spec.The`,
  `Fl4Spec.partialInv`, and an explicit `| _ => undefined` case. `hd`,
  `last` and `xs ! i` are `the xs.head?`, `the xs.getLast?`, `the xs[i]?`.
- **Maps.** Partial maps are `α → Option β`; `f(x := v)` is
  `Function.update f x v`; `dom`/`ran` are `Fl4Spec.dom`/`Fl4Spec.ran`.
  `opt_map` (`|>`), `opt_map_Some` (`||>`), `opt_pred` (`|<`) are `optMap`,
  `optMapSome`, `optPred` (Lean's `|>` is the pipe).
- **State.** `AbstractState` is l4v `abstract_state`; `State Z` extends it
  with `exst : Z` (`'z state`). `[StateExt Z]` is l4v `'z::state_ext`, with
  instances for `DetExt` (deterministic spec: `workUnitsCompletedInternal`,
  `cdtListInternal`) and `Unit`. MCS scheduler state is in `AbstractState`
  (`readyQueues : Domain → Priority → List ObjRef`, `releaseQueue`,
  `schedulerAction`, `curSc`, `curTime`, `consumedTime`, `reprogramTimer`,
  `domainList`, `domainIndex`, `domainStartIndex`, `curDomain`,
  `domainTime`); only the CDT sibling lists and the work units are in
  `DetExt`. `kheap : ObjRef → Option KernelObject`; `cdt : CslotPtr → Option
  CslotPtr`; `CslotPtr = ObjRef × List Bool`. CNode contents are
  `List Bool → Option Cap`; TCB slots are `tcbCnodeIndex n` (3-bit
  big-endian bit lists) via `tcbCnodeMap`.
- **Monads.** `SMonad Z α`, `FMonad`, `SEMonad`, `LFMonad`, `PMonad` (Exceptions_A)
  are `NonDet (State Z) α` and `NonDetE (State Z) ε α`. The reader option
  monad (`r_monad`, `lookup`) is `Lookup σ α = ReaderT σ Option α`
  (`RMonad Z α`). In `do` blocks write `x ← pure e` for l4v `x ← return e`
  and `pure ()` for a non-final `return ()`: Lean's `return` exits the whole
  block.
- **Words.** `mask`, `ucast`, `unat`, `testBit` (`!!`), `toBl`, `ofBl`,
  `wordRcat`, `wordRsplit`, `uptoEnum` (`[a .e. b]`), `uptoEnumStep`
  (`[a, b .e. c]`), `assocs`, `intUpto` (`[i..j]` on int) are in Machine.
- **Constructors and fields** are lowerCamelCase (`Cap.endpointCap`,
  `Register.rax`, `VMPageSize.x64SmallPage`, `Tcb.tcbSchedContext`,
  `AbstractState.curThread`).

- **Record updates.** Isabelle's generated `f_update` functions, passed as
  arguments to `set_tcb_obj_ref`, `set_sc_obj_ref`, `set_ntfn_obj_ref`,
  `set_reply_obj_ref` and `update_sched_context`, are explicit functions in
  Structures (`tcbSchedContextUpdate`, `scRefillsUpdate`, `ntfnScUpdate`,
  `replyScUpdate`, ...). Add more there as needed. A record update written
  inline in the spec (`s⦇reprogram_timer := True⦈`, `r⦇r_amount := x⦈`) is
  `{ s with ... }`.
- **Datatype discriminators** (`is_WaitingNtfn`) are `Bool` functions in the
  type's namespace (`Ntfn.isWaitingNtfn`); `is_ArchObjectCap` is the existing
  `isArchCap`. Datatypes holding caps (`Invocation`, `TcbInvocation`,
  `RecDelCall`, ...) derive only `Inhabited` (caps have no `DecidableEq`).
- **Prop vs Bool, continued.** Cap predicates that compare caps or
  quantify are `Prop`: `sameRegionAs`, `sameObjectAs`, `sameAobjectAs`,
  `archSameRegionAs`, `shouldBeParentOf`, `isCapRevocable`,
  `archIsCapRevocable`, `shouldBeArchParentOf`, `capRemoveable`,
  `capCyclicZombie`, `hasCancelSendRights`, `isValidVtableRoot`,
  `inUserFrame`, `isFinalCap'`, `isHighestPrio`, `isAligned`,
  `canMergeRefill`. Case functions are `Bool`: `isPhysical`,
  `archIsPhysical`, `isIrqControlDescendant`, `longRunningDelete`,
  `canFastFinalise`, `checkMappingPptr`, `isDeviceUntypedCap`. Monadic
  results the spec branches on are `Bool` (`isFinalCap`, `isRoundRobin`,
  `refillFull`, `noReplyInTs`, the `r_monad` readers); `cap_insert` turns its
  `Prop`s into `Bool` with `decide`.
- **Loops.** l4v `whileLoop (λ_ s. the (f s))` with an `r_monad` condition is
  `NonDet.whileLoop (fun _ s => the (f s) = true)`.
- **List idioms.** `[a ..< b]` is `List.range' a (b - a)`; `[a ..< Suc b]`
  is `List.range' a (b + 1 - a)`; `butlast` is `List.dropLast`; `removeAll`
  is `Fl4Spec.removeAll` (IpcCancel); `xs[i := v]` is `List.set`; the list
  comprehension `[i ← xs. P i]` is `xs.filter (decide ∘ P)`; prefix `≤` on
  lists (HOL-Library.Prefix_Order) is `<+:`; Isabelle `Max S` is
  `Fl4Spec.setMax S` (Machine); `the_index` is `theIndex`; `the_pred_option P`
  is `partialInv P true`; `ptr_add` is `ptrAdd`; `is_aligned` is
  `isAligned`.
- **Partial recursive functions.** Isabelle `function`s without a
  termination proof (`rec_del`, `cap_revoke`) are `NonDet.lfp` of a
  functional (`recDelF`, `capRevokeF`) that transliterates the equations with
  the recursive calls as a parameter. Terminating ones (`resolve_address_bits'`)
  use Lean well-founded recursion on the Isabelle measure; the `let` of the
  recursion argument replaces `← returnOk` so the measure proof can see it.
- **Nested `do` results.** Inside a nested `do` used as a value
  (`return_now ← do ...` in `sched_context_yield_to`) write `pure`, never
  `return`.
- **Match statements in `do`.** A non-final Isabelle `case ... ;` is a Lean
  `match` statement whose arms are `SMonad Z Unit` (`| none => pure ()`),
  followed by the rest of the block at the outer indentation. Put a
  multi-line argument on its own lines, indented past the function name, or
  Lean parses it as a new statement.

## Deviations

- **X64 is not MCS on l4v `rt`.** The X64 machine and arch theories on the
  `rt` branch are the non-MCS ones. Taken from RISCV64 on `rt` (the 64-bit
  architecture without hypervisor), with X64 values from the C kernel where
  they differ, each marked "rt X64 gap": `time_state` and
  `last_machine_time` in `machine_state`, `time_oracle`, `getCurrentTime`,
  `setDeadline`, `deadlineIRQ`, `ackDeadlineIRQ`, `timerIRQ` (= 125, C
  `irq_timer`), `replyRegister` (R12), `nbsendRecvDest` (R13),
  `timeoutMessage` (C `TIMEOUT_REPLY_MESSAGE`), `arch_cap_badge`,
  `reply_bits` (5), `parse_time_arg`, `words_from_time`; `ntfn_bits` is the
  MCS value 6, not X64's non-MCS 5.
- **Kernel_Config** is generated from a C build; here `numDomains` is an
  unspecified constant (`opaque kernelConfig`) constrained by exactly the
  facts of `Kernel_Config_Lemmas`; `config_HAVE_FPU` is `true` (x86-64).
- **Time.thy's `consts` + `axiomatization`** (`kernelWCET_us`,
  `ticks_per_timer_unit`, `timer_unit` and their ten axioms) are one opaque
  structure `timeConsts`, inhabited by the witness of Time.thy's consistency
  `notepad`; the axioms are theorems projected from it. No Lean `axiom`.
- **`typedecl machine_state_rest`** is an opaque nonempty type.
- **`next_not_child`** (`function (domintros)`, partial) is `THE` of its
  inductively defined graph, as Isabelle's function package defines it.
- **`upto_enum` on words** uses l4v's lemma `upto_enum_word`
  (`map of_nat [unat a ..< Suc (unat b)]`) as its definition.
- **Not ported:** lemmas, `translations`, the Haskell `FPUState` synonym
  (unused), `MiscMachine_A.ipa_size` (ARM-only config), the VT-d
  declarations left in X64 Arch_Structs_A and ArchVSpaceAcc_A (no IOMMU).
- **Module map:** Deterministic_A and Exceptions_A moved before KHeap
  (`Fl4Spec/Deterministic.lean`), since KHeap_A imports them.
- **Chunk A (CSpaceAcc_A … ArchFault_A) rt X64 gaps:**
  - X64 `Arch_A` on `rt` imports TcbAcc_A but uses `cap_insert` and
    `max_free_index_update` from CSpace_A, and `Schedule_A` uses
    SchedContext_A; the X64 import graph on `rt` is the non-MCS one and does
    not build. The MCS order of RISCV64 `rt` is used, so IpcCancel_A,
    SchedContext_A and CSpace_A are ported before Arch_A (module map).
  - `idle_sc_ptr` (RISCV64 Machine_A, `pptr_base + 0x3000`) is
    `idleScPtr = kernel_base + 0x7000` in Machine: X64 Init_A puts the 8KiB
    IRQ node at `kernel_base + 0x2000` and the global paging structures up to
    `kernel_base + 0x6000`. IpcCancel_A imports Init_A only for it, so
    X64/Init_A is not a prerequisite of IpcCancel here.
  - `timerPrecision` (RISCV64 Arch_Structs_B, Haskell `usToTicks 1`) is in
    X64/Structs; the C kernel's x86 `getTimerPrecision` is `usToTicks(1)`.
  - `make_arch_fault_msg` uses label 6 (C x86 `seL4_Fault_VMFault` with
    `CONFIG_KERNEL_MCS`, RISCV64 `rt`), not X64 `rt`'s non-MCS 5.
  - No other MCS-specific arch definition differs: RISCV64 `rt`'s
    ArchVSpace_A, ArchCSpace_A, ArchRetype_A, ArchIpcCancel_A, ArchTcb_A and
    Arch_A have the same set of definitions as X64's.
- **Kernel_Config `resetChunkBits`** is a field of `kernelConfig` (C default
  8, unspecified here; l4v states no lemmas about it).
- **`rec_del`, `cap_revoke`** (partial `function`s) are least fixed points
  (`NonDet.lfp`): equal to Isabelle's definition on its domain (where l4v's
  proofs use them); outside it Isabelle's value is unspecified and the lfp
  is the partial-correctness value (results of terminating runs, failure
  only if a terminating run fails). The monotonicity of the functionals is
  not proved.
- **`resolve_address_bits'`** drops the `'z itself` argument (it only fixes
  the state type) and binds `rest` with `let` (for the termination proof)
  instead of `← returnOk`.
- **`update_cap_data`**: Isabelle `size guard''` (the word length of a
  `data` word) is the literal 64.
- **Not ported:** lemmas (`fast_finalise_def2`, `rab_termination`,
  `sc_with_reply_def2`, `msg_align_bits`), Sporadic_A's `thm` checks, the
  CSpaceAcc_A notations (plain `parentOf`, `parentOfTrancl`,
  `parentOfRtrancl` instead). IOMMU: `PageIOMap`, `io_pt_invocation`,
  `InvokeIOPT`, and the IOSpace/IO page table cases of `arch_derive_cap`,
  `arch_finalise_cap`, `arch_same_region_as` (commented out in l4v).
