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
| `Fl4Spec/CSpace.lean`        | CSpaceAcc_A, CSpace_A, X64/ArchCSpace_A                              |
| `Fl4Spec/Tcb.lean`           | TcbAcc_A, Tcb_A, X64/ArchTcb_A                                       |
| `Fl4Spec/Sched.lean`         | Sporadic_A, SchedContext_A, Schedule_A                               |
| `Fl4Spec/Ipc.lean`           | IpcCancel_A, Ipc_A, X64/ArchIpcCancel_A                              |
| `Fl4Spec/Retype.lean`        | Retype_A, X64/ArchRetype_A                                           |
| `Fl4Spec/VSpace.lean`        | X64/ArchVSpace_A, X64/Arch_A                                         |
| `Fl4Spec/Interrupt.lean`     | Interrupt_A, X64/ArchInterrupt_A                                     |
| `Fl4Spec/Decode.lean`        | Invocations_A, X64/ArchInvocation_A, Decode_A, X64/ArchDecode_A      |
| `Fl4Spec/Syscall.lean`       | Syscall_A                                                            |
| `Fl4Spec/Init.lean`          | KernelInit_A, X64/Init_A                                             |

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
