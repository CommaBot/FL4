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
| `Fl4Spec/Machine.lean`       | spec/machine (MachineTypes, Time, X64/MachineOps, X64/Platform)      |
| `Fl4Spec/Types.lean`         | ExceptionTypes_A, VMRights_A, CapRights_A, InvocationLabels_A        |
| `Fl4Spec/X64/Structs.lean`   | X64/Arch_Structs_A, X64/ArchVMAttributes_A (+ Arch_Structs_B)        |
| `Fl4Spec/Structures.lean`    | Structures_A                                                         |
| `Fl4Spec/KHeap.lean`         | KHeap_A, X64/ArchVSpaceAcc_A                                         |
| `Fl4Spec/CSpace.lean`        | CSpaceAcc_A, CSpace_A, X64/ArchCSpace_A                              |
| `Fl4Spec/Tcb.lean`           | TcbAcc_A, Tcb_A, X64/ArchTcb_A                                       |
| `Fl4Spec/Sched.lean`         | Sporadic_A, SchedContext_A, Schedule_A, Deterministic_A              |
| `Fl4Spec/Ipc.lean`           | IpcCancel_A, Ipc_A, X64/ArchIpcCancel_A                              |
| `Fl4Spec/Retype.lean`        | Retype_A, X64/ArchRetype_A                                           |
| `Fl4Spec/VSpace.lean`        | X64/ArchVSpace_A, X64/Arch_A                                         |
| `Fl4Spec/Interrupt.lean`     | Interrupt_A, X64/ArchInterrupt_A                                     |
| `Fl4Spec/Decode.lean`        | Invocations_A, X64/ArchInvocation_A, Decode_A, X64/ArchDecode_A      |
| `Fl4Spec/Syscall.lean`       | Exceptions_A, Syscall_A                                              |
| `Fl4Spec/Init.lean`          | KernelInit_A, X64/Init_A                                             |

Split a module into several files if it grows past about 1500 lines; keep
the theory order.
