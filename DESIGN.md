# FL4: a verified Rust seL4 with fine-grained SMP

*Design, draft 8 (2026-11-12). Published copy: https://claude.ai/artifact/3zN2Xrz25AFk4ysqA4qfin*

FL4 re-implements the seL4 17.0 kernel in Rust. Every seL4 program builds and runs on it unchanged from source, and FL4 adds its own APIs on top. Binary compatibility is not a goal. It makes MCS and SMP first-class, detects hardware at boot instead of asking for configuration, and replaces the big kernel lock with per-object locks. The serial kernel is proven correct in Lean through Aeneas. The concurrent kernel is checked by deterministic simulation against that proven serial kernel.

| | |
|---|---|
| Baseline | seL4 17.0.0-dev (c98d70ad) |
| First target | x86_64, tested only inside QEMU/KVM |
| API | MCS only |
| Next target | AArch64 |
| License | GPL-2.0, same as seL4 |

Assurance levels used below: **Verified** (extracted by Aeneas, proven in Lean), **Sim-tested** (checked by deterministic simulation), **Trusted** (small unsafe or hardware code, reviewed and tested).

## 1. Goals and scope

### Goals

- **A superset of the seL4 API.** Every seL4 user program is a valid FL4 program at the source level: unmodified sel4test sources build against FL4's own libsel4 and pass. FL4 is free to renumber its ABI and adds new features and APIs over time, so FL4 programs need not run on seL4.
- **Few configuration options.** Hardware features are detected at boot. The only build inputs left are the build profile and the few seL4 settings that user programs are compiled against.
- **MCS and SMP as the main configuration.** seL4 treats SMP as a big-kernel-lock add-on and has not verified MCS+SMP. FL4 designs for MCS on many cores from the start.
- **Fine-grained locking.** Independent operations on different cores run in parallel. Two threads doing IPC on separate endpoints never share a lock.
- **Machine-checked serial correctness.** The kernel logic is safe Rust that Aeneas translates to Lean 4. We prove it free of panics and overflow, prove it preserves the kernel invariants, and prove it refines an abstract spec.
- **Tested concurrent correctness.** A deterministic simulator runs the real kernel code on simulated cores and checks that every concurrent run is equivalent to some serial run of the proven kernel.
- **Portable.** x86_64 first. The architecture boundary is drawn so AArch64 is a new backend crate, not a rewrite.

### Out of scope

- The non-MCS (master) API. FL4 builds only with `KernelIsMCS` on. Decided.
- In-kernel IOMMU support. FL4 builds with `KernelIOMMU` off and has no IO page table objects. User space programs the IOMMU directly (§11). Decided.
- 32-bit architectures (ia32, aarch32) and RISC-V.
- VT-x virtualisation (`seL4_VMEnter`, VCPU objects).
- Fastpaths. seL4's IPC and exception fastpaths are a second, hand-optimized copy of the general path, with their own proofs. FL4 has only the general path, so there is one implementation to verify. A fastpath can be added later if measurements show a need, together with a proof that it matches the general path. Decided.
- Information-flow (confidentiality) proofs and binary-level translation validation. The design leaves room for both.

## 2. Compatibility contract

FL4 is compatible with seL4 at the source level, not the binary level:

- **seL4 programs build and run unchanged.** Any program written against the libsel4 17.0 MCS API compiles against FL4's libsel4 without edits and behaves as the seL4 spec allows.
- **seL4 binaries do not carry over.** FL4 generates its own libsel4 and numbers syscalls, invocation labels, object types, BootInfo records and fault types itself. Every program is rebuilt for FL4.
- **FL4 programs may not build on seL4.** They can use FL4's extensions.

### What stays the same

| Surface                                                                                                            | Rule                                                                       |
|--------------------------------------------------------------------------------------------------------------------|----------------------------------------------------------------------------|
| Functions and types: `seL4_Call`, `seL4_TCB_Configure`, `seL4_MessageInfo_t`, the bitfield accessors, …            | Same names, parameters and return types                                    |
| Constants: `seL4_TCBBits`, `seL4_IllegalOperation`, `seL4_CapInitThreadTCB`, object type names, …                  | Same names. Values may change, so programs that use the names keep working |
| Structures user code reads directly: `seL4_BootInfo`, `seL4_IPCBuffer`, `seL4_UserContext`, extra BootInfo records | Same field names and meanings                                              |
| Build interface: sel4test's CMake settings and the `CONFIG_*` macros user code tests                               | Same names (see §3)                                             |
| Behavior: check order in decoders, which error a failing call returns, fault message contents, scheduling          | Follows the seL4 C source and the ported spec (§9)               |

sel4test does not cover all of that behavior, so FL4 adds a differential fuzzer. It generates programs that use only the seL4 API, builds each one twice, against upstream libsel4 for seL4 and against FL4's libsel4 for FL4, runs both under QEMU and compares their syscall traces (§12).

### What FL4 is free to change

- **Numbering.** FL4 keeps one interface definition: seL4's interface XML, imported into the FL4 tree, with FL4's methods added where they belong in each interface. The generator numbers everything from it and emits the kernel decoders and FL4's libsel4 together, so the two always agree.
- **Object sizes.** The `seL4_*Bits` constants are FL4's own. The first change is `seL4_TCBBits` 12 (4 KiB), so a TCB holds the full AVX-512 register state (2,432 bytes with x87, SSE and AVX). The other sizes keep seL4's values for now.
- **Register conventions.** The syscall register layout could change too. FL4 keeps seL4's x86_64 convention for now, and libsel4's hand-written syscall stubs are reused.

### Extensions

- Every new API gets a new name. The meaning of an existing seL4 name never changes. New behavior on an existing object is a new method, and the seL4 method keeps its seL4 meaning.
- Extensions use the `seL4_` prefix, as the l4h ones already do, and live in the same headers. They are not build options: every FL4 libsel4 and kernel has all of them.
- If upstream seL4 later adds an API that FL4 wants, FL4 adopts it under seL4's name, as a normal part of following seL4.

## 3. Configuration

seL4 has over a hundred `Kernel*` build options, and many of them just tell the kernel what hardware it will run on. FL4 adds no options of its own. It sorts seL4's options into four groups. The only inputs that change the kernel image are the profile and the three settings in the last group, and none of them depend on the hardware.

### Detected at boot (option removed)

| seL4 option                                                                                            | FL4 detects it from                                                                                                                                                                                                                                                                              |
|--------------------------------------------------------------------------------------------------------|--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| `KernelLAPICMode`, `KernelUseLogicalIDs`                                                               | CPUID.01H:ECX\[21\] and `IA32_APIC_BASE`. x2APIC when the CPU has it, and always when firmware already turned it on. xAPIC otherwise. IPIs use physical destination mode in both                                                                                                                 |
| `KernelIRQController`, `KernelMaxNumIOAPIC`                                                            | ACPI MADT: IOAPICs when listed, legacy PIC otherwise                                                                                                                                                                                                                                             |
| `KernelPC99TSCFrequency`                                                                               | In order: CPUID 15H/16H on Intel, the hypervisor leaf 40000010H under KVM, then the PIT, which some Alder Lake systems gate off. Measured once on the boot core as the median of 5 runs, never again per core. Reported to user space in the existing `SEL4_BOOTINFO_HEADER_X86_TSC_FREQ` record |
| `KernelSupportPCID`                                                                                    | CPUID.01H:ECX\[17\], with INVPCID from CPUID.07H:EBX\[10\]                                                                                                                                                                                                                                       |
| `KernelFSGSBase`                                                                                       | CPUID.07H:EBX\[0\]. FSGSBASE instructions when present, the MSRs otherwise                                                                                                                                                                                                                       |
| `KernelFPU`, `KernelXSave`, `KernelXSaveFeatureSet`, `KernelXSaveSize`                                 | CPUID 0DH. Best save instruction available (XSAVES, XSAVEC, XSAVEOPT, XSAVE, then FXSAVE). XCR0 enables every user state component the CPU has except AMX tile data (8 KiB), which stays off. The 4 KiB TCB (§2) holds the largest remaining area, 2,432 bytes with AVX-512           |
| `KernelX86MicroArch`                                                                                   | CPUID family and model, for errata only                                                                                                                                                                                                                                                          |
| `KernelSkimWindow`, `KernelX86IBRSMode`, `KernelX86IBPBOnContextSwitch`, `KernelX86RSBOnContextSwitch` | CPUID speculation bits and `IA32_ARCH_CAPABILITIES`. Each mitigation is on exactly when the CPU needs it. For example, the skim window is used only when the CPU does not report `RDCL_NO`. An Intel CPU without `IA32_ARCH_CAPABILITIES` counts as vulnerable, so it gets the skim window too   |
| `KernelMaxNumNodes` (as a hardware count)                                                              | Enabled processors in the MADT. See the last group for the upper bound                                                                                                                                                                                                                           |
| `KernelCacheLnSz`                                                                                      | CPUID.01H:EBX for flush loops. Data layout always aligns to 64 bytes                                                                                                                                                                                                                             |
| `KernelMultiboot1Header`, `KernelMultiboot2Header`, `KernelMultibootGFX*`                              | Both headers are always present. The multiboot2 header asks, as an optional request, for a linear framebuffer with no preferred size                                                                                                                                                             |
| EFER.NXE (for `seL4_X86_ExecuteNever`)                                                                 | CPUID 80000001H:EDX\[20\]. Without execute-disable the attribute is ignored                                                                                                                                                                                                                      |
| MCS timer mode                                                                                         | Already a boot-time choice in seL4: TSC-deadline when available, calibrated LAPIC one-shot otherwise                                                                                                                                                                                             |

### Fixed at one value

These are accepted only at the value FL4 supports. The CMake shim fails the build with a clear message for any other value. Values that user programs see are generated into FL4's libsel4, so programs and kernel always agree.

- API shape: `KernelIsMCS` on, `KernelIOMMU` off, `KernelVTX` off, `KernelHugePage` on, SYSCALL as the entry method, `KernelPTLevels` 4.
- Kernel limits at seL4's defaults: `KernelNumPriorities`, `KernelRootCNodeSizeBits`, `KernelMaxNumBootinfoUntypedCaps`, `KernelRetypeFanOutLimit`, `KernelMaxNumWorkUnitsPerPreemption`, `KernelStaticMaxPeriodUs`, `KernelWcetScale`, `KernelTimeSlice`, `KernelBootThreadTimeSlice`, `KernelStackBits`.
- `KernelResetChunkBits` is 16: untyped resets clear 64 KiB, then check for preemption, as in l4h patch 0030.
- Always off: fastpaths (`KernelFastpath`, `KernelExceptionFastpath`, `KernelSignalFastpath`), `KernelDangerousCodeInjection`, `KernelX86DangerousMSR`. Fastpaths are left out because a second, hand-optimized copy of IPC is hard to verify (see §1). User programs cannot tell the difference, since the fastpath only changes speed.
- Compiler options (`KernelOptimisation` and similar) do not apply. Cargo profiles replace them.

### Set by the build profile

There are two profiles, **debug** and **release**. Debug turns on `KernelDebugBuild`, `KernelPrinting`, the hardware debug API (breakpoints and single-step, which sel4test turns on for debug builds), invocation error reporting and IRQ reporting. Release turns them all off. Benchmark support stays out until sel4bench needs it, and then becomes a third profile, not separate options.

### Read from the user-program configuration

Three settings stay, because user programs are compiled against them and sel4test runs with more than one value. FL4 reads them from the same generated configuration as libsel4:

- `KernelNumDomains` and `KernelNumDomainSchedules`. These set the range checks for `DomainSet` invocations. sel4test uses 1 domain, or 4 with `DOMAINS`.
- `KernelMaxNumNodes` as an upper bound. FL4 starts min(cores found, this value) cores, so a program sized for N cores never sees more than N. The per-core arrays use a fixed internal maximum of 64.

### Boot command line

FL4 keeps one of l4h's boot options, with the same name. It says where console output can be seen, which the build cannot know:

| Option       | Effect                                                                                                |
|--------------|-------------------------------------------------------------------------------------------------------|
| `fb_console` | Also draw the console on the multiboot2 framebuffer, for machines whose serial port cannot be reached |

SMP is not an option either. One kernel image runs on one core or many. With one core, lock operations take a predicted branch on a flag set at boot, so uniprocessor IPC does no atomic operations.

AArch64 follows the same rule: GIC version, timer frequency, physical address size and memory map come from ID registers and the device tree at boot, so one image covers every supported board.

## 4. From the l4h patch series

The l4h kernel is seL4 plus 41 patches (`l4h/kernel/patches`). FL4 includes every fix and feature in that series, except the VT-x and AMD-V work (0038 to 0043) and multikernel partitioning (0031 to 0036). New APIs become FL4 extensions under §2. Fixes become FL4's behavior from the start, each with a regression test in `fl4test` or the simulator.

### l4h user space

l4h's new methods, constants, flags and BootInfo records keep their l4h names and arguments, so l4h user space builds against FL4's libsel4 with no source changes. Their numbers come from FL4's generator, like everything else, so l4h user space is rebuilt like any other program.

### New APIs

| Patch                  | Extension                                                                                                          | FL4 notes                                                                                                                                                                                                                                                                                                                                                                                                                                                     |
|------------------------|--------------------------------------------------------------------------------------------------------------------|---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| 0003, 0006             | `seL4_TCB_SetTimer`: one-shot deadline timer per TCB that signals a badge to its bound notification                | The in-kernel timer. Armed timers sit in a per-core balanced tree ordered by deadline, held under that core's scheduler lock. Arm and disarm take O(log n). At most 32 timers fire per kernel entry, and the rest fire on an interrupt programmed for right away. The hardware is armed for the deadline itself, so a timer never fires early. The armed deadline is tracked, and the timer is not reprogrammed for a later deadline. Tree invariants join P1 |
| 0001, 0004, 0027, 0007 | `seL4_TCBFlag_trapSyscalls`: every syscall instruction of the thread goes to its fault handler as `UnknownSyscall` | For foreign syscall ABIs such as Linux processes. `int $N` on the gates open to user space is reported as \#GP with the vector. FL4 always saves and restores the user RSP on SYSCALL entry, with or without the skim window. On AArch64 the fault carries x8                                                                                                                                                                                                 |
| 0002                   | `seL4_TCB_ReadFPU`, `seL4_TCB_WriteFPU` through a frame                                                            | The image is always the standard (uncompacted) XSAVE layout, whatever save instruction was chosen at boot. Written images are sanitized: MXCSR is masked with the CPU's MXCSR_MASK, and only components enabled in XCR0 are kept. A live copy on another core is flushed first, and the state is reloaded when the target is the caller                                                                                                                       |
| 0009                   | `seL4_X86_ExecuteNever` VM attribute                                                                               | Sets XD on 4 KiB, 2 MiB and 1 GiB user mappings, so user space can enforce W^X                                                                                                                                                                                                                                                                                                                                                                                |
| 0017                   | `seL4_X86_DeferFlush` attribute and `seL4_X64_PML4_Flush`                                                          | A remap that only lowers rights can skip the TLB shootdown, and the caller flushes a batch at once. FL4 also adopts the flush rules that need no API: mapping into a not-present entry flushes nothing, and a remap that only raises rights flushes the local core only                                                                                                                                                                                       |
| 0023, 0029             | `Page_TestAndClearAccessed` for 4 KiB and 2 MiB mappings                                                           | For page reclaim in user-level OS personalities                                                                                                                                                                                                                                                                                                                                                                                                               |
| 0029                   | `Page_DeriveSubframe`: 4 KiB aliases of a RAM-backed 2 MiB frame                                                   | The aliases are CDT children of the large frame cap, so revoking it removes them. The CDT invariants in P1 cover the new parent-child shape                                                                                                                                                                                                                                                                                                                   |
| 0025                   | `IRQControl_GetIOAPICRemapped`                                                                                     | Programs an IOAPIC pin in remappable format with an interrupt-remapping handle the caller owns. This is the piece that lets a user-space IOMMU driver do interrupt remapping (§11)                                                                                                                                                                                                                                                                  |
| 0021                   | BootInfo record for the boot modules after the first                                                               | The modules are copied above the root task's image, below 4 GiB, and handed over as device untypeds so retyping does not clear them                                                                                                                                                                                                                                                                                                                           |
| 0018                   | BootInfo record for the AArch64 feature ID registers                                                               | Part of the AArch64 port                                                                                                                                                                                                                                                                                                                                                                                                                                      |

### Fixes that become FL4 behavior

| Patch      | Behavior in FL4                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                |
|------------|----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| 0000       | Remote stalls can fail. A stall IPI is handled only on the interrupt path. When the remote core is busy, the operation gives up and the syscall restarts. In FL4 that is an ordinary transaction abort and retry. The operations that need a stall are listed explicitly in `prepare`: TCB invocations, finalising a TCB or SC cap, removing a reply whose donated SC belongs to a thread on another core, `SchedContext_YieldTo`, and `SchedControl_ConfigureFlags`. l4h's GenMC harnesses for the lock and IPI code are ported to FL4's lock table and serial gate, next to the simulator's weak-memory mode |
| 0012       | A timer interrupt that finds the timer still armed belongs to a deadline that has since been replaced. FL4 acknowledges it and returns to user space without starting a transaction. The armed deadline is compared with the time first, so a due interrupt does not pay for the MSR read, which traps under a hypervisor. This prevents the livelock l4h saw with vCPUs that the host deschedules                                                                                                                                                                                                             |
| 0013       | `SchedControl_ConfigureFlags` enqueues a thread on another core only when it is schedulable. A postponed thread still gets a remote queue update, so that core reprograms its timer                                                                                                                                                                                                                                                                                                                                                                                                                            |
| 0014       | APIC countdown mode converts deadlines with both rates instead of their truncated ratio, rounds up so the count never runs out early, and re-arms delays longer than the 32-bit count                                                                                                                                                                                                                                                                                                                                                                                                                          |
| 0019       | At boot, only free pages that contain a nonzero word are cleared, which keeps the hypervisor's shared zero pages. Clean boot untypeds start with a free index of 0. Untyped resets at run time still clear everything                                                                                                                                                                                                                                                                                                                                                                                          |
| 0021       | The load-address search skips memory regions that end below the minimum address and rounds region starts up to a page. Modules whose end is below their start are ignored                                                                                                                                                                                                                                                                                                                                                                                                                                      |
| 0028       | User segments use the Linux layout: data at 0x2b, code at 0x33, and STAR\[63:48\] = 0x23, so SYSRET and IRET load the same selectors. The selector values are not part of the libsel4 API, but a program that reads %cs sees a different value than on seL4                                                                                                                                                                                                                                                                                                                                                    |
| 0030       | Untyped resets clear 64 KiB, then check for preemption (§3)                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         |
| 0037       | APs load the full GDT base in real mode                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        |
| 0008       | Every invocation starts with an empty error-message buffer, so an error reply never carries a message left by an earlier, possibly more privileged, invocation. The MCP threshold from the same patch is left out (see below)                                                                                                                                                                                                                                                                                                                                                                                  |
| 0011, 0020 | Multiboot2 framebuffer request and the framebuffer console (§3)                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     |
| 0022, 0024 | Timer-rate sources and the Meltdown check, now boot-time detection (§3)                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             |
| 0015, 0016 | AArch64 port: broadcast inner-shareable TLBI instead of IPIs, 16-bit ASIDs required (`TCR_EL1.AS`), APs that fail init stop, and MCS uses the CNTFRQ rate read at boot (§11)                                                                                                                                                                                                                                                                                                                                                                                                                           |

### Fixes found while building FL4

Behavior where FL4 differs from seL4 17.0 only by closing a race or an overflow. They were found by the simulator (§10) or the P0 proofs (§9).

| Where                  | Behavior in FL4                                                                                                                                                                                                                                       |
|------------------------|-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| `TCB_CopyRegisters`    | The source thread is stalled like the target when it runs on another core. seL4 stalls only the target, so it copies a stale register context and, with `suspendSource`, leaves the other core running a suspended thread until its next kernel entry |
| Domain time accounting | The check that the domain's time has run out saturates, so a very long interval cannot wrap the sum and underflow the remaining time                                                                                                               |

### Left out

- **Debug syscall MCP threshold** (0008, `KernelDebugSyscallMinMCP`). FL4 does not gate debug syscalls or kernel error messages by MCP. Debug syscalls exist only in the debug profile, which is not for running untrusted code.
- **VT-x and AMD-V** (0038 to 0043). Out of scope. 0038's idea, making a feature a boot-time choice instead of a build option, is what FL4 does everywhere.
- **Multikernel partitioning** (0031 to 0036). FL4 is always the only kernel on its machine. That drops the kernel load-address build option, the `ap_boot_page=`, `no_legacy_irq`, `peers=`, `console_ring=`, `tsc_mhz=` and `apic_khz=` boot options, and `IRQControl_SendPeer`. FL4 loads at the fixed seL4 address, owns the IOAPICs and PIC, and always measures its own timer rates.

## 5. Architecture

The kernel is a stack of layers. Each one has a single assurance level, so the trusted code stays small and easy to find.

| Layer | Crate | Assurance | Contents |
|---|---|---|---|
| User space | sel4test, rootserver | | Unmodified sources, built against FL4's libsel4 |
| Entry and exit | `fl4-arch-x86_64` | Trusted | SYSCALL/SYSRET, interrupt and exception stubs, register save into the TCB, per-core GS state, FPU switching |
| Transaction runtime | `fl4-sync` | Sim-tested | Runs each kernel entry as a transaction: lock acquisition, validation, retry, escalation, IPI servicing while spinning |
| Kernel logic | `fl4-core` | Verified | Syscall dispatch, decode, CSpace, CDT, IPC, notifications, untyped, scheduling, MCS refills, VSpace logic, IRQ objects. Safe Rust only, generic over the store and arch traits |
| Object store | `fl4-store` | Trusted | Turns typed object references into Rust references over physical memory. In the simulator it also checks that every access is covered by a held lock |
| Hardware backends | | Trusted | Page-table writes, TLB and cache maintenance, x2APIC, TSC-deadline timer, IOAPIC/MSI, ACPI parsing, serial |

### Workspace layout

    fl4/
      crates/
        fl4-abi/          # generated from interfaces/ and .bf; no_std, no unsafe
        fl4-bitfield-gen/ # Rust backend for seL4's bitfield_gen.py
        fl4-core/         # #![forbid(unsafe_code)]; the Aeneas input
        fl4-sync/         # seqlock table, lock sets, transactions, IPI-aware spinning
        fl4-store/        # PhysStore (bare metal) and SimStore (checked)
        fl4-arch/         # Arch + Platform traits, shared by all backends
        fl4-arch-x86_64/  # entry asm, paging, APIC, timer, FPU, VT-d (later)
        fl4-arch-aarch64/ # placeholder that compiles; filled after M5
        fl4-kernel/       # the kernel binary: boot, glue, linker script
        fl4-sim/          # deterministic simulator and oracles (host binary)
      proofs/             # Lean 4 project (Lake)
        Extracted/        # Aeneas output, regenerated in CI, never hand-edited
        Spec/             # abstract spec, ported from seL4's Isabelle ASpec (MCS)
        Invariants/  Refinement/  Footprint/
      cmake/              # drop-in "kernel" for seL4 CMake projects (sel4test)
      interfaces/         # the one interface definition: seL4's XML imported, plus FL4 methods
      libsel4/            # FL4's libsel4: generated headers + seL4's hand-written ones
      vendor/seL4/        # pinned upstream, for CMake config, generators and the fuzzer's seL4 build
      xtask/              # codegen, extract, prove, sim, sel4test runners

## 6. The verified core

`fl4-core` holds every kernel decision. It has to stay inside the Rust subset that Charon and Aeneas translate, so we design for that from the start rather than retrofit it.

### Rules for `fl4-core`

- `#![no_std]`, no `alloc`, `#![forbid(unsafe_code)]`. No raw pointers, `Cell`, `RefCell`, atomics, `dyn` or closures stored in data.
- Objects are named by typed physical-address handles (`TcbRef`, `EpRef`, `SlotRef`, …), never by references held across calls. Intrusive lists (endpoint queues, ready queues, the CDT) link handles, as in seL4.
- Every fallible path returns `Result`. Arithmetic uses explicit checked or wrapping operations. Aeneas models overflow as failure, so "never fails" theorems cover overflow too.
- Loops are bounded by data the kernel controls (queue length, CNode radix, preemption-point counters). Long operations return to the caller at preemption points, exactly as seL4 does.
- Dependency on hardware goes through two traits: `Store` for kernel memory and `Arch` for machine operations. Both are plain generic parameters, which Aeneas turns into Lean structure arguments.
- CI runs Charon and Aeneas on every commit. A construct Aeneas cannot translate fails the build. This "extractability gate" is the main guard against slowly drifting out of the subset.

### Shape of the core API

seL4 already splits every invocation into a mostly read-only *decode* and a writing *invoke*. FL4 makes that split strict and uses it for concurrency: `prepare` only reads and returns the full set of objects the step will touch, and `perform` writes only inside that set.

    // fl4-core: safe Rust, extracted by Aeneas
    pub trait Store {
        fn tcb(&self, r: TcbRef) -> Result<&Tcb, Fault>;
        fn tcb_mut(&mut self, r: TcbRef) -> Result<&mut Tcb, Fault>;
        fn ep(&self, r: EpRef) -> Result<&Endpoint, Fault>;
        // … one pair per object kind, plus slot and CNode access
    }

    pub struct Footprint { objs: LockSet }   // bounded, sorted, deduplicated

    pub enum Prepared {
        Ready { plan: Plan, fp: Footprint },   // all decisions made; perform cannot fail on lookup
        Need(ObjId),                            // discovered a new object; lock it and re-run prepare
        Done(SyscallResult),                    // error found while decoding; no writes needed
    }

    pub fn prepare<S: Store, A: Arch>(s: &S, cpu: CpuId, entry: &Entry) -> Result<Prepared, Fault>;
    pub fn perform<S: Store, A: Arch>(s: &mut S, a: &mut A, plan: Plan) -> Result<Outcome, Fault>;

On one core, `prepare` followed by `perform` is the whole kernel entry, and the transaction runtime only checks a flag set at boot. The proofs are about this serial composition.

### Ghost footprints

In the Lean model of `Store`, every access records the object it touched. We prove two lemmas per entry point: `perform` touches only objects in the footprint returned by `prepare`, and the result of `prepare` depends only on objects it touched. These are serial theorems, so Aeneas can discharge them, yet they are exactly what the lock protocol in §7 needs to be correct. They are the bridge between the serial proof and concurrent execution.

## 7. Fine-grained locking

seL4 SMP protects the whole kernel with one CLH lock (`NODE_LOCK_SYS` in `include/smp/lock.h`). FL4 runs every kernel entry as a short transaction over only the objects it touches.

### The striped seqlock table

Endpoints are 16 bytes and cap slots 32, and a CNode holds thousands of slots. Instead of growing every small object and every slot by a lock word, FL4 keeps locks in a global table indexed by a hash of the object's physical address.

- Each entry is one cache-line-padded 64-bit word: a lock bit and a 63-bit version. Writers set the bit, bump the version on release. Readers can check a version without writing to the line. The default is 4096 entries (256 KiB), configurable.
- Two objects that hash to the same entry share a lock. This costs some false contention but never correctness, because the protocol only needs "a held lock covers the object".
- Per-core scheduler state (ready queues, release queue, reschedule flag, current SC accounting) uses a separate array of per-core locks. These rank above every table entry.
- The total order for deadlock freedom is: table entries by index, then per-core scheduler locks by core id. A transaction that holds a lock never blocks on a lower-ranked one.

### Transaction protocol

Each kernel entry, and each chunk of a preemptible operation, runs as follows:

``` mermaid
flowchart LR
  E[Kernel entry] --> P[prepare on current snapshot]
  P -->|Need obj| L{lock rank above all held?}
  L -->|yes| A[spin-acquire] --> P
  L -->|no| T[try-lock]
  T -->|ok| P
  T -->|busy| R[release all, re-acquire in order] --> P
  P -->|Ready| V[validate read versions]
  V -->|changed| R
  V -->|ok| W[perform, all locks held]
  W --> X[release, bump versions, exit]
  P -->|Done| X
  R -->|retries exceed N| S[escalate to serial mode] --> P
```

- **Writes under strict two-phase locking.** Every object in the write set is locked before `perform` starts and stays locked until it ends. `perform` never acquires locks.
- **Reads validated optimistically.** CSpace walks read slots without locking, recording each slot's table version. Before `perform`, the runtime re-checks those versions. This keeps shared CSpaces fast: sel4test threads share one CSpace, and every invocation reads slots in it.
- **No dereference before validation.** Lock-free reads of kernel memory go through atomic loads in `fl4-store`, so a read of a slot that was just deleted and retyped returns garbage, not undefined behavior. The garbage is discarded when validation fails. The kernel window maps all of kernel memory, so these reads never fault.
- **Bounded retries, then serial mode.** Normal transactions hold a per-core shared flag on a global "serial gate". After N retries (default 4), a transaction takes the gate exclusively and waits for in-flight transactions to drain. This guarantees progress and gives a worst-case bound similar to the big lock. Rare global operations (domain schedule, IRQ control, ASID pool allocation) also use the gate.
- **IPI-aware spinning.** seL4 services remote-stall IPIs while spinning on its lock. FL4 does the same in every spin loop. IPI handlers touch only core-local state, so a core that is waiting for an IPI acknowledgement cannot deadlock with a core that is spinning on its lock.

### Footprints of common operations

| Operation                             | Locked objects                                                         | Validated reads                              |
|---------------------------------------|------------------------------------------------------------------------|----------------------------------------------|
| Call to a waiting passive server      | caller TCB, endpoint, server TCB, reply object, caller SC, sched(core) | endpoint cap slot, reply cap slot            |
| ReplyRecv                             | server TCB, reply, client TCB, endpoint, SC, sched(core)               | endpoint and reply cap slots                 |
| Signal, nobody waiting                | notification                                                           | notification cap slot                        |
| Signal wakes a thread on another core | notification, waiter TCB, sched(target core)                           | notification cap slot; IPI sent after commit |
| CNode_Copy / Mint                     | source slot, destination slot, source's CDT next-neighbor              | CSpace path slots                            |
| Delete (one preemption chunk)         | slot, CDT prev and next, object if final cap                           | CSpace path slots                            |
| Untyped_Retype (one chunk)            | untyped slot, destination slots, CDT neighbors                         | CSpace path slots                            |
| Timer interrupt (MCS)                 | current TCB, current SC, sched(core)                                   | none                                         |

The CDT stays seL4's doubly linked list in derivation order, so the "is this the final cap" check and inserts only need the slot and its two neighbors. Neighbors are discovered in `prepare` and added to the footprint like any other object. With MCS, IPC uses reply objects instead of reply caps, so the IPC path never touches the CDT. This is one of the main reasons FL4 builds on MCS.

### Implementation: a transactional Store

FL4 builds this protocol into `fl4-store` rather than into a `prepare`/`perform` split of every operation in `fl4-core`. The core keeps its serial form, the one the proofs are about, and each kernel entry runs against a transactional `Store`:

- **Reads** look up the object's entry in the striped seqlock table and are valid only if the entry is unlocked and its version is no newer than the version clock read when the transaction began (TL2). A failed check aborts the entry at once, so the core only ever sees a consistent snapshot. Every loop in the core is bounded (P0), so a snapshot can never make it run away.
- **Writes** go to a per-core write buffer. At commit, the entries covering the write set are locked in table order, the read set is validated, the buffer is applied, and the versions are bumped and released.
- **Arch effects** that other cores could observe (IPIs, timer programming, interrupt acknowledgement, TLB invalidation, console output) are queued and run after commit. Effects that cannot be deferred or undone (port I/O, remote stalls, FPU transfers between cores) abort the transaction and rerun it under the serial gate, which is also where a transaction goes after N failed attempts.
- The footprint of an entry is the set of entries it actually touched, exact by construction. The footprint lemmas planned as P2 become a property of this runtime, tested in the simulator by the footprint and serializability oracles (§10), rather than one Lean lemma per entry point. The argument in §9 is unchanged: each committed transaction behaves like a serial kernel entry on a consistent snapshot, and two-phase locking with validated reads makes the history conflict-serializable.

### Ownership of running threads

A TCB whose thread is running on core C has its register context owned by C. A remote operation that changes that context, such as `TCB_WriteRegisters` or suspend, locks the TCB and then stalls C with an IPI, like seL4's `remoteTCBStall`. When the kernel finds only one core, lock operations, the serial gate and IPIs are skipped behind a flag set at boot, which keeps uniprocessor IPC free of atomic operations.

## 8. SMP and MCS semantics

FL4 follows seL4 17.0 MCS+SMP behavior exactly. The design points that matter for locking:

- Each core has its own `SchedControl` cap, ready queues with priority bitmap, release queue and timer. A thread runs on the core of its bound scheduling context.
- When a client donates its SC to a passive server on Call, the server runs on the client's core. Migration takes the source and destination scheduler locks in core-id order.
- Budget accounting reads the per-core TSC and updates only the current SC, which is in the timer path's footprint. The refill algorithm (`src/kernel/sporadic.c`) is ported directly and verified on its own: refill invariants are some of the first Lean proofs.
- Cross-core wakeups update the target core's queues under its scheduler lock, set its reschedule flag, then send an IPI after the transaction commits, never while holding locks.
- The domain scheduler keeps seL4's global schedule. Changes go through the serial gate.

## 9. Proof plan

The proof is staged so each level is useful by itself and later levels build on earlier ones.

| Level | Statement                                                                                                                                                                                                                                       | Scope                                                                                           |
|-------|-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|-------------------------------------------------------------------------------------------------|
| P0    | Every extracted function terminates without failure (no panic, overflow or out-of-bounds) when the invariants hold                                                                                                                              | All of `fl4-core`                                                                               |
| P1    | Each kernel entry preserves the invariants: well-typed heap, object alignment and non-overlap, CDT well-formed (including subframe aliases), queues consistent with thread states, refill invariants, deadline-timer trees, untyped bookkeeping | All of `fl4-core`                                                                               |
| P2    | Footprint soundness: `perform` stays inside `prepare`'s footprint, and `prepare` depends only on what it read                                                                                                                                   | All entry points; required before fine-grained locking ships                                    |
| P3    | Functional refinement: every kernel entry refines the abstract spec                                                                                                                                                                             | One subsystem at a time: CSpace, then IPC and notifications, scheduler and MCS, untyped, VSpace |
| P3x   | Conservative extension: on any state reachable by seL4 calls alone, every seL4 call behaves exactly as in the ported seL4 spec                                                                                                                  | Proven once for the spec, then again for each extension that touches shared state               |
| P4    | Integrity, then confidentiality                                                                                                                                                                                                                 | After P3                                                                                        |

### The abstract spec

Decided: we port seL4's Isabelle abstract specification (the MCS version, from `l4v/spec/abstract`) to Lean 4 as a nondeterministic state monad. It is long but close to a transliteration, and it keeps FL4 tied to the meaning the seL4 proofs have already validated. Only the parts FL4 builds are ported: no non-MCS paths, no IO page tables, no VCPUs. Where FL4 must differ, such as per-core state, the difference is written down in the spec and listed in one place.

- The port goes subsystem by subsystem in P3 order. Each Lean definition carries a comment naming the Isabelle definition it comes from, so reviewers can compare them side by side.
- The Lean spec is executable where the Isabelle spec is deterministic. Those parts double as a reference model in the simulator and the differential fuzzer.
- Extensions go in separate Lean modules on top of the ported spec, never as edits to it. Theorem P3x states that they leave seL4 behavior unchanged, which is the formal form of the superset rule in §2.

### From serial to concurrent

The argument

\(1\) Each transaction behaves like one serial kernel entry, by P0 to P3. (2) Its accesses stay inside the locks it holds, by P2. (3) Strict two-phase locking with validated reads makes any execution conflict-equivalent to running the transactions one after another in commit order. That step is textbook and will later get its own small Lean proof over an abstract model of `fl4-sync`. (4) What is left unproven is that `fl4-sync`, `fl4-store` and the IPI paths actually implement locks and validation correctly on real memory. The simulator tests exactly that.

### Trusted base

The proof assumes: Rust, LLVM and the linker; Charon, Aeneas and the Lean kernel; the abstract spec; entry assembly and boot code; `fl4-store` and `fl4-sync`; hardware backends; and the processor's memory model. Everything trusted is listed in one file in the repo, with its size tracked in CI.

## 10. Deterministic simulation

`fl4-sim` is a host program that links the real `fl4-core`, `fl4-sync` and a checked `SimStore`, with a simulated arch backend. Nothing is mocked above the hardware line.

### Execution model

- Each simulated CPU is a coroutine. A seeded scheduler decides which CPU runs at every scheduling point: each atomic operation, lock attempt, IPI send and store access. The same seed always replays the same run.
- Time is virtual. Each CPU has its own TSC and TSC-deadline timer, so MCS budget overruns, timeouts and refill edge cases can be hit on purpose.
- Atomics run on a store-buffer model of x86-TSO. For AArch64 the same harness switches to a weak-memory model, so ordering bugs show up before there is AArch64 hardware in CI.
- User programs are Rust closures that issue seL4 syscalls through the simulated register ABI. Workloads include generated random syscall programs, ports of the SMP-sensitive sel4test cases, and targeted races: revoke during IPC, deleting an endpoint with queued threads on several cores, SC exhaustion during migration, signal racing with a thread being bound to another core.

### Oracles

| Oracle                                                                                                                                                                        | Catches                                                                                           |
|-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|---------------------------------------------------------------------------------------------------|
| **Footprint checker.** `SimStore` fails any write to an object whose lock the CPU does not hold, and any read not covered by a lock or a recorded version.                    | Missing locks, found on the first run that executes the path, with no unlucky interleaving needed |
| **Serializability.** Record the commit order, replay the same transactions on a single-core FL4 (the proven configuration), compare every syscall result and the final state. | Lost updates, stale reads, validation bugs                                                        |
| **Invariants.** Executable Rust versions of the P1 invariants, checked after every commit.                                                                                    | Corruption, close to where it starts                                                              |
| **Liveness.** Wait-for graph with cycle detection, bounded retry counts, IPI acknowledgement deadlines.                                                                       | Deadlock, livelock, missed IPIs                                                                   |

### Exploration

- Random walks and PCT (probabilistic concurrency testing) at scale, millions of seeds per night.
- Bounded exhaustive search with partial-order reduction for small scenarios of 2 to 3 CPUs and a few syscalls each. These cover the hand-picked races completely.
- Failing seeds shrink automatically and become regression tests.
- For bugs seen only in QEMU, QEMU record and replay reproduces the full-system run. The simulator remains the main tool.

## 11. x86_64 now, AArch64 next

### x86_64 backend

- Multiboot 1 and 2 entry, so QEMU `-kernel` with the rootserver as a module works the way the seL4 x86 build does. APs start with INIT-SIPI-SIPI.
- SYSCALL/SYSRET, per-core GS-based kernel state, SMEP and SMAP, PCID, and the optional kernel skim window (seL4's KPTI-style mitigation).
- x2APIC or xAPIC, chosen at boot (§3). In xAPIC mode IPIs use physical destination mode, so more than 8 cores can be addressed.
- MCS timer: TSC-deadline mode when CPUID reports it, otherwise the LAPIC one-shot timer with a TSC-to-APIC ratio calibrated at boot. seL4 has the same fallback in `apic.c`. Both are first-class paths, and the test setups in §12 exercise each one.
- IOAPIC and MSI routing, ACPI MADT parsing, IO port caps.
- Eager XSAVE FPU switching. VT-x is out of scope.

### IOMMU left to user space

FL4 has no IO page table objects and no `IOSpace` caps. The kernel never programs the IOMMU.

- The kernel parses the ACPI DMAR (Intel) or IVRS (AMD) table only to find the IOMMU's MMIO registers. It does not reserve them, so they show up in BootInfo as ordinary device untypeds, and the root task can hand them to an IOMMU driver.
- User space finds the DMAR or IVRS table through the ACPI RSDP that seL4 already passes in BootInfo, so no new interface is needed.
- The kernel leaves the IOMMU in whatever state firmware set. A driver that enables translation has to map anything devices need, which is its job.
- The consequence is that DMA isolation now depends on the user-space driver, and devices can reach kernel memory until that driver turns translation on. This is a deliberate trade, and the trusted-base list records it.
- sel4test's IO page table tests are compiled only when `CONFIG_IOMMU` is set, so the suite runs unchanged without them.

### Keeping AArch64 cheap

- `Arch` covers register context, fault decoding, page-table formats as associated types, TLB and cache maintenance, and IRQ controller access. `fl4-core` never names an x86 type.
- Arch-specific kernel objects (page tables, ASID pools, IO ports) are an enum in `fl4-core` selected by `cfg`, with verified logic per architecture. Their invariants are written against the `Arch` trait.
- `fl4-sync` uses only acquire/release orderings plus explicit fences. Nothing relies on x86-TSO, and the simulator's weak-memory mode checks that.
- The AArch64 fixes from l4h are requirements of the port: broadcast TLB invalidation, 16-bit ASIDs, CNTFRQ for MCS accounting, the ID-register BootInfo record, and x8 in trapped-syscall faults (§4).
- The AArch64 placeholder crate compiles in CI from M0, so the trait boundary cannot quietly pick up x86 assumptions.

## 12. sel4test and CI

sel4test finds the kernel through `find_package(seL4)` in its `kernel/` directory and builds libsel4 and the kernel image from there. FL4 ships a drop-in replacement in `cmake/`:

- It reuses upstream seL4's CMake configuration from `vendor/seL4`, so sel4test's settings work unchanged, but builds libsel4 from FL4's `libsel4/` and generators instead of upstream's.
- It replaces only the `kernel.elf` target with a `cargo build` that reads the generated configuration and checks it against §3.
- sel4test runs with `SIMULATION=OFF`, because its `SIMULATION` mode turns on `KernelIOMMU` for x86. With `SIMULATION` off, a debug build also turns on the hardware debug API, so FL4 implements breakpoints and single-step in the debug profile. KVM passes debug registers through to the guest.
- FL4's extensions get their own suite, `fl4test`, built on the same test framework and run in the same QEMU setups. It covers every extension and fix taken from l4h. sel4test itself stays unmodified.
- l4h user space, rebuilt against FL4's libsel4, runs under QEMU/KVM as a second compatibility check. Parts that depend on multikernel boot are skipped.
- `xtask sel4test` links the checkout at `~/Projects/sel4test` with this kernel directory, builds, runs under QEMU and parses the test summary. sel4test has 228 test definitions. Each one is tracked separately so progress is visible.

### Test machine

FL4 is never booted on the development machine's hardware. Every kernel run happens inside a QEMU/KVM guest on that machine, driven locally by `xtask`. Hosted CI can come later with the same commands.

|                   |                                                                                                                                                                            |
|-------------------|----------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| CPU               | AMD Ryzen 7 7700 (Zen 4), 8 cores, 16 threads                                                                                                                              |
| Memory            | 61 GiB                                                                                                                                                                     |
| Virtualisation    | KVM (AMD-V), `/dev/kvm` usable by the build user                                                                                                                           |
| QEMU              | 10.0.13                                                                                                                                                                    |
| Relevant features | Has `pcid`, `invpcid`, `smep`, `smap`, `xsaveopt`, `fsgsbase`, 1 GiB pages, invariant TSC. No TSC-deadline timer. x2APIC is not exposed to the host. AMD-Vi IOMMU present. |

KVM emulates both x2APIC and the TSC-deadline timer for guests, even though this host CPU lacks both. Masking them in the guest CPU model covers the fallback paths that real CPUs without those features would take. So sel4test runs in three QEMU setups:

| Setup                 | QEMU options                                        | Purpose                                                                         |
|-----------------------|-----------------------------------------------------|---------------------------------------------------------------------------------|
| KVM, full features    | `-enable-kvm -cpu host`                             | Fast main loop; x2APIC and TSC-deadline paths. Same kernel image in every setup |
| KVM, reduced features | `-enable-kvm -cpu host,-x2apic,-tsc-deadline`       | xAPIC and the calibrated one-shot timer paths                                   |
| TCG                   | `-accel tcg -icount`, record and replay when needed | Deterministic reruns of failures seen under KVM                                 |

Performance numbers come from KVM with pinned vCPUs and are labelled that way. They are compared with upstream seL4 measured in the same setup, never with bare-metal figures.

### Test matrix

| Job                               | Configurations                                                                                             | When                       |
|-----------------------------------|------------------------------------------------------------------------------------------------------------|----------------------------|
| sel4test on QEMU                  | x86_64 MCS × {1, 2, 4 cores} × {debug, release} × the first two setups above                               | Every PR                   |
| Extract and check proofs          | Charon → Aeneas → `lake build`                                                                             | Every PR                   |
| Simulation, short                 | 10⁴ seeds plus all regression seeds                                                             | Every PR                   |
| Simulation, long                  | Millions of seeds, PCT, exhaustive small scenarios, TSO and weak modes                                     | Nightly                    |
| Differential fuzzing against seL4 | Same generated programs on seL4 and FL4, compare traces                                                    | Nightly                    |
| Performance                       | sel4bench IPC and signal latency; multi-core scaling on independent endpoints; FL4 and seL4 both under KVM | Nightly, tracked over time |

Performance targets: uniprocessor IPC within 1.2× of seL4 built with `KernelFastpath` off (seL4 with its fastpath is also measured and reported, for reference), and near-linear throughput scaling for independent IPC pairs where seL4's big lock stays flat. The machine has 8 physical cores, so scaling is measured up to 8 vCPUs pinned one per physical core.

## 13. Milestones

Ordered by dependency. Each milestone ends with a check that can be run.

- **M0 Scaffolding** — ABI and bitfield generators, workspace, CMake drop-in, Aeneas pipeline on a stub core, boot to a serial banner on QEMU. *Exit: sel4test builds against FL4; extraction runs in CI.*
- **M1 Uniprocessor MCS kernel** — CSpace, CDT, untyped, TCB, endpoints, notifications, reply and SC objects, VSpace, IRQs, faults, debug syscalls, both MCS timer modes. The l4h fixes, and the l4h extensions that do not depend on SMP. *Exit: sel4test passes with 1 core, debug and release, in both KVM setups.*
- **M2 P0 and first P1 proofs** — No-failure proofs for all of `fl4-core`, CDT and refill invariants. *Exit: P0 complete; extraction gate enforced.*
- **M3 SMP in serial-gate mode** — APs, per-core scheduling, IPIs, migration, and the remaining l4h extensions. Every transaction takes the serial gate, which behaves like a big lock. Simulator with oracles running. *Exit: sel4test passes with 2 and 4 cores.*
- **M4 Fine-grained locking** — P2 footprint proofs, then switch on the lock table. Serial-gate mode stays as a test-only Cargo feature for differential runs. It is not a user-facing option. *Exit: P2 complete; nightly simulation clean for two weeks; sel4test passes; scaling target met.*
- **M5 P1 completion and performance** — Full invariant set. Speed up the general IPC path in `fl4-core` without adding a second copy of it. *Exit: P1 complete; uniprocessor IPC within target.*
- **M6 Refinement and breadth** — P3 per subsystem against the ported spec, AArch64 backend. *Exit: each subsystem's refinement proof lands separately.*

## 14. Risks

| Risk                                                                                      | Mitigation                                                                                                                                                                             |
|-------------------------------------------------------------------------------------------|----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| Aeneas cannot express some kernel patterns, or proof terms grow too large at kernel scale | Extractability gate from M0. Keep functions small. Prove against the `Store` trait instead of a concrete heap. Budget time to contribute upstream fixes to Charon and Aeneas.          |
| Porting the abstract spec to Lean is a large job                                          | Port incrementally per subsystem, in the same order as P3. P0 to P2 do not need the abstract spec.                                                                                     |
| Behavior differs from seL4 in cases sel4test does not cover                               | Differential fuzzing against seL4 on QEMU. Decoders follow the C source check by check.                                                                                                |
| Retries make worst-case execution time hard to bound                                      | Serial-gate escalation after N retries gives a bound comparable to the big lock. Measure retry rates in simulation and on hardware.                                                    |
| False sharing in the lock table under load                                                | Table size is configurable. The hash includes high address bits. Monitor collision counters in benchmark builds.                                                                       |
| The simulator misses a bug that only real hardware shows                                  | Keep the trusted runtime tiny, test both KVM CPU models and TCG, and use QEMU record and replay to reproduce.                                                                          |
| KVM hides timing and ordering behavior of real hardware, and one AMD host runs every test | The reduced-feature KVM setup covers the fallback hardware paths. The simulator's memory model does not depend on the host. Add an Intel KVM host once FL4 is ready for wider testing. |

## 15. Decisions

Settled on 2026-11-12.

| Question                    | Decision                                                                                                                                  | Where it applies                             |
|-----------------------------|-------------------------------------------------------------------------------------------------------------------------------------------|----------------------------------------------|
| Support the non-MCS API?    | No. MCS only.                                                                                                                             | §1, §2, §12 |
| Source of the abstract spec | Port seL4's Isabelle abstract spec to Lean.                                                                                               | §9                                 |
| IOMMU                       | No in-kernel support. User space programs the IOMMU directly.                                                                             | §11                                |
| Configuration               | As few options as possible. Hardware is detected at boot, not configured.                                                                 | §3                                |
| API evolution               | FL4 is a superset of the seL4 API. Every seL4 program builds and runs on FL4 from source, but FL4 programs may use extensions seL4 lacks. | §2, §9                  |
| l4h patch series            | Include every fix and feature except VT-x, AMD-V, multikernel partitioning and the debug syscall MCP threshold.                           | §4                                   |
| Binary compatibility        | Not a goal. FL4 is compatible with the seL4 API at the source level and numbers its own ABI.                                              | §2                                |
| Debug syscall MCP threshold | Not supported.                                                                                                                            | §4                                   |
| Multikernel                 | Not supported. FL4 is the only kernel on its machine.                                                                                     | §4                                   |
| Fastpaths                   | None for now. Only the general, verified IPC path.                                                                                        | §1, §3                  |
| Test hardware               | Only inside QEMU/KVM guests on the development machine. FL4 never boots on that machine's hardware.                                       | §12                              |

VT-x stays out of scope until after the AArch64 port. That was a recommendation in draft 1 and nothing has changed it.
