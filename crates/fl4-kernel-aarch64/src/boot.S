/* FL4 AArch64 entry from the UEFI loader, and the entry of the other cores
 * from PSCI CPU_ON. Both run at their physical addresses with the MMU and
 * caches off, at EL2 or EL1: this code is position independent and reads
 * no data before the MMU is on except what was cleaned to the point of
 * coherency (`fl4_ap_params`). */

.equ SCTLR_EL1_RES1,  0x30d00800
.equ SCTLR_MMU_ON,    0x34d5d81d
/* T0SZ = T1SZ = 16, 4 KiB granules, write-back inner-shareable walks,
 * 16-bit ASIDs (TCR_EL1.AS); IPS is added from ID_AA64MMFR0_EL1. */
.equ TCR_LO,          0xb5103510
.equ TCR_AS,          (1 << 36)
.equ SPSR_EL1H_MASKED, 0x3c5

.section .boot.text, "ax"
.global _start
_start:
    /* x0: the boot record's offset in the kernel region, which starts
     * here. */
    mov     x19, x0
    adr     x20, _start
    bl      fl4_el_setup
    add     x21, x20, x19
    ldr     x0, [x21, #32]          /* BootInfo.ttbr0 */
    ldr     x1, [x21, #40]          /* BootInfo.ttbr1 */
    bl      fl4_mmu_on
    ldr     x9, =fl4_boot_high
    br      x9

.global _ap_start
_ap_start:
    /* x0: the core's index (the CPU_ON context). */
    mov     x19, x0
    bl      fl4_el_setup
    adr     x9, fl4_ap_params
    ldr     x0, [x9, #0]
    ldr     x1, [x9, #8]
    bl      fl4_mmu_on
    ldr     x9, =fl4_ap_high
    br      x9

/* Leave EL2 for EL1 with EL1 given the timers, FP/SIMD and the GIC
 * system registers, and nothing left that traps EL0 or EL1 to EL2; at EL1
 * do nothing. Keeps x19-x21; returns at EL1. */
fl4_el_setup:
    mrs     x9, CurrentEL
    lsr     x9, x9, #2
    cmp     x9, #2
    b.ne    1f
    /* First the EL2 vectors: the firmware's VBAR_EL2 points into memory
     * that becomes user RAM (boot services code and data), or is UNKNOWN
     * on a core PSCI started. EL2's MMU stays off, so the physical
     * address is the one to give. */
    adr     x9, fl4_el2_vectors
    msr     vbar_el2, x9
    isb
    mov     x9, #(1 << 31)          /* HCR_EL2.RW: EL1 is AArch64 */
    /* Pointer authentication (any of APA, API, GPA, GPI, APA3, GPA3):
     * HCR_EL2.API, or PACGA, which no SCTLR_EL1 bit enables, traps from
     * EL0 to EL2; HCR_EL2.APK, or EL1's key registers trap to EL2. The
     * keys are the firmware's: clear them, so PACGA gives every thread on
     * every core the same function of its operands, of no one's secret. */
    mrs     x10, id_aa64isar1_el1
    ldr     x11, =0xff000ff0
    and     x10, x10, x11
    mrs     x11, s3_0_c0_c6_2       /* ID_AA64ISAR2_EL1 (RAZ before v8.6) */
    and     x11, x11, #0xff00
    orr     x10, x10, x11
    cbz     x10, 7f
    orr     x9, x9, #(3 << 40)      /* HCR_EL2.APK, HCR_EL2.API */
    msr     hcr_el2, x9
    isb
    msr     s3_0_c2_c1_0, xzr       /* APIAKeyLo_EL1 */
    msr     s3_0_c2_c1_1, xzr       /* APIAKeyHi_EL1 */
    msr     s3_0_c2_c1_2, xzr       /* APIBKeyLo_EL1 */
    msr     s3_0_c2_c1_3, xzr       /* APIBKeyHi_EL1 */
    msr     s3_0_c2_c2_0, xzr       /* APDAKeyLo_EL1 */
    msr     s3_0_c2_c2_1, xzr       /* APDAKeyHi_EL1 */
    msr     s3_0_c2_c2_2, xzr       /* APDBKeyLo_EL1 */
    msr     s3_0_c2_c2_3, xzr       /* APDBKeyHi_EL1 */
    msr     s3_0_c2_c3_0, xzr       /* APGAKeyLo_EL1 */
    msr     s3_0_c2_c3_1, xzr       /* APGAKeyHi_EL1 */
7:  msr     hcr_el2, x9
    isb
    /* Fine-grained traps (FEAT_FGT, FEAT_FGT2): reset to UNKNOWN values
     * the firmware may have left set. All clear: no positive trap; the
     * negative (n) bits trap EL0 and EL1 use of registers the kernel does
     * not manage, which fl4_el2_vectors turns into a user exception. */
    mrs     x10, id_aa64mmfr0_el1
    ubfx    x10, x10, #56, #4
    cbz     x10, 8f
    msr     s3_4_c1_c1_4, xzr       /* HFGRTR_EL2 */
    msr     s3_4_c1_c1_5, xzr       /* HFGWTR_EL2 */
    msr     s3_4_c1_c1_6, xzr       /* HFGITR_EL2 */
    msr     s3_4_c3_c1_4, xzr       /* HDFGRTR_EL2 */
    msr     s3_4_c3_c1_5, xzr       /* HDFGWTR_EL2 */
    mrs     x11, id_aa64pfr0_el1
    ubfx    x11, x11, #44, #4       /* AMU */
    cbz     x11, 9f
    msr     s3_4_c3_c1_6, xzr       /* HAFGRTR_EL2 */
9:  cmp     x10, #2
    b.lo    8f
    msr     s3_4_c3_c1_0, xzr       /* HDFGRTR2_EL2 */
    msr     s3_4_c3_c1_1, xzr       /* HDFGWTR2_EL2 */
    msr     s3_4_c3_c1_2, xzr       /* HFGRTR2_EL2 */
    msr     s3_4_c3_c1_3, xzr       /* HFGWTR2_EL2 */
    msr     s3_4_c3_c1_7, xzr       /* HFGITR2_EL2 */
8:  /* HCRX_EL2 (FEAT_HCX), also UNKNOWN at reset: all clear, every
     * extension it enables for EL1 and EL0 off. */
    mrs     x10, id_aa64mmfr1_el1
    ubfx    x10, x10, #40, #4
    cbz     x10, 10f
    msr     s3_4_c1_c2_2, xzr       /* HCRX_EL2 */
10: isb
    /* EL1 physical counter and timer, in both CNTHCTL_EL2 layouts. */
    mov     x9, #3
    orr     x9, x9, #(3 << 10)
    msr     cnthctl_el2, x9
    msr     cntvoff_el2, xzr
    /* No FP/SIMD traps; the CPTR_EL2 layout depends on HCR_EL2.E2H,
     * which may be fixed at 1. */
    mrs     x9, hcr_el2
    tbz     x9, #34, 2f
    mov     x9, #(3 << 20)
    b       3f
2:  mov     x9, #0x33ff
3:  msr     cptr_el2, x9
    msr     hstr_el2, xzr
    mrs     x9, midr_el1
    msr     vpidr_el2, x9
    mrs     x9, mpidr_el1
    msr     vmpidr_el2, x9
    msr     vttbr_el2, xzr
    /* EL1 may use the PMU counters and debug registers. */
    mrs     x9, id_aa64dfr0_el1
    ubfx    x9, x9, #8, #4
    cbz     x9, 4f
    cmp     x9, #0xf                /* IMPLEMENTATION DEFINED: no PMCR_EL0 */
    b.eq    4f
    mrs     x9, pmcr_el0
    ubfx    x9, x9, #11, #5
    b       5f
4:  mov     x9, #0
5:  msr     mdcr_el2, x9
    /* The GIC CPU interface's system registers at EL1. */
    mrs     x9, id_aa64pfr0_el1
    ubfx    x9, x9, #24, #4
    cbz     x9, 6f
    mrs     x9, s3_4_c12_c9_5       /* ICC_SRE_EL2 */
    mov     x10, #0x9               /* SRE, Enable */
    orr     x9, x9, x10
    msr     s3_4_c12_c9_5, x9
    isb
    msr     s3_4_c12_c11_0, xzr     /* ICH_HCR_EL2 */
6:  ldr     x9, =SCTLR_EL1_RES1
    msr     sctlr_el1, x9
    mov     x9, #SPSR_EL1H_MASKED
    msr     spsr_el2, x9
    adr     x9, 1f
    msr     elr_el2, x9
    eret
1:  msr     daifset, #0xf
    ldr     x9, =SCTLR_EL1_RES1
    msr     sctlr_el1, x9
    isb
    ret

/* EL2's exception vectors while FL4 runs, at EL1. Nothing is meant to
 * reach EL2: a synchronous exception from AArch64 EL0 (a trap the setup
 * above did not foresee) goes on to EL1 as an Undefined Instruction
 * exception, as on a core booted at EL1, so the thread gets a user
 * exception fault; anything else stops the core here, in the kernel image,
 * and never runs firmware or user memory at EL2. TPIDR_EL2 is the only
 * scratch: x0 goes back as it came. */
.macro el2_halt
    .balign 128
    b       fl4_el2_halt
.endm

.balign 2048
fl4_el2_vectors:
    .rept 8
    el2_halt                        /* from EL2 */
    .endr
    .balign 128
    b       fl4_el2_reflect         /* lower EL, AArch64, synchronous */
    .rept 7
    el2_halt                        /* IRQ, FIQ, SError, AArch32 */
    .endr

fl4_el2_reflect:
    msr     tpidr_el2, x0
    mrs     x0, spsr_el2
    tst     x0, #0x1f               /* M[4:0] == 0: AArch64 EL0t */
    b.ne    fl4_el2_halt
    msr     spsr_el1, x0
    mrs     x0, elr_el2
    msr     elr_el1, x0
    mov     x0, #(1 << 25)          /* EC 0 (unknown reason), IL */
    msr     esr_el1, x0
    /* PSTATE as an exception to EL1 sets it: EL1h, DAIF masked, and PAN
     * set when SCTLR_EL1.SPAN is clear, else kept. */
    mrs     x0, sctlr_el1
    tbnz    x0, #23, 11f
    ldr     x0, =(SPSR_EL1H_MASKED | (1 << 22))
    b       12f
11: mrs     x0, spsr_el1
    and     x0, x0, #(1 << 22)
    orr     x0, x0, #0x3c0
    orr     x0, x0, #0x4
    orr     x0, x0, #0x1
12: msr     spsr_el2, x0
    mrs     x0, vbar_el1
    add     x0, x0, #0x400          /* lower EL, AArch64, synchronous */
    msr     elr_el2, x0
    mrs     x0, tpidr_el2
    eret

fl4_el2_halt:
    wfi
    b       fl4_el2_halt

/* Turn the EL1 MMU on with TTBR0 = x0 (an identity map of the kernel
 * region) and TTBR1 = x1. */
fl4_mmu_on:
    tlbi    vmalle1
    dsb     nsh
    isb
    ldr     x9, =FL4_MAIR
    msr     mair_el1, x9
    mrs     x9, id_aa64mmfr0_el1
    and     x9, x9, #0xf
    cmp     x9, #5
    mov     x10, #5
    csel    x9, x9, x10, ls
    lsl     x9, x9, #32
    ldr     x10, =TCR_LO
    orr     x9, x9, x10
    mov     x10, #1
    lsl     x10, x10, #36
    orr     x9, x9, x10
    msr     tcr_el1, x9
    msr     ttbr0_el1, x0
    msr     ttbr1_el1, x1
    isb
    ldr     x9, =SCTLR_MMU_ON
    msr     sctlr_el1, x9
    isb
    ic      iallu
    dsb     nsh
    isb
    ret

.ltorg

/* Written by the boot core through the kernel window and cleaned to the
 * point of coherency before each CPU_ON: the tables and stack an
 * application processor starts with. */
.section .boot.data, "aw"
.balign 64
.global fl4_ap_params
fl4_ap_params:
    .quad 0     /* TTBR0 */
    .quad 0     /* TTBR1 */
    .quad 0     /* stack top */
    .quad 0     /* reserved */

.section .text
fl4_boot_high:
    ldr     x9, =fl4_boot_stack_top
    mov     sp, x9
    mov     x0, x19
    bl      fl4_boot
1:  wfi
    b       1b

fl4_ap_high:
    ldr     x9, =fl4_ap_params
    ldr     x9, [x9, #16]
    mov     sp, x9
    mov     x0, x19
    bl      fl4_ap_main
1:  wfi
    b       1b

.ltorg

.section .bss
.balign 16
fl4_boot_stack:
    /* fl4_boot keeps its memory lists here (bootmem.rs, 272 ranges each). */
    .space 131072
fl4_boot_stack_top:
