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
 * system registers; at EL1 do nothing. Keeps x19-x21; returns at EL1. */
fl4_el_setup:
    mrs     x9, CurrentEL
    lsr     x9, x9, #2
    cmp     x9, #2
    b.ne    1f
    mov     x9, #(1 << 31)          /* HCR_EL2.RW: EL1 is AArch64 */
    msr     hcr_el2, x9
    isb
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
