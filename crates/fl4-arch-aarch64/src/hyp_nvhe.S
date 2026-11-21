/* FL4 AArch64 EL2 nVHE runtime exception vectors and guest world-switch stub.
 *
 * Runs at EL2 with E2H=0 and identity-mapped Normal WB Inner-Shareable MMU
 * enabled (`TTBR0_EL2` = `hyp_ident`). `SP_EL2` permanently holds the physical
 * address of this core's `HypCpu` structure; `TPIDR_EL2` is the 1-register
 * exception-entry scratch. */

.equ HYP_IN_GUEST,         0x00
.equ HYP_REGS_PA,          0x08
.equ HYP_VCPU_PA,          0x10
.equ HYP_HOST_HCR,         0x18
.equ HYP_HOST_MDCR,        0x20
.equ HYP_GUEST_MDCR,       0x28
.equ HYP_GIC_V3,           0x30
.equ HYP_VGIC_LRS,         0x38
.equ HYP_VGIC_N_APR,       0x40
.equ HYP_HAS_RAS,          0x48
.equ HYP_HOST_ELR,         0x50
.equ HYP_HOST_SPSR,        0x58
.equ HYP_HOST_TTBR0,       0x60
.equ HYP_HOST_CPACR,       0x68
.equ HYP_HOST_SP_EL1,      0x70
.equ HYP_HOST_SCTLR,       0x78
.equ HYP_HOST_TCR,         0x80
.equ HYP_HOST_TTBR1,       0x88
.equ HYP_HOST_MAIR,        0x90
.equ HYP_HOST_VBAR,        0x98
.equ HYP_HOST_TPIDR_EL1,   0xa0
.equ HYP_HOST_CNTKCTL,     0xa8
.equ HYP_HOST_MDSCR,       0xb0
.equ HYP_GUEST_MDCCINT_NZ, 0xb8
.equ HYP_GUEST_RAS_NZ,     0xc0
.equ HYP_GUEST_CNTVOFF_NZ, 0xc8
.equ HYP_CUR_ACTLR,        0xd0
.equ HYP_CUR_VTTBR,        0xd8
.equ HYP_CUR_VPIDR,        0xe0
.equ HYP_CUR_VMPIDR,       0xe8
.equ HYP_VGIC_LIVE,        0xf0
.equ HYP_VGIC_LR_MASK,     0xf8
.equ HYP_CUR_VMCR,         0x100
.equ HYP_CUR_AP0R,         0x108
.equ HYP_CUR_AP1R,         0x128
.equ HYP_HOST_ACTLR,       0x148
.equ HYP_CUR_CPTR,         0x150
.equ HYP_CUR_CNTV_CTL,     0x158
.equ HYP_CUR_CNTV_CVAL,    0x160
.equ HYP_CUR_CSSELR,       0x168
.equ HYP_CUR_MDSCR,        0x170
.equ HYP_VGIC_OWNER,       0x178

.equ HYP_KIND_SYNC,        0
.equ HYP_KIND_IRQ,         1
.equ HYP_KIND_SERROR,      2
.equ HYP_KIND_RETRY,       3

.equ HYP_SPSR_EL1H_MASKED, 0x3c5

.macro hyp_ventry label
    .balign 128
    b       \label
.endm

.macro vgic_load_apr idx, ap0_sys, ap1_sys
    ldr     x11, [x10, #8 * (40 + \idx)]
    ldr     x12, [sp, #(HYP_CUR_AP0R + 8 * \idx)]
    cmp     x11, x12
    b.eq    110\@f
    msr     \ap0_sys, x11
    str     x11, [sp, #(HYP_CUR_AP0R + 8 * \idx)]
110\@:
    ldr     x11, [x10, #8 * (44 + \idx)]
    ldr     x12, [sp, #(HYP_CUR_AP1R + 8 * \idx)]
    cmp     x11, x12
    b.eq    111\@f
    msr     \ap1_sys, x11
    str     x11, [sp, #(HYP_CUR_AP1R + 8 * \idx)]
111\@:
.endm

.macro vgic_load_lr idx, sysreg
    cmp     x9, #\idx
    b.ls    30f
    ldr     x11, [x10, #8 * (48 + \idx)]
    cbnz    x11, 100\@f
    tbz     x14, #\idx, 101\@f
    msr     \sysreg, xzr
    b       101\@f
100\@:
    msr     \sysreg, x11
    orr     x15, x15, #(1 << \idx)
101\@:
.endm

.macro vgic_save_lr idx, sysreg
    tbz     x14, #\idx, 200\@f
    tbnz    x12, #\idx, 201\@f
    mrs     x11, \sysreg
    str     x11, [x10, #8 * (48 + \idx)]
    b       200\@f
201\@:
    ldr     x11, [x10, #8 * (48 + \idx)]
    bic     x11, x11, #(3 << 62)
    str     x11, [x10, #8 * (48 + \idx)]
200\@:
.endm

.section .hyp.text, "ax"
.balign 2048
.global fl4_hyp_vectors
fl4_hyp_vectors:
    hyp_ventry fl4_hyp_halt         /* EL2t sync */
    hyp_ventry fl4_hyp_halt         /* EL2t IRQ */
    hyp_ventry fl4_hyp_halt         /* EL2t FIQ */
    hyp_ventry fl4_hyp_halt         /* EL2t SError */
    hyp_ventry fl4_hyp_halt         /* EL2h sync */
    hyp_ventry fl4_hyp_halt         /* EL2h IRQ */
    hyp_ventry fl4_hyp_halt         /* EL2h FIQ */
    hyp_ventry fl4_hyp_halt         /* EL2h SError */
    hyp_ventry fl4_hyp_sync         /* Lower EL AArch64 sync */
    hyp_ventry fl4_hyp_irq          /* Lower EL AArch64 IRQ */
    hyp_ventry fl4_hyp_fiq          /* Lower EL AArch64 FIQ */
    hyp_ventry fl4_hyp_serror       /* Lower EL AArch64 SError */
    hyp_ventry fl4_hyp_sync_a32     /* Lower EL AArch32 sync */
    hyp_ventry fl4_hyp_irq          /* Lower EL AArch32 IRQ */
    hyp_ventry fl4_hyp_fiq          /* Lower EL AArch32 FIQ */
    hyp_ventry fl4_hyp_serror       /* Lower EL AArch32 SError */

fl4_hyp_halt:
    wfi
    b       fl4_hyp_halt

/* ---- Vector entry dispatch ------------------------------------------------ */

fl4_hyp_sync:
    hint    #22                     /* clrbhb */
    msr     tpidr_el2, x0
    ldr     x0, [sp, #HYP_IN_GUEST]
    cbnz    x0, fl4_hyp_guest_sync
    /* Host EL0/EL1 synchronous exception to EL2.
     * Check EC == 0x07 (FP/SIMD trap from lazy CPTR_EL2.TFP=1 left after
     * guest exit) before EL0 reflection or EL1 HVC dispatch. */
    mrs     x0, esr_el2
    lsr     x0, x0, #26
    cmp     x0, #0x07
    b.ne    1f
    mov     x0, #0x33ff
    msr     cptr_el2, x0
    str     x0, [sp, #HYP_CUR_CPTR]
    isb
    mrs     x0, tpidr_el2
    eret
1:
    mrs     x0, spsr_el2
    tst     x0, #0x1f               /* M[4:0] == 0: AArch64 EL0t */
    b.eq    fl4_hyp_reflect_el0
    /* Must be EL1 HVC64 (EC == 0x16). */
    mrs     x0, esr_el2
    lsr     x0, x0, #26
    cmp     x0, #0x16
    b.ne    fl4_hyp_halt
    mrs     x0, tpidr_el2
    cmp     x0, #1
    b.eq    fl4_hyp_vcpu_run
    cmp     x0, #2
    b.eq    fl4_hyp_set_vtcr
    cmp     x0, #3
    b.eq    fl4_hyp_tlbi_ipas2
    cmp     x0, #4
    b.eq    fl4_hyp_tlbi_vmalls12_is
    cmp     x0, #5
    b.eq    fl4_hyp_tlbi_vmalls12_local
    cmp     x0, #6
    b.eq    fl4_hyp_vgic_vtr
    cmp     x0, #7
    b.eq    fl4_hyp_quiesce_vgic
    cmp     x0, #8
    b.eq    fl4_hyp_read_vgic_eisr
    cmp     x0, #9
    b.eq    fl4_hyp_save_host_regs
    cmp     x0, #10
    b.eq    fl4_hyp_set_cntp
    cmp     x0, #11
    b.eq    fl4_hyp_flush_vgic
    cmp     x0, #12
    b.eq    fl4_hyp_tlbi_alle1_is
    b       fl4_hyp_halt

fl4_hyp_sync_a32:
    hint    #22
    msr     tpidr_el2, x0
    ldr     x0, [sp, #HYP_IN_GUEST]
    cbnz    x0, fl4_hyp_guest_sync
    b       fl4_hyp_halt

fl4_hyp_irq:
fl4_hyp_fiq:
    hint    #22
    msr     tpidr_el2, x0
    ldr     x0, [sp, #HYP_IN_GUEST]
    cbz     x0, fl4_hyp_halt
    ldr     x0, [sp, #HYP_REGS_PA]
    str     x1, [x0, #8]
    mrs     x1, tpidr_el2
    str     x1, [x0, #0]
    mov     x1, #HYP_KIND_IRQ
    b       fl4_hyp_guest_exit_common

fl4_hyp_serror:
    hint    #22
    msr     tpidr_el2, x0
    ldr     x0, [sp, #HYP_IN_GUEST]
    cbz     x0, fl4_hyp_halt
    ldr     x0, [sp, #HYP_REGS_PA]
    str     x1, [x0, #8]
    mrs     x1, tpidr_el2
    str     x1, [x0, #0]
    mov     x1, #HYP_KIND_SERROR
    b       fl4_hyp_guest_exit_common

/* Reflect an unexpected AArch64 EL0 trap to EL1 as Undefined Instruction. */
fl4_hyp_reflect_el0:
    mrs     x0, spsr_el2
    msr     spsr_el1, x0
    mrs     x0, elr_el2
    msr     elr_el1, x0
    mov     x0, #(1 << 25)
    msr     esr_el1, x0
    mrs     x0, sctlr_el1
    tbnz    x0, #23, 1f
    ldr     x0, =(HYP_SPSR_EL1H_MASKED | (1 << 22))
    b       2f
1:  mrs     x0, spsr_el1
    and     x0, x0, #(1 << 22)
    orr     x0, x0, #0x3c0
    orr     x0, x0, #0x4
    orr     x0, x0, #0x1
2:  msr     spsr_el2, x0
    mrs     x0, vbar_el1
    add     x0, x0, #0x400
    msr     elr_el2, x0
    mrs     x0, tpidr_el2
    eret

/* ---- Small EL2 maintenance HVCs ------------------------------------------- */

fl4_hyp_save_host_regs:
    mrs     x9, sctlr_el1
    mrs     x10, tcr_el1
    stp     x9, x10, [sp, #HYP_HOST_SCTLR]
    mrs     x9, ttbr1_el1
    mrs     x10, mair_el1
    stp     x9, x10, [sp, #HYP_HOST_TTBR1]
    mrs     x9, vbar_el1
    mrs     x10, tpidr_el1
    stp     x9, x10, [sp, #HYP_HOST_VBAR]
    mrs     x9, cntkctl_el1
    mrs     x10, mdscr_el1
    stp     x9, x10, [sp, #HYP_HOST_CNTKCTL]
    str     x10, [sp, #HYP_CUR_MDSCR]
    mrs     x9, actlr_el1
    str     x9, [sp, #HYP_HOST_ACTLR]
    str     x9, [sp, #HYP_CUR_ACTLR]
    mov     x0, #0
    eret

fl4_hyp_set_cntp:
    cbz     x3, 1f
    msr     cntp_cval_el0, x1
1:  msr     cntp_ctl_el0, x2
    isb
    mov     x0, #0
    eret

fl4_hyp_set_vtcr:
    msr     vtcr_el2, x1
    msr     vttbr_el2, x2
    str     x2, [sp, #HYP_CUR_VTTBR]
    isb
    tlbi    vmalls12e1
    dsb     nsh
    isb
    mov     x0, #0
    eret

fl4_hyp_tlbi_ipas2:
    mrs     x9, vttbr_el2
    msr     vttbr_el2, x1
    isb
    dsb     ishst
    tlbi    ipas2e1is, x2
    dsb     ish
    tlbi    vmalle1is
    dsb     ish
    isb
    msr     vttbr_el2, x9
    isb
    mov     x0, #0
    eret

fl4_hyp_tlbi_vmalls12_is:
    mrs     x9, vttbr_el2
    msr     vttbr_el2, x1
    isb
    dsb     ishst
    tlbi    vmalls12e1is
    dsb     ish
    isb
    msr     vttbr_el2, x9
    isb
    mov     x0, #0
    eret

fl4_hyp_tlbi_vmalls12_local:
    tlbi    alle1
    dsb     nsh
    isb
    mov     x0, #0
    eret

fl4_hyp_tlbi_alle1_is:
    dsb     ishst
    tlbi    alle1is
    dsb     ish
    isb
    mov     x0, #0
    eret

fl4_hyp_vgic_vtr:
    mrs     x0, s3_4_c12_c11_1      /* ICH_VTR_EL2 */
    eret

fl4_hyp_quiesce_vgic:
    msr     s3_4_c12_c11_0, xzr     /* ICH_HCR_EL2 */
    str     xzr, [sp, #HYP_VGIC_LIVE]
    isb
    mov     x0, #0
    eret

fl4_hyp_read_vgic_eisr:
    mrs     x0, s3_4_c12_c11_3      /* ICH_EISR_EL2 */
    msr     s3_4_c12_c11_0, xzr     /* ICH_HCR_EL2 = 0 (deassert PPI 25) */
    str     xzr, [sp, #HYP_VGIC_LIVE]
    isb
    eret

fl4_hyp_flush_vgic:
    ldr     x9, [sp, #HYP_VGIC_OWNER]
    cbz     x9, 1f
    add     x9, x9, #0x40
    mrs     x11, s3_4_c12_c11_7     /* ICH_VMCR_EL2 */
    str     x11, [x9, #8 * 36]
    str     x11, [sp, #HYP_CUR_VMCR]
    ldr     x10, [sp, #HYP_VGIC_N_APR]
    cbz     x10, 2f
    mrs     x11, s3_4_c12_c8_0
    mrs     x12, s3_4_c12_c9_0
    str     x11, [x9, #8 * 40]
    str     x12, [x9, #8 * 44]
    str     x11, [sp, #(HYP_CUR_AP0R + 8 * 0)]
    str     x12, [sp, #(HYP_CUR_AP1R + 8 * 0)]
    cmp     x10, #2
    b.lo    2f
    mrs     x11, s3_4_c12_c8_1
    mrs     x12, s3_4_c12_c9_1
    str     x11, [x9, #8 * 41]
    str     x12, [x9, #8 * 45]
    str     x11, [sp, #(HYP_CUR_AP0R + 8 * 1)]
    str     x12, [sp, #(HYP_CUR_AP1R + 8 * 1)]
    cmp     x10, #4
    b.lo    2f
    mrs     x11, s3_4_c12_c8_2
    mrs     x12, s3_4_c12_c9_2
    str     x11, [x9, #8 * 42]
    str     x12, [x9, #8 * 46]
    str     x11, [sp, #(HYP_CUR_AP0R + 8 * 2)]
    str     x12, [sp, #(HYP_CUR_AP1R + 8 * 2)]
    mrs     x11, s3_4_c12_c8_3
    mrs     x12, s3_4_c12_c9_3
    str     x11, [x9, #8 * 43]
    str     x12, [x9, #8 * 47]
    str     x11, [sp, #(HYP_CUR_AP0R + 8 * 3)]
    str     x12, [sp, #(HYP_CUR_AP1R + 8 * 3)]
2:  dsb     ishst
    str     xzr, [sp, #HYP_VGIC_OWNER]
1:  mov     x0, #0
    eret

/* ---- HVC_VCPU_RUN: Host EL1 -> Guest EL1/EL0 ------------------------------ */
/* x1 = regs_pa, x2 = vcpu_pa, x3 = vttbr, x4 = hcr_nvhe, x5 = trap_fp */
fl4_hyp_vcpu_run:
    /* Save only the 5 dynamic host registers; constant host EL1 regs were saved
     * once at boot by HVC_HYP_SAVE_HOST_REGS. */
    mrs     x9, elr_el2
    mrs     x10, spsr_el2
    stp     x9, x10, [sp, #HYP_HOST_ELR]
    mrs     x9, ttbr0_el1
    mrs     x10, cpacr_el1
    stp     x9, x10, [sp, #HYP_HOST_TTBR0]
    mrs     x9, sp_el1
    str     x9, [sp, #HYP_HOST_SP_EL1]

    /* Record guest context pointers and mark in_guest = 1. */
    mov     x9, #1
    str     x9, [sp, #HYP_IN_GUEST]
    stp     x1, x2, [sp, #HYP_REGS_PA]

    /* Configure EL2 controls for guest execution (skip VTTBR_EL2 if unchanged). */
    ldr     x9, [sp, #HYP_CUR_VTTBR]
    cmp     x3, x9
    b.eq    10f
    msr     vttbr_el2, x3
    str     x3, [sp, #HYP_CUR_VTTBR]
10:
    bic     x4, x4, #(1 << 34)      /* Ensure HCR_EL2.E2H == 0 */
    msr     hcr_el2, x4
    ldr     x9, [sp, #HYP_GUEST_MDCR]
    msr     mdcr_el2, x9
    /* CPTR_EL2 (E2H=0): TFP (bit 10) set when trap_fp != 0; skip msr if unchanged. */
    mov     x9, #0x33ff
    cbz     x5, 1f
    orr     x9, x9, #(1 << 10)
1:  ldr     x10, [sp, #HYP_CUR_CPTR]
    cmp     x9, x10
    b.eq    12f
    msr     cptr_el2, x9
    str     x9, [sp, #HYP_CUR_CPTR]
12:

    /* Load guest EL1 sysregs, timer, and VGICv3 from vcpu_pa + 0x40. */
    add     x10, x2, #0x40
    ldp     x11, x12, [x10, #8 * 0] /* SCTLR, CPACR */
    msr     sctlr_el1, x11
    msr     cpacr_el1, x12
    ldp     x11, x12, [x10, #8 * 2] /* TCR, TTBR0 */
    msr     tcr_el1, x11
    msr     ttbr0_el1, x12
    ldp     x11, x12, [x10, #8 * 4] /* TTBR1, MAIR */
    msr     ttbr1_el1, x11
    msr     mair_el1, x12
    ldp     x11, x12, [x10, #8 * 6] /* AMAIR, CIDR */
    msr     amair_el1, x11
    msr     contextidr_el1, x12
    ldp     x11, x12, [x10, #8 * 8] /* AFSR0, AFSR1 */
    msr     afsr0_el1, x11
    msr     afsr1_el1, x12
    ldp     x11, x12, [x10, #8 * 10] /* ESR, FAR */
    msr     esr_el1, x11
    msr     far_el1, x12
    ldp     x11, x12, [x10, #8 * 12] /* PAR, VBAR */
    msr     par_el1, x11
    msr     vbar_el1, x12
    ldp     x11, x12, [x10, #8 * 14] /* TPIDR_EL1, VMPIDR_EL2 */
    msr     tpidr_el1, x11
    ldr     x9, [sp, #HYP_CUR_VMPIDR]
    cmp     x12, x9
    b.eq    11f
    msr     vmpidr_el2, x12
    str     x12, [sp, #HYP_CUR_VMPIDR]
11:
    ldp     x11, x12, [x10, #8 * 16] /* SP_EL1, ELR_EL1 */
    msr     sp_el1, x11
    msr     elr_el1, x12
    ldp     x11, x12, [x10, #8 * 18] /* SPSR_EL1, CSSELR_EL1 */
    msr     spsr_el1, x11
    ldr     x9, [sp, #HYP_CUR_CSSELR]
    cmp     x12, x9
    b.eq    13f
    msr     csselr_el1, x12
    str     x12, [sp, #HYP_CUR_CSSELR]
13:

    /* Lazy RAS (VDISR_EL2 / VSESR_EL2): only touch if non-zero or HCR_EL2.VSE=1. */
    ldr     x9, [sp, #HYP_HAS_RAS]
    cbz     x9, 2f
    ldr     x11, [x10, #8 * 20]     /* VDISR_EL2 */
    ldr     x12, [x10, #8 * 27]     /* VSESR_EL2 */
    orr     x9, x11, x12
    tbnz    x4, #8, 20f             /* HCR_EL2.VSE (bit 8) */
    cbnz    x9, 20f
    str     xzr, [sp, #HYP_GUEST_RAS_NZ]
    b       2f
20:
    msr     s3_4_c12_c1_1, x11
    msr     s3_4_c5_c2_3, x12
    mov     x9, #1
    str     x9, [sp, #HYP_GUEST_RAS_NZ]
2:
    /* Lazy CNTVOFF_EL2: skip when 0. */
    ldr     x11, [x10, #8 * 23]     /* CNTVOFF */
    cbz     x11, 21f
    msr     cntvoff_el2, x11
    mov     x9, #1
    str     x9, [sp, #HYP_GUEST_CNTVOFF_NZ]
    b       22f
21:
    str     xzr, [sp, #HYP_GUEST_CNTVOFF_NZ]
22:
    ldp     x11, x12, [x10, #8 * 21] /* CNTV_CTL, CNTV_CVAL */
    ldr     x9, [sp, #HYP_CUR_CNTV_CVAL]
    cmp     x12, x9
    b.eq    221f
    msr     cntv_cval_el0, x12
    str     x12, [sp, #HYP_CUR_CNTV_CVAL]
221:
    ldr     x9, [sp, #HYP_CUR_CNTV_CTL]
    cmp     x11, x9
    b.eq    222f
    msr     cntv_ctl_el0, x11
    str     x11, [sp, #HYP_CUR_CNTV_CTL]
222:
    ldp     x11, x12, [x10, #8 * 24] /* CNTKCTL_EL1, VPIDR_EL2 */
    msr     cntkctl_el1, x11
    ldr     x9, [sp, #HYP_CUR_VPIDR]
    cmp     x12, x9
    b.eq    23f
    msr     vpidr_el2, x12
    str     x12, [sp, #HYP_CUR_VPIDR]
23:
    /* Cached ACTLR_EL1 (guest writes are trapped by HCR_EL2.TACR=1). */
    ldr     x11, [x10, #8 * 28]     /* ACTLR_EL1 */
    ldr     x9, [sp, #HYP_CUR_ACTLR]
    cmp     x11, x9
    b.eq    24f
    msr     actlr_el1, x11
    str     x11, [sp, #HYP_CUR_ACTLR]
24:
    /* Cached MDSCR_EL1 + lazy MDCCINT_EL1 (trapped by MDCR_EL2.TDA=1). */
    ldp     x11, x12, [x10, #8 * 29] /* MDSCR_EL1, MDCCINT_EL1 */
    ldr     x9, [sp, #HYP_CUR_MDSCR]
    cmp     x11, x9
    b.eq    241f
    msr     mdscr_el1, x11
    str     x11, [sp, #HYP_CUR_MDSCR]
241:
    cbz     x12, 25f
    msr     s2_0_c0_c2_0, x12
    mov     x9, #1
    str     x9, [sp, #HYP_GUEST_MDCCINT_NZ]
    b       26f
25:
    str     xzr, [sp, #HYP_GUEST_MDCCINT_NZ]
26:

    /* Sparse / lazy GICv3 ICH_* restore with per-core VMCR/AP*R ownership. */
    ldr     x9, [sp, #HYP_GIC_V3]
    cbz     x9, 4f
    ldr     x9, [sp, #HYP_VGIC_OWNER]
    cmp     x9, x2
    b.eq    27f
    cbz     x9, 270f
    add     x9, x9, #0x40
    mrs     x11, s3_4_c12_c11_7     /* ICH_VMCR_EL2 */
    str     x11, [x9, #8 * 36]
    str     x11, [sp, #HYP_CUR_VMCR]
    ldr     x13, [sp, #HYP_VGIC_N_APR]
    cbz     x13, 270f
    mrs     x11, s3_4_c12_c8_0
    mrs     x12, s3_4_c12_c9_0
    str     x11, [x9, #8 * 40]
    str     x12, [x9, #8 * 44]
    str     x11, [sp, #(HYP_CUR_AP0R + 8 * 0)]
    str     x12, [sp, #(HYP_CUR_AP1R + 8 * 0)]
    cmp     x13, #2
    b.lo    270f
    mrs     x11, s3_4_c12_c8_1
    mrs     x12, s3_4_c12_c9_1
    str     x11, [x9, #8 * 41]
    str     x12, [x9, #8 * 45]
    str     x11, [sp, #(HYP_CUR_AP0R + 8 * 1)]
    str     x12, [sp, #(HYP_CUR_AP1R + 8 * 1)]
    cmp     x13, #4
    b.lo    270f
    mrs     x11, s3_4_c12_c8_2
    mrs     x12, s3_4_c12_c9_2
    str     x11, [x9, #8 * 42]
    str     x12, [x9, #8 * 46]
    str     x11, [sp, #(HYP_CUR_AP0R + 8 * 2)]
    str     x12, [sp, #(HYP_CUR_AP1R + 8 * 2)]
    mrs     x11, s3_4_c12_c8_3
    mrs     x12, s3_4_c12_c9_3
    str     x11, [x9, #8 * 43]
    str     x12, [x9, #8 * 47]
    str     x11, [sp, #(HYP_CUR_AP0R + 8 * 3)]
    str     x12, [sp, #(HYP_CUR_AP1R + 8 * 3)]
270:
    ldr     x11, [x10, #8 * 36]     /* VGIC_VMCR */
    ldr     x9, [sp, #HYP_CUR_VMCR]
    cmp     x11, x9
    b.eq    29f
    msr     s3_4_c12_c11_7, x11
    str     x11, [sp, #HYP_CUR_VMCR]
29:
    ldr     x9, [sp, #HYP_VGIC_N_APR]
    cbz     x9, 3f
    vgic_load_apr 0, s3_4_c12_c8_0, s3_4_c12_c9_0
    cmp     x9, #2
    b.lo    3f
    vgic_load_apr 1, s3_4_c12_c8_1, s3_4_c12_c9_1
    cmp     x9, #4
    b.lo    3f
    vgic_load_apr 2, s3_4_c12_c8_2, s3_4_c12_c9_2
    vgic_load_apr 3, s3_4_c12_c8_3, s3_4_c12_c9_3
3:
    str     x2, [sp, #HYP_VGIC_OWNER]
27:
    ldr     x13, [x10, #8 * 35]     /* VGIC_HCR */
    cbnz    x13, 28f
    ldr     x9, [sp, #HYP_VGIC_LIVE]
    cbz     x9, 4f
    msr     s3_4_c12_c11_0, xzr     /* ICH_HCR_EL2 = 0 */
    str     xzr, [sp, #HYP_VGIC_LIVE]
    b       4f
28:
    mov     x9, #1
    str     x9, [sp, #HYP_VGIC_LIVE]
    ldr     x9, [sp, #HYP_VGIC_LRS]
    ldr     x14, [sp, #HYP_VGIC_LR_MASK]
    mov     x15, #0
    vgic_load_lr 0,  s3_4_c12_c12_0
    vgic_load_lr 1,  s3_4_c12_c12_1
    vgic_load_lr 2,  s3_4_c12_c12_2
    vgic_load_lr 3,  s3_4_c12_c12_3
    vgic_load_lr 4,  s3_4_c12_c12_4
    vgic_load_lr 5,  s3_4_c12_c12_5
    vgic_load_lr 6,  s3_4_c12_c12_6
    vgic_load_lr 7,  s3_4_c12_c12_7
    vgic_load_lr 8,  s3_4_c12_c13_0
    vgic_load_lr 9,  s3_4_c12_c13_1
    vgic_load_lr 10, s3_4_c12_c13_2
    vgic_load_lr 11, s3_4_c12_c13_3
    vgic_load_lr 12, s3_4_c12_c13_4
    vgic_load_lr 13, s3_4_c12_c13_5
    vgic_load_lr 14, s3_4_c12_c13_6
    vgic_load_lr 15, s3_4_c12_c13_7
30:
    str     x15, [sp, #HYP_VGIC_LR_MASK]
    msr     s3_4_c12_c11_0, x13     /* ICH_HCR_EL2 */
4:
    isb

    /* Restore guest GPRs, SP_EL0, ELR_EL2, SPSR_EL2, TPIDR*_EL0 and enter guest. */
    mov     x30, x1                 /* x30 = regs_pa */
    ldp     x21, x22, [x30, #8 * 31] /* SP_EL0, ELR_EL2 */
    ldr     x23, [x30, #8 * 33]     /* SPSR_EL2 */
    msr     sp_el0, x21
    msr     elr_el2, x22
    msr     spsr_el2, x23
    ldp     x21, x22, [x30, #8 * 35] /* TPIDR_EL0, TPIDRRO_EL0 */
    msr     tpidr_el0, x21
    msr     tpidrro_el0, x22
    ldp     x0,  x1,  [x30, #16 * 0]
    ldp     x2,  x3,  [x30, #16 * 1]
    ldp     x4,  x5,  [x30, #16 * 2]
    ldp     x6,  x7,  [x30, #16 * 3]
    ldp     x8,  x9,  [x30, #16 * 4]
    ldp     x10, x11, [x30, #16 * 5]
    ldp     x12, x13, [x30, #16 * 6]
    ldp     x14, x15, [x30, #16 * 7]
    ldp     x16, x17, [x30, #16 * 8]
    ldp     x18, x19, [x30, #16 * 9]
    ldp     x20, x21, [x30, #16 * 10]
    ldp     x22, x23, [x30, #16 * 11]
    ldp     x24, x25, [x30, #16 * 12]
    ldp     x26, x27, [x30, #16 * 13]
    ldp     x28, x29, [x30, #16 * 14]
    ldr     x30, [x30, #8 * 30]
    eret
    dsb     nsh
    isb

/* ---- Guest exit -> Host EL1 ----------------------------------------------- */

fl4_hyp_guest_sync:
    ldr     x0, [sp, #HYP_REGS_PA]
    str     x1, [x0, #8]
    mrs     x1, tpidr_el2
    str     x1, [x0, #0]
    mov     x1, #HYP_KIND_SYNC

fl4_hyp_guest_exit_common:
    /* x0 = regs_pa (x0, x1 already stored), x1 = kind. */
    stp     x2,  x3,  [x0, #16 * 1]
    stp     x4,  x5,  [x0, #16 * 2]
    stp     x6,  x7,  [x0, #16 * 3]
    stp     x8,  x9,  [x0, #16 * 4]
    stp     x10, x11, [x0, #16 * 5]
    stp     x12, x13, [x0, #16 * 6]
    stp     x14, x15, [x0, #16 * 7]
    stp     x16, x17, [x0, #16 * 8]
    stp     x18, x19, [x0, #16 * 9]
    stp     x20, x21, [x0, #16 * 10]
    stp     x22, x23, [x0, #16 * 11]
    stp     x24, x25, [x0, #16 * 12]
    stp     x26, x27, [x0, #16 * 13]
    stp     x28, x29, [x0, #16 * 14]
    mrs     x21, sp_el0
    stp     x30, x21, [x0, #8 * 30] /* X30, SP_EL0 */
    mrs     x22, elr_el2
    mrs     x23, spsr_el2
    stp     x22, x23, [x0, #8 * 32] /* ELR, SPSR */
    mrs     x21, tpidr_el0
    mrs     x22, tpidrro_el0
    stp     x21, x22, [x0, #8 * 35] /* TPIDR_EL0, TPIDRRO_EL0 */

    /* Capture exit syndrome into x19..x22. */
    mov     x19, x1                 /* kind */
    mrs     x20, esr_el2
    mrs     x21, far_el2
    mrs     x22, hpfar_el2

    /* Save guest EL1 sysregs, timer, and VGICv3 into vcpu_pa + 0x40. */
    ldr     x10, [sp, #HYP_VCPU_PA]
    add     x10, x10, #0x40
    mrs     x11, sctlr_el1
    mrs     x12, cpacr_el1
    stp     x11, x12, [x10, #8 * 0]
    mrs     x11, tcr_el1
    mrs     x12, ttbr0_el1
    stp     x11, x12, [x10, #8 * 2]
    mrs     x11, ttbr1_el1
    mrs     x12, mair_el1
    stp     x11, x12, [x10, #8 * 4]
    mrs     x11, amair_el1
    mrs     x12, contextidr_el1
    stp     x11, x12, [x10, #8 * 6]
    mrs     x11, afsr0_el1
    mrs     x12, afsr1_el1
    stp     x11, x12, [x10, #8 * 8]
    mrs     x11, esr_el1
    mrs     x12, far_el1
    stp     x11, x12, [x10, #8 * 10]
    mrs     x11, par_el1
    mrs     x12, vbar_el1
    stp     x11, x12, [x10, #8 * 12]
    mrs     x11, tpidr_el1
    str     x11, [x10, #8 * 14]     /* VMPIDR_EL2 is guest-RO: skip */
    mrs     x11, sp_el1
    mrs     x12, elr_el1
    stp     x11, x12, [x10, #8 * 16]
    mrs     x11, spsr_el1
    mrs     x12, csselr_el1
    stp     x11, x12, [x10, #8 * 18]
    str     x12, [sp, #HYP_CUR_CSSELR]

    ldr     x9, [sp, #HYP_GUEST_RAS_NZ]
    cbz     x9, 5f
    mrs     x11, s3_4_c12_c1_1      /* VDISR_EL2 */
    mrs     x12, s3_4_c5_c2_3       /* VSESR_EL2 */
    str     x11, [x10, #8 * 20]
    str     x12, [x10, #8 * 27]
5:
    mrs     x11, cntv_ctl_el0
    mrs     x12, cntv_cval_el0
    stp     x11, x12, [x10, #8 * 21]
    stp     x11, x12, [sp, #HYP_CUR_CNTV_CTL]
    mrs     x12, cntkctl_el1        /* CNTVOFF_EL2, VPIDR_EL2, ACTLR_EL1 are guest-RO/trapped */
    str     x12, [x10, #8 * 24]
    mrs     x11, mdscr_el1
    str     x11, [x10, #8 * 29]
    str     x11, [sp, #HYP_CUR_MDSCR]
    ldr     x9, [sp, #HYP_GUEST_MDCCINT_NZ]
    cbz     x9, 50f
    mrs     x12, s2_0_c0_c2_0       /* MDCCINT_EL1 */
    str     x12, [x10, #8 * 30]
    msr     s2_0_c0_c2_0, xzr       /* restore host MDCCINT_EL1 = 0 */
50:

    /* Stage-2 permission fault (not S1PTW): resolve VA->IPA via AT S1E1R
     * while guest Stage-1/2 are still live in hardware (guest PAR_EL1 is
     * already saved above). */
    cbnz    x19, 6f                 /* only KIND_SYNC */
    lsr     x9, x20, #26
    cmp     x9, #0x20               /* EC_IABT_LOW */
    b.eq    51f
    cmp     x9, #0x24               /* EC_DABT_LOW */
    b.ne    6f
51: and     x9, x20, #0x3c
    cmp     x9, #0x0c               /* Permission fault */
    b.ne    6f
    tbnz    x20, #7, 6f             /* S1PTW */
    at      s1e1r, x21
    isb
    mrs     x9, par_el1
    tbnz    x9, #0, 52f             /* Translation failed -> retry */
    lsr     x9, x9, #8
    ldr     x11, =0x00000ffffffffff0
    and     x22, x9, x11
    b       6f
52: mov     x19, #HYP_KIND_RETRY
6:
    /* Sparse / lazy GICv3 ICH_* save (VMCR/MISR/EISR/AP*R stay lazily owned). */
    ldr     x9, [sp, #HYP_GIC_V3]
    cbz     x9, 8f
    ldr     x9, [sp, #HYP_VGIC_LIVE]
    cbz     x9, 8f
    mrs     x11, s3_4_c12_c11_0     /* ICH_HCR_EL2 */
    str     x11, [x10, #8 * 35]
    mrs     x12, s3_4_c12_c11_5     /* ICH_ELRSR_EL2 */
    str     x12, [x10, #8 * 39]
    ldr     x14, [sp, #HYP_VGIC_LR_MASK]
    cbz     x14, 70f
    vgic_save_lr 0,  s3_4_c12_c12_0
    vgic_save_lr 1,  s3_4_c12_c12_1
    vgic_save_lr 2,  s3_4_c12_c12_2
    vgic_save_lr 3,  s3_4_c12_c12_3
    vgic_save_lr 4,  s3_4_c12_c12_4
    vgic_save_lr 5,  s3_4_c12_c12_5
    vgic_save_lr 6,  s3_4_c12_c12_6
    vgic_save_lr 7,  s3_4_c12_c12_7
    vgic_save_lr 8,  s3_4_c12_c13_0
    vgic_save_lr 9,  s3_4_c12_c13_1
    vgic_save_lr 10, s3_4_c12_c13_2
    vgic_save_lr 11, s3_4_c12_c13_3
    vgic_save_lr 12, s3_4_c12_c13_4
    vgic_save_lr 13, s3_4_c12_c13_5
    vgic_save_lr 14, s3_4_c12_c13_6
    vgic_save_lr 15, s3_4_c12_c13_7
70:
    /* Capture live ICH_MISR_EL2 and ICH_EISR_EL2 before clearing/modifying ICH_HCR_EL2. */
    mrs     x11, s3_4_c12_c11_2     /* ICH_MISR_EL2 */
    mrs     x12, s3_4_c12_c11_3     /* ICH_EISR_EL2 */
    stp     x11, x12, [x10, #8 * 37]
    /* On IRQ exit, keep En and maintenance IE bits [7:0] live so level-triggered
     * PPI 25 stays asserted until EL1 acks it in take_irq(), but ALWAYS clear
     * trap bits (TC/TALL0/TALL1/TSEI/TDIR) which otherwise trap EL1's own
     * ICC_IAR1_EL1 access even with HCR_EL2.IMO == 0. */
    cmp     x19, #HYP_KIND_IRQ
    b.ne    71f
    ldr     x11, [x10, #8 * 35]     /* saved ICH_HCR_EL2 */
    and     x11, x11, #0xff
    msr     s3_4_c12_c11_0, x11
    b       8f
71: msr     s3_4_c12_c11_0, xzr
    str     xzr, [sp, #HYP_VGIC_LIVE]
8:
    /* Quiesce guest CNTV_CTL_EL0 only when NOT an IRQ exit (level-triggered
     * PPI 27 must stay asserted until EL1 acks it in take_irq). */
    cmp     x19, #HYP_KIND_IRQ
    b.eq    9f
    ldr     x11, [x10, #8 * 21]     /* saved CNTV_CTL */
    cbz     x11, 9f
    msr     cntv_ctl_el0, xzr
    str     xzr, [sp, #HYP_CUR_CNTV_CTL]
9:
    ldr     x9, [sp, #HYP_GUEST_CNTVOFF_NZ]
    cbz     x9, 91f
    msr     cntvoff_el2, xzr
91:
    str     xzr, [sp, #HYP_IN_GUEST]

    /* Sync hardware auto-clear of HCR_EL2.VSE (bit 8) when vSError was delivered. */
    ldr     x11, [x10, #8 * 26]     /* cached guest HCR_EL2 */
    tbz     x11, #8, 95f            /* fast path: VSE not armed */
    mrs     x9, hcr_el2
    tbnz    x9, #8, 95f             /* VSE still pending (masked in guest) */
    bic     x11, x11, #(1 << 8)     /* hardware delivered vSError -> clear VSE */
    str     x11, [x10, #8 * 26]
95:
    /* Restore host EL2 controls and host EL1/EL2 registers.
     * CPTR_EL2 is kept as-is and restored lazily on host EC == 0x07 trap. */
    ldr     x9, [sp, #HYP_HOST_HCR]
    msr     hcr_el2, x9
    ldr     x9, [sp, #HYP_HOST_MDCR]
    msr     mdcr_el2, x9

    ldp     x9, x10, [sp, #HYP_HOST_SCTLR]
    msr     sctlr_el1, x9
    msr     tcr_el1, x10
    ldp     x9, x10, [sp, #HYP_HOST_TTBR1]
    msr     ttbr1_el1, x9
    msr     mair_el1, x10
    ldp     x9, x10, [sp, #HYP_HOST_VBAR]
    msr     vbar_el1, x9
    msr     tpidr_el1, x10
    ldp     x9, x10, [sp, #HYP_HOST_CNTKCTL]
    msr     cntkctl_el1, x9
    ldr     x9, [sp, #HYP_CUR_MDSCR]
    cmp     x10, x9
    b.eq    94f
    msr     mdscr_el1, x10
    str     x10, [sp, #HYP_CUR_MDSCR]
94:
    ldp     x9, x10, [sp, #HYP_HOST_TTBR0]
    msr     ttbr0_el1, x9
    msr     cpacr_el1, x10
    ldr     x9, [sp, #HYP_HOST_SP_EL1]
    msr     sp_el1, x9
    ldr     x9, [sp, #HYP_CUR_ACTLR]
    ldr     x10, [sp, #HYP_HOST_ACTLR]
    cmp     x9, x10
    b.eq    92f
    msr     actlr_el1, x10
    str     x10, [sp, #HYP_CUR_ACTLR]
92:
    ldp     x9, x10, [sp, #HYP_HOST_ELR]
    msr     elr_el2, x9
    msr     spsr_el2, x10

    /* Return (kind, esr, far, hpfar) in (x0, x1, x2, x3) to EL1. */
    mov     x0, x19
    mov     x1, x20
    mov     x2, x21
    mov     x3, x22
    isb
    eret
    dsb     nsh
    isb

.ltorg
