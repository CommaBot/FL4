/* FL4 AArch64 exception vectors and the way back to user code.
 *
 * While a thread runs at EL0, SP_EL1 points at the register array of its
 * TCB (fl4_core::layout::tcb::REGS, in the order of layout::reg), so an
 * exception from EL0 saves straight into it, then switches to the core's
 * kernel stack (PerCpu offset 0, through TPIDR_EL1) and calls
 * fl4_entry(kind, esr, far). The kernel runs with every exception masked;
 * only the idle loop takes interrupts at EL1. */

.equ KIND_SYNC,   0
.equ KIND_IRQ,    1
.equ KIND_SERROR, 2

.macro ventry label
    .balign 128
    b       \label
.endm

.section .text.vectors, "ax"
.balign 2048
.global fl4_vectors
fl4_vectors:
    ventry  fl4_vec_invalid         /* EL1t sync */
    ventry  fl4_vec_invalid         /* EL1t IRQ */
    ventry  fl4_vec_invalid         /* EL1t FIQ */
    ventry  fl4_vec_invalid         /* EL1t SError */
    ventry  fl4_kernel_sync         /* EL1h sync */
    ventry  fl4_kernel_irq_entry    /* EL1h IRQ: the idle loop */
    ventry  fl4_vec_invalid         /* EL1h FIQ */
    ventry  fl4_kernel_serror       /* EL1h SError */
    ventry  fl4_user_sync           /* EL0 AArch64 sync */
    ventry  fl4_user_irq            /* EL0 AArch64 IRQ */
    ventry  fl4_vec_invalid         /* EL0 AArch64 FIQ */
    ventry  fl4_user_serror         /* EL0 AArch64 SError */
    ventry  fl4_vec_invalid         /* EL0 AArch32 */
    ventry  fl4_vec_invalid
    ventry  fl4_vec_invalid
    ventry  fl4_vec_invalid

.balign 2048
.global fl4_vectors_el2
fl4_vectors_el2:
    ventry  fl4_vec_invalid         /* EL2t sync */
    ventry  fl4_vec_invalid         /* EL2t IRQ */
    ventry  fl4_vec_invalid         /* EL2t FIQ */
    ventry  fl4_vec_invalid         /* EL2t SError */
    ventry  fl4_kernel_sync         /* EL2h sync */
    ventry  fl4_kernel_irq_entry_el2 /* EL2h IRQ: the idle loop */
    ventry  fl4_vec_invalid         /* EL2h FIQ */
    ventry  fl4_kernel_serror       /* EL2h SError */
    ventry  fl4_user_sync_el2       /* Lower EL AArch64 sync */
    ventry  fl4_user_irq_el2        /* Lower EL AArch64 IRQ */
    ventry  fl4_vec_invalid         /* Lower EL AArch64 FIQ */
    ventry  fl4_user_serror_el2     /* Lower EL AArch64 SError */
    ventry  fl4_vec_invalid         /* Lower EL AArch32 */
    ventry  fl4_vec_invalid
    ventry  fl4_vec_invalid
    ventry  fl4_vec_invalid

.macro user_entry kind, tpidr
    stp     x0,  x1,  [sp, #16 * 0]
    stp     x2,  x3,  [sp, #16 * 1]
    stp     x4,  x5,  [sp, #16 * 2]
    stp     x6,  x7,  [sp, #16 * 3]
    stp     x8,  x9,  [sp, #16 * 4]
    stp     x10, x11, [sp, #16 * 5]
    stp     x12, x13, [sp, #16 * 6]
    stp     x14, x15, [sp, #16 * 7]
    stp     x16, x17, [sp, #16 * 8]
    stp     x18, x19, [sp, #16 * 9]
    stp     x20, x21, [sp, #16 * 10]
    stp     x22, x23, [sp, #16 * 11]
    stp     x24, x25, [sp, #16 * 12]
    stp     x26, x27, [sp, #16 * 13]
    stp     x28, x29, [sp, #16 * 14]
    mrs     x21, sp_el0
    stp     x30, x21, [sp, #8 * 30]     /* X30, SP_EL0 */
    mrs     x22, elr_el1
    mrs     x23, spsr_el1
    stp     x22, x23, [sp, #8 * 32]     /* ELR_EL1/EL2, SPSR_EL1/EL2 */
    mrs     x21, tpidr_el0
    str     x21, [sp, #8 * 35]          /* TPIDR_EL0 */
    mrs     x0, \tpidr
    ldr     x1, [x0]
    mov     sp, x1
    mov     x0, #\kind
    mrs     x1, esr_el1
    mrs     x2, far_el1
    bl      fl4_entry
    b       fl4_vec_invalid
.endm

.section .text
fl4_user_sync:
    user_entry KIND_SYNC, tpidr_el1

fl4_user_irq:
    user_entry KIND_IRQ, tpidr_el1

fl4_user_serror:
    user_entry KIND_SERROR, tpidr_el1

fl4_user_sync_el2:
    user_entry KIND_SYNC, tpidr_el2

fl4_user_irq_el2:
    user_entry KIND_IRQ, tpidr_el2

fl4_user_serror_el2:
    user_entry KIND_SERROR, tpidr_el2

/* An interrupt while the core idles: the idle loop keeps no state. */
fl4_kernel_irq_entry:
    mrs     x0, tpidr_el1
    ldr     x1, [x0]
    mov     sp, x1
    bl      fl4_kernel_irq
    b       fl4_vec_invalid

fl4_kernel_irq_entry_el2:
    mrs     x0, tpidr_el2
    ldr     x1, [x0]
    mov     sp, x1
    bl      fl4_kernel_irq
    b       fl4_vec_invalid

fl4_kernel_sync:
    sub     sp, sp, #32
    stp     x29, x30, [sp]
    mrs     x0, esr_el1
    mrs     x1, far_el1
    mrs     x2, elr_el1
    add     x3, sp, #32
    bl      fl4_kernel_fault
    b       fl4_vec_invalid

fl4_kernel_serror:
    mrs     x0, esr_el1
    mov     x1, #0
    mrs     x2, elr_el1
    mov     x3, sp
    bl      fl4_kernel_fault
    b       fl4_vec_invalid

fl4_vec_invalid:
    msr     daifset, #0xf
1:  wfi
    b       1b

/* fl4_restore_user(regs): run the thread whose register array is at x0. */
.global fl4_restore_user
fl4_restore_user:
    mov     sp, x0
    ldp     x21, x22, [sp, #8 * 31]     /* SP_EL0, ELR_EL1 */
    ldr     x23, [sp, #8 * 33]          /* SPSR_EL1 */
    msr     sp_el0, x21
    msr     elr_el1, x22
    msr     spsr_el1, x23
    ldp     x21, x22, [sp, #8 * 35]     /* TPIDR_EL0, TPIDRRO_EL0 */
    msr     tpidr_el0, x21
    msr     tpidrro_el0, x22
    ldp     x0,  x1,  [sp, #16 * 0]
    ldp     x2,  x3,  [sp, #16 * 1]
    ldp     x4,  x5,  [sp, #16 * 2]
    ldp     x6,  x7,  [sp, #16 * 3]
    ldp     x8,  x9,  [sp, #16 * 4]
    ldp     x10, x11, [sp, #16 * 5]
    ldp     x12, x13, [sp, #16 * 6]
    ldp     x14, x15, [sp, #16 * 7]
    ldp     x16, x17, [sp, #16 * 8]
    ldp     x18, x19, [sp, #16 * 9]
    ldp     x20, x21, [sp, #16 * 10]
    ldp     x22, x23, [sp, #16 * 11]
    ldp     x24, x25, [sp, #16 * 12]
    ldp     x26, x27, [sp, #16 * 13]
    ldp     x28, x29, [sp, #16 * 14]
    ldr     x30, [sp, #8 * 30]
    eret
    /* No speculation past the exception return. */
    dsb     nsh
    isb

/* fl4_idle(stack_top): wait for interrupts on the core's stack. */
.global fl4_idle
fl4_idle:
    mov     sp, x0
    msr     daifclr, #2
1:  wfi
    b       1b
