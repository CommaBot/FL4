/* Application-processor start-up code. The boot core copies everything from
 * fl4_ap_trampoline to fl4_ap_trampoline_end to physical AP_BASE (0x8000),
 * fills in the data words at the end, and sends INIT-SIPI-SIPI with vector
 * AP_BASE >> 12. The AP starts here in 16-bit real mode, goes through
 * 32-bit protected mode into long mode on the page table in ap_cr3 (the
 * kernel's, plus an identity map of low memory), and jumps to ap_entry
 * with the core index in RDI and RSP = ap_stack. */

    .set AP_BASE, 0x8000

    .section .rodata
    .align 16
    .global fl4_ap_trampoline
fl4_ap_trampoline:
    .code16
    cli
    cld
    xorw %ax, %ax
    movw %ax, %ds
    lgdtl (ap_gdt_ptr - fl4_ap_trampoline + AP_BASE)
    movl %cr0, %eax
    orl $1, %eax
    movl %eax, %cr0
    ljmpl $0x08, $((ap_pm32 - fl4_ap_trampoline + AP_BASE))

    .code32
ap_pm32:
    movw $0x10, %ax
    movw %ax, %ds
    movw %ax, %es
    movw %ax, %ss
    movl %cr4, %eax
    orl $((1 << 5) | (1 << 7)), %eax      /* PAE, PGE */
    movl %eax, %cr4
    movl (ap_cr3 - fl4_ap_trampoline + AP_BASE), %eax
    movl %eax, %cr3
    movl $0xC0000080, %ecx                /* EFER: LME and the boot core's NXE */
    rdmsr
    orl (ap_efer - fl4_ap_trampoline + AP_BASE), %eax
    wrmsr
    movl %cr0, %eax
    orl $((1 << 31) | (1 << 16)), %eax    /* PG, WP */
    movl %eax, %cr0
    ljmpl $0x18, $((ap_lm64 - fl4_ap_trampoline + AP_BASE))

    .code64
ap_lm64:
    movq (ap_stack - fl4_ap_trampoline + AP_BASE), %rsp
    movq (ap_cpu - fl4_ap_trampoline + AP_BASE), %rdi
    movq (ap_entry - fl4_ap_trampoline + AP_BASE), %rax
    jmp *%rax

    .align 16
ap_gdt:
    .quad 0
    .quad 0x00cf9a000000ffff                /* 0x08 code, 32-bit */
    .quad 0x00cf92000000ffff                /* 0x10 data */
    .quad 0x00af9a000000ffff                /* 0x18 code, 64-bit */
ap_gdt_ptr:
    .short 4 * 8 - 1
    .long (ap_gdt - fl4_ap_trampoline + AP_BASE)

    .align 8
    .global fl4_ap_data
fl4_ap_data:
ap_cr3:   .quad 0
ap_efer:  .quad 0
ap_stack: .quad 0
ap_entry: .quad 0
ap_cpu:   .quad 0
    .global fl4_ap_trampoline_end
fl4_ap_trampoline_end:

    .text
