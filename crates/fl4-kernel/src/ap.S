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

/* An Intel TDX AP has no INIT or SIPI. Firmware parks it, and on the ACPI
 * wakeup mailbox's command jumps here in 64-bit mode on firmware's identity
 * map, with interrupts off, in four- or five-level paging (firmware uses
 * five levels for a 52-bit GPA width). The boot core copies this code to a
 * page of loader code (executable in firmware's tables) that its boot table
 * also identity maps, and fills in the data. It is position independent,
 * and writes nothing to its own page, which firmware may map read-only.
 * Nothing here may take #VE: no IDT is loaded yet.
 *
 * The VMM decides which vCPU runs this, and how often. On the boot table,
 * before it touches a kernel stack, each vCPU takes its core index once
 * (FL4_TDX_AP_CLAIMED), and none may once the boot core is done
 * (FL4_TDX_AP_CLOSED): any other ends the guest (.Ltdx_ap_reject). The
 * kernel's statics are named by absolute address, as this code runs from
 * the copy in the wakeup page. */
    .align 16
    .global fl4_tdx_ap_trampoline
fl4_tdx_ap_trampoline:
    .code64
    cli
    cld
    leaq fl4_tdx_ap_trampoline(%rip), %rbx /* below 4 GiB */
    movl $0xC0000080, %ecx                /* EFER: the boot core's NXE */
    rdmsr
    movl %eax, %esi
    orl tdx_ap_efer(%rip), %esi
    cmpl %eax, %esi
    je 1f
    movl %esi, %eax
    wrmsr
1:
    movq %cr0, %rax
    orq $(1 << 16), %rax                  /* WP */
    movq %rax, %cr0
    lgdtq tdx_ap_gdt_ptr(%rip)
    /* Before any new CR3: PGE and PCIDE off drop firmware's global and PCID
     * TLB entries, and PCIDE and CET must be off to clear CR0.PG below. */
    movq %cr4, %rax
    andq $~((1 << 7) | (1 << 17) | (1 << 23)), %rax
    movq %rax, %cr4
    btq $12, %rax                         /* LA57 */
    jc 3f
    movq tdx_ap_cr3(%rip), %rax
    movq %rax, %cr3
    jmp .Ltdx_ap_tables
3:
    /* LA57 changes only with paging off, from a 32-bit code segment. */
    ljmpl *tdx_ap_to_compat(%rip)
    .code32
    .global fl4_tdx_ap_compat
fl4_tdx_ap_compat:
    movl $0x18, %eax
    movl %eax, %ds
    movl %eax, %es
    movl %eax, %ss
    movl %cr0, %eax
    andl $0x7fffffff, %eax
    movl %eax, %cr0
    movl %cr4, %eax
    andl $~(1 << 12), %eax
    movl %eax, %cr4
    movl (tdx_ap_cr3 - fl4_tdx_ap_trampoline)(%ebx), %eax
    movl %eax, %cr3
    movl %cr0, %eax
    orl $0x80000000, %eax
    movl %eax, %cr0
    ljmpl *(tdx_ap_to_long - fl4_tdx_ap_trampoline)(%ebx)
    .code64
    .global fl4_tdx_ap_long
fl4_tdx_ap_long:
.Ltdx_ap_tables:
    /* The kernel image is mapped (writable .bss) from here on, the wakeup
     * page perhaps still read-only. No more vCPUs once the cores are up. */
    movabsq $FL4_TDX_AP_CLOSED, %rax
    cmpb $0, (%rax)
    jne .Ltdx_ap_reject
    /* The core index: an AP's (1..63), and not yet taken. */
    movq tdx_ap_cpu(%rip), %r12
    testq %r12, %r12
    jz .Ltdx_ap_reject
    cmpq $64, %r12
    jae .Ltdx_ap_reject
    movabsq $FL4_TDX_AP_CLAIMED, %rax
    lock btsq %r12, (%rax)
    jc .Ltdx_ap_reject
    movq tdx_ap_stack(%rip), %rsp
    /* The kernel image's GDT, as on the boot core and SNP APs: this page
     * leaves the address space when fl4_ap_main loads the kernel's tables,
     * and an exception before gdt::init_core still reads the GDT. */
    movabsq $fl4_efi_gdt, %rax
    pushq %rax
    pushq $0
    movw $31, 6(%rsp)
    lgdt 6(%rsp)
    addq $16, %rsp
    leaq 2f(%rip), %rax
    pushq $0x10
    pushq %rax
    lretq
2:
    movl $0x18, %eax
    movl %eax, %ds
    movl %eax, %es
    movl %eax, %ss
    xorl %eax, %eax
    movl %eax, %fs
    movl %eax, %gs
    subq $8, %rsp                         /* SysV call alignment */
    movq %r12, %rdi                       /* the index this vCPU took */
    movq tdx_ap_entry(%rip), %rax
    jmp *%rax

    /* A vCPU the kernel did not ask for, or a second one for an index: no
     * stack and no IDT, so poison the guest for the boot core (which stops
     * at the sight of it), report a fatal error to the VMM with
     * TDG.VP.VMCALL<ReportFatalError> (no #VE), and spin. */
.Ltdx_ap_reject:
    cli
    movabsq $FL4_CVM_POISONED, %rax
    movb $1, (%rax)
    xorl %eax, %eax                       /* TDG.VP.VMCALL */
    movl $((1 << 10) | (1 << 11) | (1 << 12) | (1 << 13)), %ecx
    xorl %r10d, %r10d
    movl $0x10003, %r11d                  /* ReportFatalError */
    movl $11, %r12d                       /* the kernel's AP reason */
    xorl %r13d, %r13d
    .byte 0x66, 0x0f, 0x01, 0xcc          /* TDCALL */
1:
    pause
    jmp 1b

    .align 8
    .global fl4_tdx_ap_gdt
fl4_tdx_ap_gdt:                             /* accessed bits set: read-only */
    .quad 0
    .quad 0x00cf9b000000ffff                /* 0x08 code, 32-bit */
    .quad 0x00af9b000000ffff                /* 0x10 code, 64-bit */
    .quad 0x00cf93000000ffff                /* 0x18 data */
    .align 8
    .global fl4_tdx_ap_data
fl4_tdx_ap_data:
tdx_ap_cr3:   .quad 0
tdx_ap_efer:  .quad 0
tdx_ap_stack: .quad 0
tdx_ap_entry: .quad 0
tdx_ap_cpu:   .quad 0
tdx_ap_to_compat:                           /* far pointers: offset, selector */
    .long 0
    .short 0x08, 0
tdx_ap_to_long:
    .long 0
    .short 0x10, 0
tdx_ap_gdt_ptr:
    .short 4 * 8 - 1
    .quad 0                                 /* the GDT's address in the page */
    .global fl4_tdx_ap_trampoline_end
fl4_tdx_ap_trampoline_end:

    .text
