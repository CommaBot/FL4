/* fl4_sysret_check regs, scratch, iret: fall through if the thread whose
 * register array (fl4_core::layout::reg order) is at \regs may leave by
 * SYSRET, else jump to \iret. Clobbers \scratch and the flags.
 *
 * SYSRET loads RIP from rcx and RFLAGS from r11, so it returns the
 * thread's registers only as SYSCALL left them: Error = -1 (a context
 * SYSCALL saved; the API clears it when it changes another thread's
 * registers, but not a fault reply's or the thread's own copy), RCX =
 * NextIP and R11 = FLAGS. NextIP must be in the canonical lower half:
 * SYSRET to a non-canonical address faults in ring 0 on Intel, after the
 * user's RSP is loaded. And FLAGS must have neither RF, which SYSRET
 * cannot set, nor TF, which SYSRET sets with a trap before the first user
 * instruction, where IRET traps after it (as Linux, which uses IRET for
 * both). Everything else leaves by IRET. Host-tested by
 * fl4-arch-x86_64/tests/kernel_sysret.rs. */
.macro fl4_sysret_check regs, scratch, iret
    cmpq $-1, 15*8(\regs)
    jne \iret
    movq 14*8(\regs), \scratch
    cmpq 19*8(\regs), \scratch
    jne \iret
    shrq $47, \scratch
    jnz \iret
    movq 13*8(\regs), \scratch
    cmpq 18*8(\regs), \scratch
    jne \iret
    testq $0x10100, \scratch
    jnz \iret
.endm
