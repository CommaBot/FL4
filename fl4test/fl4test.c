/*
 * fl4test (DESIGN.md §12): FL4's extensions and the l4h fixes FL4 takes,
 * on sel4test's framework. `cargo xtask fl4test` links this file into the
 * sel4test workspace and runs the tests whose names start with FL4; plain
 * sel4test runs leave them out.
 */
#include <stdio.h>
#include <string.h>
#include <sel4/sel4.h>
#include <vka/object.h>
#include <vka/capops.h>
#include <vspace/vspace.h>
#include <sel4test/testutil.h>
#include <sel4test/macros.h>

#include "../helpers.h"

static uint64_t rdtsc(void)
{
    return __builtin_ia32_rdtsc();
}

/* ---- l4h 0001: seL4_TCBFlag_trapSyscalls ---------------------------- */

static int yield_once(seL4_Word a, seL4_Word b, seL4_Word c, seL4_Word d)
{
    seL4_Yield();
    return 0;
}

/* A thread with trapSyscalls set makes no seL4 calls: its syscall
 * instruction reaches its fault handler as an UnknownSyscall fault that
 * names the syscall. */
static int test_trap_syscalls(env_t env)
{
    helper_thread_t t;
    vka_object_t reply;
    test_error_eq(vka_alloc_reply(&env->vka, &reply), 0);
    seL4_CPtr fault_ep = vka_alloc_endpoint_leaky(&env->vka);
    create_helper_thread(env, &t);
    int error = api_tcb_set_space(get_helper_tcb(&t), fault_ep, env->cspace_root,
                                  api_make_guard_skip_word(seL4_WordBits - env->cspace_size_bits),
                                  env->page_directory, seL4_NilData);
    test_error_eq(error, seL4_NoError);
    seL4_TCB_SetFlags_t f = seL4_TCB_SetFlags(get_helper_tcb(&t), 0, seL4_TCBFlag_trapSyscalls);
    test_error_eq(f.error, seL4_NoError);
    test_check(f.flags & seL4_TCBFlag_trapSyscalls);
    start_helper(env, &t, yield_once, 0, 0, 0, 0);
    seL4_Word badge;
    seL4_MessageInfo_t tag = api_recv(fault_ep, &badge, reply.cptr);
    test_eq(seL4_MessageInfo_get_label(tag), (seL4_Word) seL4_Fault_UnknownSyscall);
    test_eq((seL4_Word) seL4_GetMR(seL4_UnknownSyscall_Syscall), (seL4_Word) seL4_SysYield);
    cleanup_helper(env, &t);
    return sel4test_get_result();
}
DEFINE_TEST(FL4TRAP0001, "trapSyscalls sends syscalls to the fault handler (l4h 0001)", test_trap_syscalls, true)

/* ---- l4h 0003, 0006: seL4_TCB_SetTimer ------------------------------ */

/* The timer signals its badge to the TCB's bound notification, not before
 * the deadline. */
static int test_tcb_timer(env_t env)
{
    seL4_CPtr ntfn = vka_alloc_notification_leaky(&env->vka);
    test_error_eq(seL4_TCB_BindNotification(env->tcb, ntfn), seL4_NoError);
    uint64_t deadline = rdtsc() + 2000000;
    test_error_eq(seL4_TCB_SetTimer(env->tcb, deadline, 0x42), seL4_NoError);
    seL4_Word badge = 0;
    seL4_Wait(ntfn, &badge);
    uint64_t now = rdtsc();
    test_eq(badge, (seL4_Word) 0x42);
    test_geq(now, deadline);
    test_error_eq(seL4_TCB_UnbindNotification(env->tcb), seL4_NoError);
    return sel4test_get_result();
}
DEFINE_TEST(FL4TIMER0001, "TCB_SetTimer signals the bound notification at the deadline (l4h 0003)", test_tcb_timer, true)

/* A deadline in the past fires at once; deadline 0 disarms. */
static int test_tcb_timer_past_and_disarm(env_t env)
{
    seL4_CPtr ntfn = vka_alloc_notification_leaky(&env->vka);
    test_error_eq(seL4_TCB_BindNotification(env->tcb, ntfn), seL4_NoError);
    test_error_eq(seL4_TCB_SetTimer(env->tcb, 1, 0x7), seL4_NoError);
    seL4_Word badge = 0;
    seL4_Wait(ntfn, &badge);
    test_eq(badge, (seL4_Word) 0x7);

    test_error_eq(seL4_TCB_SetTimer(env->tcb, rdtsc() + 1000000, 0x9), seL4_NoError);
    test_error_eq(seL4_TCB_SetTimer(env->tcb, 0, 0), seL4_NoError);
    uint64_t until = rdtsc() + 4000000;
    while (rdtsc() < until) {
    }
    badge = 0;
    seL4_Poll(ntfn, &badge);
    test_eq(badge, (seL4_Word) 0);
    test_error_eq(seL4_TCB_UnbindNotification(env->tcb), seL4_NoError);
    return sel4test_get_result();
}
DEFINE_TEST(FL4TIMER0002, "TCB_SetTimer: past deadlines fire at once, 0 disarms (l4h 0003)", test_tcb_timer_past_and_disarm, true)

/* ---- l4h 0002: seL4_TCB_ReadFPU and seL4_TCB_WriteFPU -------------- */

#define FPU_BYTES 4096

/* Map a fresh frame, returning its cap and address. */
static void *map_frame(env_t env, seL4_CPtr *cap)
{
    *cap = vka_alloc_frame_leaky(&env->vka, seL4_PageBits);
    if (!*cap) {
        return NULL;
    }
    return vspace_map_pages(&env->vspace, cap, NULL, seL4_AllRights, 1, seL4_PageBits, 1);
}

/* An image written to a thread reads back in the standard XSAVE layout,
 * with MXCSR's reserved bits cleared. */
static int test_fpu_read_write(env_t env)
{
    helper_thread_t t;
    create_helper_thread(env, &t);
    seL4_CPtr fcap;
    uint8_t *frame = map_frame(env, &fcap);
    test_assert(frame != NULL);
    test_error_eq(seL4_TCB_ReadFPU(get_helper_tcb(&t), fcap, 0), seL4_NoError);
    /* XMM0 is at byte 160 of the legacy area; MXCSR at 24. */
    for (int i = 0; i < 16; i++) {
        frame[160 + i] = 0xa0 + i;
    }
    uint32_t mxcsr = 0x1f80 | 0xffff0000u;
    memcpy(frame + 24, &mxcsr, 4);
    test_error_eq(seL4_TCB_WriteFPU(get_helper_tcb(&t), fcap, 0), seL4_NoError);
    memset(frame, 0, FPU_BYTES);
    test_error_eq(seL4_TCB_ReadFPU(get_helper_tcb(&t), fcap, 0), seL4_NoError);
    for (int i = 0; i < 16; i++) {
        test_eq((int) frame[160 + i], 0xa0 + i);
    }
    /* Bits outside the CPU's MXCSR_MASK are cleared. */
    memcpy(&mxcsr, frame + 24, 4);
    static uint8_t fx[512] __attribute__((aligned(16)));
    __asm__ volatile("fxsave64 %0" : "=m"(fx));
    uint32_t mask;
    memcpy(&mask, fx + 28, 4);
    if (mask == 0) {
        mask = 0xffbf;
    }
    test_eq(mxcsr & ~mask, 0u);
    test_eq(mxcsr & 0xffff, 0x1f80u);
    /* Misaligned offsets are refused. */
    test_neq(seL4_TCB_ReadFPU(get_helper_tcb(&t), fcap, 8), seL4_NoError);
    cleanup_helper(env, &t);
    return sel4test_get_result();
}
DEFINE_TEST(FL4FPU0001, "TCB_ReadFPU and TCB_WriteFPU round trip, sanitised (l4h 0002)", test_fpu_read_write, true)

/* MXCSR, which the thread's start-up code leaves alone. */
static int read_mxcsr(seL4_Word a, seL4_Word b, seL4_Word c, seL4_Word d)
{
    uint32_t v;
    __asm__ volatile("stmxcsr %0" : "=m"(v));
    return (int)(v & 0xffff);
}

/* A thread starts with the FPU state written to it. */
static int test_fpu_write_runs(env_t env)
{
    helper_thread_t t;
    create_helper_thread(env, &t);
    seL4_CPtr fcap;
    uint8_t *frame = map_frame(env, &fcap);
    test_assert(frame != NULL);
    test_error_eq(seL4_TCB_ReadFPU(get_helper_tcb(&t), fcap, 0), seL4_NoError);
    /* Flush-to-zero on: 0x9f80. */
    uint32_t mxcsr = 0x9f80;
    memcpy(frame + 24, &mxcsr, 4);
    /* XSTATE_BV: x87 and SSE state present. */
    uint64_t bv;
    memcpy(&bv, frame + 512, 8);
    bv |= 3;
    memcpy(frame + 512, &bv, 8);
    test_error_eq(seL4_TCB_WriteFPU(get_helper_tcb(&t), fcap, 0), seL4_NoError);
    start_helper(env, &t, read_mxcsr, 0, 0, 0, 0);
    test_eq(wait_for_helper(&t), 0x9f80);
    cleanup_helper(env, &t);
    return sel4test_get_result();
}
DEFINE_TEST(FL4FPU0002, "A thread runs with the FPU state written to it (l4h 0002)", test_fpu_write_runs, true)

/* ---- l4h 0009: seL4_X86_ExecuteNever; 0023: TestAndClearAccessed ----- */

/* Map `cap` at `vaddr` with `attr`, after vspace has made the page tables. */
static int remap(env_t env, seL4_CPtr cap, void *vaddr, seL4_Word attr)
{
    int err = seL4_X86_Page_Unmap(cap);
    if (err) {
        return err;
    }
    return seL4_X86_Page_Map(cap, env->page_directory, (seL4_Word) vaddr, seL4_AllRights, attr);
}

static int jump_to(seL4_Word target, seL4_Word b, seL4_Word c, seL4_Word d)
{
    ((void (*)(void)) target)();
    return 0;
}

/* Executing from a page mapped ExecuteNever faults as an instruction fetch. */
static int test_execute_never(env_t env)
{
    seL4_CPtr fcap;
    uint8_t *page = map_frame(env, &fcap);
    test_assert(page != NULL);
    page[0] = 0xc3; /* ret */
    test_error_eq(remap(env, fcap, page, seL4_X86_Default_VMAttributes | seL4_X86_ExecuteNever), seL4_NoError);

    helper_thread_t t;
    vka_object_t reply;
    test_error_eq(vka_alloc_reply(&env->vka, &reply), 0);
    seL4_CPtr fault_ep = vka_alloc_endpoint_leaky(&env->vka);
    create_helper_thread(env, &t);
    int error = api_tcb_set_space(get_helper_tcb(&t), fault_ep, env->cspace_root,
                                  api_make_guard_skip_word(seL4_WordBits - env->cspace_size_bits),
                                  env->page_directory, seL4_NilData);
    test_error_eq(error, seL4_NoError);
    start_helper(env, &t, jump_to, (seL4_Word) page, 0, 0, 0);
    seL4_Word badge;
    seL4_MessageInfo_t tag = api_recv(fault_ep, &badge, reply.cptr);
    test_eq(seL4_MessageInfo_get_label(tag), (seL4_Word) seL4_Fault_VMFault);
    test_eq(seL4_GetMR(seL4_VMFault_Addr), (seL4_Word) page);
    test_eq(seL4_GetMR(seL4_VMFault_PrefetchFault), (seL4_Word) 1);
    cleanup_helper(env, &t);
    return sel4test_get_result();
}
DEFINE_TEST(FL4VM0001, "ExecuteNever mappings fault on instruction fetch (l4h 0009)", test_execute_never, true)

/* TestAndClearAccessed reports and clears the accessed bit. */
static int test_accessed(env_t env)
{
    seL4_CPtr fcap;
    volatile uint8_t *page = map_frame(env, &fcap);
    test_assert(page != NULL);
    (void) page[0];
    seL4_X86_Page_TestAndClearAccessed_t r = seL4_X86_Page_TestAndClearAccessed(fcap);
    test_error_eq(r.error, seL4_NoError);
    test_eq(r.accessed, (seL4_Word) 1);
    r = seL4_X86_Page_TestAndClearAccessed(fcap);
    test_error_eq(r.error, seL4_NoError);
    test_eq(r.accessed, (seL4_Word) 0);
    /* The bit was cleared without a flush: drop the TLB entry, then touch. */
    test_error_eq(remap(env, fcap, (void *) page, seL4_X86_Default_VMAttributes), seL4_NoError);
    (void) page[1];
    r = seL4_X86_Page_TestAndClearAccessed(fcap);
    test_eq(r.accessed, (seL4_Word) 1);
    return sel4test_get_result();
}
DEFINE_TEST(FL4VM0002, "Page_TestAndClearAccessed (l4h 0023)", test_accessed, true)

/* ---- l4h 0029: Page_DeriveSubframe ------------------------------------ */

/* 4 KiB aliases of a 2 MiB frame see its contents. */
static int test_derive_subframe(env_t env)
{
    seL4_CPtr large = vka_alloc_frame_leaky(&env->vka, seL4_LargePageBits);
    if (!large) {
        return sel4test_get_result();
    }
    uint8_t *big = vspace_map_pages(&env->vspace, &large, NULL, seL4_AllRights, 1, seL4_LargePageBits, 1);
    test_assert(big != NULL);
    for (int i = 0; i < 4; i++) {
        big[0x3000 + i * 4096] = 0x50 + i;
    }
    /* The aliases go in a new 4-slot CNode, then move to our CSpace. */
    vka_object_t cn;
    test_error_eq(vka_alloc_cnode_object(&env->vka, 2, &cn), 0);
    int err = seL4_X86_Page_DeriveSubframe(large, env->cspace_root, cn.cptr, seL4_WordBits, 0, 0x3000, 4, seL4_AllRights);
    test_error_eq(err, seL4_NoError);
    seL4_CPtr subs[4];
    for (int i = 0; i < 4; i++) {
        subs[i] = get_free_slot(env);
        test_error_eq(seL4_CNode_Move(env->cspace_root, subs[i], seL4_WordBits, cn.cptr, i, 2), seL4_NoError);
    }
    for (int i = 0; i < 4; i++) {
        seL4_CPtr sub = subs[i];
        uint8_t *p = vspace_map_pages(&env->vspace, &sub, NULL, seL4_AllRights, 1, seL4_PageBits, 1);
        test_assert(p != NULL);
        test_eq((int) p[0], 0x50 + i);
        p[1] = 0x60 + i;
        test_eq((int) big[0x3001 + i * 4096], 0x60 + i);
    }
    /* Revoking the large frame removes its aliases. */
    test_error_eq(cnode_revoke(env, large), seL4_NoError);
    test_check(is_slot_empty(env, subs[0]));
    return sel4test_get_result();
}
DEFINE_TEST(FL4VM0003, "Page_DeriveSubframe aliases a 2 MiB frame (l4h 0029)", test_derive_subframe, true)

/* ---- l4h 0028: user selectors ---------------------------------------- */

static int test_user_selectors(env_t env)
{
    uint16_t cs, ss;
    __asm__ volatile("mov %%cs, %0" : "=r"(cs));
    __asm__ volatile("mov %%ss, %0" : "=r"(ss));
    test_eq((int) cs, 0x33);
    test_eq((int) ss, 0x2b);
    return sel4test_get_result();
}
DEFINE_TEST(FL4SEL0001, "User code runs with the Linux selectors (l4h 0028)", test_user_selectors, true)

/* ---- l4h 0017: seL4_X86_DeferFlush and seL4_X64_PML4_Flush ------------ */

static int write_byte(seL4_Word addr, seL4_Word b, seL4_Word c, seL4_Word d)
{
    *(volatile uint8_t *) addr = 1;
    return 0;
}

/* A remap that lowers rights with DeferFlush takes effect, on every core,
 * once the address space is flushed. */
static int test_defer_flush(env_t env)
{
    seL4_CPtr fcap;
    volatile uint8_t *page = map_frame(env, &fcap);
    test_assert(page != NULL);
    page[0] = 1;
    int err = seL4_X86_Page_Map(fcap, env->page_directory, (seL4_Word) page, seL4_CanRead,
                                seL4_X86_Default_VMAttributes | seL4_X86_DeferFlush);
    test_error_eq(err, seL4_NoError);
    test_error_eq(seL4_X64_PML4_Flush(env->page_directory), seL4_NoError);

    helper_thread_t t;
    vka_object_t reply;
    test_error_eq(vka_alloc_reply(&env->vka, &reply), 0);
    seL4_CPtr fault_ep = vka_alloc_endpoint_leaky(&env->vka);
    create_helper_thread(env, &t);
    err = api_tcb_set_space(get_helper_tcb(&t), fault_ep, env->cspace_root,
                            api_make_guard_skip_word(seL4_WordBits - env->cspace_size_bits),
                            env->page_directory, seL4_NilData);
    test_error_eq(err, seL4_NoError);
    start_helper(env, &t, write_byte, (seL4_Word) page, 0, 0, 0);
    seL4_Word badge;
    seL4_MessageInfo_t tag = api_recv(fault_ep, &badge, reply.cptr);
    test_eq(seL4_MessageInfo_get_label(tag), (seL4_Word) seL4_Fault_VMFault);
    test_eq(seL4_GetMR(seL4_VMFault_Addr), (seL4_Word) page);
    cleanup_helper(env, &t);
    return sel4test_get_result();
}
DEFINE_TEST(FL4VM0004, "DeferFlush remaps take effect after PML4_Flush (l4h 0017)", test_defer_flush, true)

/* ---- FL4: TCB_CopyRegisters stalls a running source ------------------- */

static int count_forever(seL4_Word counter, seL4_Word b, seL4_Word c, seL4_Word d)
{
    volatile seL4_Word *n = (volatile seL4_Word *) counter;
    while (1) {
        (*n)++;
    }
    return 0;
}

/* Copying from a thread running on another core with suspendSource stops
 * it at once (DESIGN.md §4, fixes found while building FL4). seL4 stalls
 * only the target, so the source runs on until that core next enters the
 * kernel. */
static int test_copy_registers_stalls_source(env_t env)
{
    if (env->cores < 2) {
        return sel4test_get_result();
    }
    helper_thread_t src, dst;
    volatile seL4_Word counter = 0;
    create_helper_thread(env, &src);
    create_helper_thread(env, &dst);
    set_helper_affinity(env, &src, 1);
    start_helper(env, &src, count_forever, (seL4_Word) &counter, 0, 0, 0);
    while (counter == 0) {
    }
    int err = seL4_TCB_CopyRegisters(get_helper_tcb(&dst), get_helper_tcb(&src), true, false, true, true, 0);
    test_error_eq(err, seL4_NoError);
    seL4_Word stopped = counter;
    uint64_t until = rdtsc() + 20000000;
    while (rdtsc() < until) {
    }
    test_eq(counter, stopped);
    cleanup_helper(env, &src);
    cleanup_helper(env, &dst);
    return sel4test_get_result();
}
DEFINE_TEST(FL4SMP0001, "CopyRegisters with suspendSource stops a source on another core", test_copy_registers_stalls_source,
            config_set(CONFIG_ENABLE_SMP_SUPPORT))
