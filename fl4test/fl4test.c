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

/* The kernel's time units: the TSC on x86_64, the virtual counter on
 * AArch64. */
static uint64_t rdtsc(void)
{
#ifdef CONFIG_ARCH_AARCH64
    uint64_t v;
    __asm__ volatile("isb; mrs %0, cntvct_el0" : "=r"(v));
    return v;
#else
    return __builtin_ia32_rdtsc();
#endif
}

#ifdef CONFIG_ARCH_AARCH64
#define PAGE_UNMAP seL4_ARM_Page_Unmap
#define PAGE_MAP seL4_ARM_Page_Map
#define DEFAULT_ATTR seL4_ARM_Default_VMAttributes
#define EXECUTE_NEVER seL4_ARM_ExecuteNever
#define PAGE_TEST_AND_CLEAR_ACCESSED seL4_ARM_Page_TestAndClearAccessed
typedef seL4_ARM_Page_TestAndClearAccessed_t test_and_clear_t;
#define PAGE_DERIVE_SUBFRAME seL4_ARM_Page_DeriveSubframe
#define ASID_MAKE_POOL seL4_ARM_ASIDControl_MakePool
#else
#define PAGE_UNMAP seL4_X86_Page_Unmap
#define PAGE_MAP seL4_X86_Page_Map
#define DEFAULT_ATTR seL4_X86_Default_VMAttributes
#define EXECUTE_NEVER seL4_X86_ExecuteNever
#define PAGE_TEST_AND_CLEAR_ACCESSED seL4_X86_Page_TestAndClearAccessed
typedef seL4_X86_Page_TestAndClearAccessed_t test_and_clear_t;
#define PAGE_DERIVE_SUBFRAME seL4_X86_Page_DeriveSubframe
#define ASID_MAKE_POOL seL4_X86_ASIDControl_MakePool
#endif

/* ---- l4h 0001: seL4_TCBFlag_trapSyscalls ---------------------------- */

/* The number a trapped AArch64 syscall reports is x8, the Linux syscall
 * number (l4h 0015); seL4's own number goes in x7. */
#define TRAP_X8 172

static int yield_once(seL4_Word a, seL4_Word b, seL4_Word c, seL4_Word d)
{
#ifdef CONFIG_ARCH_AARCH64
    register seL4_Word x7 __asm__("x7") = (seL4_Word) seL4_SysYield;
    register seL4_Word x8 __asm__("x8") = TRAP_X8;
    __asm__ volatile("svc #0" : "+r"(x7), "+r"(x8) : : "x0", "x1", "x2", "x3", "x4", "x5", "x6", "memory");
#else
    seL4_Yield();
#endif
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
#ifdef CONFIG_ARCH_AARCH64
    test_eq((seL4_Word) seL4_GetMR(seL4_UnknownSyscall_Syscall), (seL4_Word) TRAP_X8);
    test_eq((seL4_Word) seL4_GetMR(seL4_UnknownSyscall_X7), (seL4_Word) seL4_SysYield);
#else
    test_eq((seL4_Word) seL4_GetMR(seL4_UnknownSyscall_Syscall), (seL4_Word) seL4_SysYield);
#endif
    cleanup_helper(env, &t);
    return sel4test_get_result();
}
DEFINE_TEST(FL4TRAP0001, "trapSyscalls sends syscalls to the fault handler (l4h 0001)", test_trap_syscalls, true)

#ifdef CONFIG_ARCH_AARCH64
/* FL4: a trapped AArch64 syscall's message has x8-x30 and TPIDR_EL0 after
 * the standard 13 words, and a reply that long sets them; a reply of the
 * standard 13 words leaves them as they were. */
#define TRAP_TLS_FULL_SENT  0x7171
#define TRAP_TLS_FULL_SET   0x7272
#define TRAP_TLS_SHORT_SENT 0x7373

/* One trapped svc with x19 = 0x1919, x20 = `x20_in` and TPIDR_EL0 = `tls`;
 * returns x19, x20 and TPIDR_EL0 as the svc left them. TPIDR_EL0 (this
 * thread's TLS) is restored before anything else runs. */
static void trap_svc(seL4_Word x20_in, seL4_Word tls, seL4_Word out[3])
{
    seL4_Word saved;
    register seL4_Word x7 __asm__("x7") = (seL4_Word) seL4_SysYield;
    register seL4_Word x8 __asm__("x8") = TRAP_X8;
    register seL4_Word x19 __asm__("x19") = 0x1919;
    register seL4_Word x20 __asm__("x20") = x20_in;
    register seL4_Word x21 __asm__("x21") = tls;
    __asm__ volatile("mrs %[saved], tpidr_el0\n"
                     "msr tpidr_el0, %[tls]\n"
                     "svc #0\n"
                     "mrs %[tls], tpidr_el0\n"
                     "msr tpidr_el0, %[saved]"
                     : [saved] "=&r"(saved), "+r"(x7), "+r"(x8), "+r"(x19), "+r"(x20), [tls] "+r"(x21)
                     : : "x0", "x1", "x2", "x3", "x4", "x5", "x6", "memory");
    out[0] = x19;
    out[1] = x20;
    out[2] = x21;
}

static int trap_regs_twice(seL4_Word a, seL4_Word b, seL4_Word c, seL4_Word d)
{
    seL4_Word r[3];
    int ok = 1;
    /* A full-length reply: x20 and TPIDR_EL0 changed, x19 as sent. */
    trap_svc(0, TRAP_TLS_FULL_SENT, r);
    ok = ok && r[0] == 0x1919 && r[1] == 0x2020 && r[2] == TRAP_TLS_FULL_SET;
    /* A standard-length reply: x19, x20 and TPIDR_EL0 as sent. */
    trap_svc(0x2121, TRAP_TLS_SHORT_SENT, r);
    ok = ok && r[0] == 0x1919 && r[1] == 0x2121 && r[2] == TRAP_TLS_SHORT_SENT;
    return ok ? 7 : 1;
}

static int test_trap_full_registers(env_t env)
{
    helper_thread_t t;
    vka_object_t reply;
    test_error_eq(vka_alloc_reply(&env->vka, &reply), 0);
    vka_object_t ep = {0};
    int error = vka_alloc_endpoint(&env->vka, &ep);
    test_error_eq(error, 0);
    seL4_CPtr fault_ep = ep.cptr;
    create_helper_thread(env, &t);
    error = api_tcb_set_space(get_helper_tcb(&t), fault_ep, env->cspace_root,
                              api_make_guard_skip_word(seL4_WordBits - env->cspace_size_bits),
                              env->page_directory, seL4_NilData);
    test_error_eq(error, seL4_NoError);
    seL4_TCB_SetFlags_t f = seL4_TCB_SetFlags(get_helper_tcb(&t), 0, seL4_TCBFlag_trapSyscalls);
    test_error_eq(f.error, seL4_NoError);
    start_helper(env, &t, trap_regs_twice, 0, 0, 0, 0);
    seL4_Word badge;

    /* The first svc: the whole message, then a full-length reply back to
     * after the svc with x20 and TPIDR_EL0 changed, every other register as
     * sent. */
    seL4_MessageInfo_t tag = api_recv(fault_ep, &badge, reply.cptr);
    test_eq(seL4_MessageInfo_get_label(tag), (seL4_Word) seL4_Fault_UnknownSyscall);
    test_eq(seL4_MessageInfo_get_length(tag), (seL4_Word) seL4_UnknownSyscall_TrapLength);
    test_eq((seL4_Word) seL4_GetMR(seL4_UnknownSyscall_TrapX8), (seL4_Word) TRAP_X8);
    test_eq((seL4_Word) seL4_GetMR(seL4_UnknownSyscall_TrapX19), (seL4_Word) 0x1919);
    test_eq((seL4_Word) seL4_GetMR(seL4_UnknownSyscall_TrapX20), (seL4_Word) 0);
    test_eq((seL4_Word) seL4_GetMR(seL4_UnknownSyscall_TrapTPIDR_EL0), (seL4_Word) TRAP_TLS_FULL_SENT);
    seL4_SetMR(seL4_UnknownSyscall_FaultIP, seL4_GetMR(seL4_UnknownSyscall_FaultIP) + 4);
    seL4_SetMR(seL4_UnknownSyscall_LR, seL4_GetMR(seL4_UnknownSyscall_FaultIP));
    seL4_SetMR(seL4_UnknownSyscall_TrapX20, 0x2020);
    seL4_SetMR(seL4_UnknownSyscall_TrapTPIDR_EL0, TRAP_TLS_FULL_SET);
    seL4_Send(reply.cptr, seL4_MessageInfo_new(0, 0, 0, seL4_UnknownSyscall_TrapLength));

    /* The second: a reply of the standard length, with other values in
     * the message registers past it, which the kernel leaves alone. */
    tag = api_recv(fault_ep, &badge, reply.cptr);
    test_eq(seL4_MessageInfo_get_label(tag), (seL4_Word) seL4_Fault_UnknownSyscall);
    test_eq(seL4_MessageInfo_get_length(tag), (seL4_Word) seL4_UnknownSyscall_TrapLength);
    test_eq((seL4_Word) seL4_GetMR(seL4_UnknownSyscall_TrapX20), (seL4_Word) 0x2121);
    test_eq((seL4_Word) seL4_GetMR(seL4_UnknownSyscall_TrapTPIDR_EL0), (seL4_Word) TRAP_TLS_SHORT_SENT);
    seL4_SetMR(seL4_UnknownSyscall_FaultIP, seL4_GetMR(seL4_UnknownSyscall_FaultIP) + 4);
    seL4_SetMR(seL4_UnknownSyscall_LR, seL4_GetMR(seL4_UnknownSyscall_FaultIP));
    seL4_SetMR(seL4_UnknownSyscall_TrapX19, 0xdead);
    seL4_SetMR(seL4_UnknownSyscall_TrapX20, 0xbeef);
    seL4_SetMR(seL4_UnknownSyscall_TrapTPIDR_EL0, 0xcafe);
    seL4_Send(reply.cptr, seL4_MessageInfo_new(0, 0, 0, seL4_UnknownSyscall_Length));

    /* Its return value reaches the fault handler too: the helper's
     * seL4_Call to report it (helpers.c signal_helper_finished, MR 0 in x2)
     * is trapped like any syscall, so wait_for_helper would never return.
     * Left unanswered. */
    tag = api_recv(fault_ep, &badge, reply.cptr);
    test_eq(seL4_MessageInfo_get_label(tag), (seL4_Word) seL4_Fault_UnknownSyscall);
    test_eq((seL4_Word) seL4_GetMR(seL4_UnknownSyscall_X7), (seL4_Word) seL4_SysCall);
    test_eq((seL4_Word) seL4_GetMR(seL4_UnknownSyscall_X2), (seL4_Word) 7);
    cleanup_helper(env, &t);
    vka_free_object(&env->vka, &reply);
    vka_free_object(&env->vka, &ep);
    return sel4test_get_result();
}
DEFINE_TEST(FL4TRAP0002, "a trapped AArch64 syscall carries and takes every register", test_trap_full_registers, true)
#endif

#ifdef CONFIG_ARCH_X86_64
/* int $0xa0, the first gate open to user space, with RAX = 39 (Linux's
 * getpid). */
extern char fl4trap_int_ip[];
static int int_gate_once(seL4_Word a, seL4_Word b, seL4_Word c, seL4_Word d)
{
    seL4_Word rax = 39;
    asm volatile("fl4trap_int_ip: int $0xa0" : "+a"(rax) : : "memory");
    return 0;
}

/* `int $N` on an open gate is an UnknownSyscall for an ordinary thread. For
 * a thread with trapSyscalls set it is the #GP that int $N raises where the
 * gate is closed: UserException 13 with error code (vector << 3) | 2, at
 * the INT instruction (GitHub issue #1). */
static int test_trap_int_gate(env_t env)
{
    for (int trap = 0; trap <= 1; trap++) {
        helper_thread_t t;
        vka_object_t reply;
        test_error_eq(vka_alloc_reply(&env->vka, &reply), 0);
        seL4_CPtr fault_ep = vka_alloc_endpoint_leaky(&env->vka);
        create_helper_thread(env, &t);
        int error = api_tcb_set_space(get_helper_tcb(&t), fault_ep, env->cspace_root,
                                      api_make_guard_skip_word(seL4_WordBits - env->cspace_size_bits),
                                      env->page_directory, seL4_NilData);
        test_error_eq(error, seL4_NoError);
        seL4_TCB_SetFlags_t f = seL4_TCB_SetFlags(get_helper_tcb(&t), 0, trap ? seL4_TCBFlag_trapSyscalls : 0);
        test_error_eq(f.error, seL4_NoError);
        start_helper(env, &t, int_gate_once, 0, 0, 0, 0);
        seL4_Word badge;
        seL4_MessageInfo_t tag = api_recv(fault_ep, &badge, reply.cptr);
        if (trap) {
            test_eq(seL4_MessageInfo_get_label(tag), (seL4_Word) seL4_Fault_UserException);
            test_eq((seL4_Word) seL4_GetMR(seL4_UserException_FaultIP), (seL4_Word) fl4trap_int_ip);
            test_eq((seL4_Word) seL4_GetMR(seL4_UserException_Number), (seL4_Word) 13);
            test_eq((seL4_Word) seL4_GetMR(seL4_UserException_Code), (seL4_Word) ((0xa0 << 3) | 2));
        } else {
            test_eq(seL4_MessageInfo_get_label(tag), (seL4_Word) seL4_Fault_UnknownSyscall);
            test_eq((seL4_Word) seL4_GetMR(seL4_UnknownSyscall_FaultIP), (seL4_Word) fl4trap_int_ip);
            test_eq((seL4_Word) seL4_GetMR(seL4_UnknownSyscall_Syscall), (((seL4_Word) 0xa0 << 24) | 39));
        }
        cleanup_helper(env, &t);
    }
    return sel4test_get_result();
}
DEFINE_TEST(FL4TRAP0002, "int $N on an open gate: UnknownSyscall, or #GP with trapSyscalls (l4h 0001)",
            test_trap_int_gate, true)
#endif

/* One syscall instruction with RDX = n, as a Linux program would make with
 * whatever RDX happens to hold. */
static int syscall_once(seL4_Word n, seL4_Word b, seL4_Word c, seL4_Word d)
{
#ifdef CONFIG_ARCH_AARCH64
    register seL4_Word x7 __asm__("x7") = n;
    register seL4_Word x8 __asm__("x8") = n ^ 0x1000;
    __asm__ volatile("svc #0" : "+r"(x7), "+r"(x8) : : "x0", "x1", "x2", "x3", "x4", "x5", "x6", "memory");
#else
    seL4_Word rax = 39;
    asm volatile("syscall" : "+a"(rax) : "d"(n) : "rcx", "r11", "memory");
#endif
    return 0;
}

/* With trapSyscalls set, every syscall instruction is an UnknownSyscall
 * fault naming RDX, whatever RDX holds: seL4 calls, debug calls and
 * SetTLSBase are none of them interpreted (GitHub issue #7). */
static int test_trap_syscall_sweep(env_t env)
{
    for (int n = -1; n >= -64; n--) {
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
        start_helper(env, &t, syscall_once, (seL4_Word) n, 0, 0, 0);
        seL4_Word badge;
        seL4_MessageInfo_t tag = api_recv(fault_ep, &badge, reply.cptr);
        test_eq(seL4_MessageInfo_get_label(tag), (seL4_Word) seL4_Fault_UnknownSyscall);
#ifdef CONFIG_ARCH_AARCH64
        test_eq((seL4_Word) seL4_GetMR(seL4_UnknownSyscall_Syscall), ((seL4_Word) (seL4_Int64) n) ^ 0x1000);
#else
        test_eq((seL4_Word) seL4_GetMR(seL4_UnknownSyscall_Syscall), (seL4_Word) (seL4_Int64) n);
#endif
        cleanup_helper(env, &t);
    }
    return sel4test_get_result();
}
DEFINE_TEST(FL4TRAP0003, "trapSyscalls: every RDX from -1 to -64 faults, SetTLSBase included (l4h 0001)",
            test_trap_syscall_sweep, true)

/* ---- seL4_KernelConfig ---------------------------------------------- */

/* The value of a key this kernel knows. */
static seL4_Word kernel_config(seL4_Word key)
{
    seL4_KernelConfig_Result_t r = seL4_KernelConfig(key);
    if (r.error != seL4_NoError) {
        ZF_LOGE("key %#lx: error %d", (unsigned long) key, (int) r.error);
        _sel4test_failure("seL4_KernelConfig failed", __FILE__, __LINE__);
    }
    return r.value;
}

static int kernel_config_refused(seL4_Word key)
{
    seL4_KernelConfig_Result_t r = seL4_KernelConfig(key);
    return r.error == seL4_InvalidArgument && r.value == 0;
}

static int has(seL4_Word flags, seL4_Word flag)
{
    return (flags & flag) != 0;
}

static int test_kernel_config(env_t env)
{
    /* Both architectures. */
#ifdef CONFIG_ARCH_AARCH64
    test_eq(kernel_config(seL4_KernelConfig_Arch), (seL4_Word) seL4_KernelConfig_Arch_AArch64);
#else
    test_eq(kernel_config(seL4_KernelConfig_Arch), (seL4_Word) seL4_KernelConfig_Arch_X86_64);
#endif
    seL4_Word build = kernel_config(seL4_KernelConfig_BuildFlags);
    test_eq(has(build, seL4_KernelConfig_BuildFlag_DebugBuild), config_set(CONFIG_DEBUG_BUILD));
    test_eq(has(build, seL4_KernelConfig_BuildFlag_Printing), config_set(CONFIG_PRINTING));
    test_eq(has(build, seL4_KernelConfig_BuildFlag_Smp), config_set(CONFIG_ENABLE_SMP_SUPPORT));
    test_eq(has(build, seL4_KernelConfig_BuildFlag_HwDebugApi), config_set(CONFIG_HARDWARE_DEBUG_API));
    test_eq(has(build, seL4_KernelConfig_BuildFlag_ExportPmcUser), config_set(CONFIG_EXPORT_PMC_USER));
    test_eq(has(build, seL4_KernelConfig_BuildFlag_DangerousMsr), config_set(CONFIG_KERNEL_X86_DANGEROUS_MSR));
    test_eq(build >> 6, (seL4_Word) 0);
    seL4_Word online = kernel_config(seL4_KernelConfig_OnlineCpus);
    test_eq(online, (seL4_Word) env->cores);
    test_geq(online, (seL4_Word) 1);
    test_leq(online, kernel_config(seL4_KernelConfig_MaxCpus));
    test_eq(kernel_config(seL4_KernelConfig_MaxCpus), (seL4_Word) CONFIG_MAX_NUM_NODES);

    /* A backend exactly when none of the reasons against one holds. */
    seL4_Word backend = kernel_config(seL4_KernelConfig_VirtBackend);
    seL4_Word reject = kernel_config(seL4_KernelConfig_VirtReject);
    seL4_Word virt = kernel_config(seL4_KernelConfig_VirtFeatures);
    test_eq(backend == seL4_KernelConfig_VirtBackend_None, reject != seL4_KernelConfig_VirtReject_None);
    test_leq(reject, (seL4_Word) seL4_KernelConfig_VirtReject_El1Only);

    seL4_Word cvm = kernel_config(seL4_KernelConfig_CvmType);
    seL4_Word cvm_flags = kernel_config(seL4_KernelConfig_CvmFlags);
    test_leq(cvm, (seL4_Word) seL4_KernelConfig_CvmType_Tdx);
    test_eq(has(cvm_flags, seL4_KernelConfig_CvmFlag_SharedDma), cvm != seL4_KernelConfig_CvmType_None);
    test_eq(has(cvm_flags, seL4_KernelConfig_CvmFlag_Hardened),
            cvm == seL4_KernelConfig_CvmType_SevSnp || cvm == seL4_KernelConfig_CvmType_Tdx);

    printf("FL4KCFG0001: build %#lx, %lu of %lu cores, virt %lu (reject %lu, features %#lx), cvm %lu (%#lx)\n",
           (unsigned long) build, (unsigned long) online,
           (unsigned long) kernel_config(seL4_KernelConfig_MaxCpus), (unsigned long) backend,
           (unsigned long) reject, (unsigned long) virt, (unsigned long) cvm, (unsigned long) cvm_flags);

    /* The other architecture's keys and ones no kernel has. */
#ifdef CONFIG_ARCH_AARCH64
    for (seL4_Word k = seL4_KernelConfig_SpecStatus; k <= seL4_KernelConfig_SpecMsrValid; k++) {
        test_check(kernel_config_refused(k));
    }
    for (seL4_Word k = seL4_KernelConfig_X86CpuVendor; k <= seL4_KernelConfig_X86ArchCapabilities; k++) {
        test_check(kernel_config_refused(k));
    }
#else
    test_check(kernel_config_refused(seL4_KernelConfig_VirtS2IpaBits));
    test_check(kernel_config_refused(seL4_KernelConfig_VirtVgicLrs));
    test_check(kernel_config_refused(seL4_KernelConfig_ArmMitigations));
    for (seL4_Word k = seL4_KernelConfig_ArmPlatformFlags; k <= seL4_KernelConfig_ArmTimerFreqHz; k++) {
        test_check(kernel_config_refused(k));
    }
#endif
    test_check(kernel_config_refused(0xdeadbeef));
    test_check(kernel_config_refused(0));
    test_check(kernel_config_refused(~0ul));
    test_check(kernel_config_refused(seL4_KernelConfig_Arch | BIT(32)));

#ifdef CONFIG_ARCH_AARCH64
    seL4_Word mitigations = kernel_config(seL4_KernelConfig_ArmMitigations);
    seL4_Word platform = kernel_config(seL4_KernelConfig_ArmPlatformFlags);
    seL4_Word gic = kernel_config(seL4_KernelConfig_ArmGicVersion);
    seL4_Word lrs = kernel_config(seL4_KernelConfig_VirtVgicLrs);
    seL4_Word ipa = kernel_config(seL4_KernelConfig_VirtS2IpaBits);
    int vhe = has(platform, seL4_KernelConfig_ArmPlatformFlag_El2Vhe);
    int nvhe = has(platform, seL4_KernelConfig_ArmPlatformFlag_El2Nvhe);
    test_eq(mitigations >> 3, (seL4_Word) 0);
    test_eq(platform >> 7, (seL4_Word) 0);
    test_check(!(vhe && nvhe));
    /* The kernel does not boot without 16-bit ASIDs (l4h 0016). */
    test_check(has(platform, seL4_KernelConfig_ArmPlatformFlag_Asid16));
    test_check(gic == 2 || gic == 3);
    if (gic == 2) {
        test_check(!has(platform, seL4_KernelConfig_ArmPlatformFlag_Gicv3Sre));
        test_check(!has(platform, seL4_KernelConfig_ArmPlatformFlag_ItsActive));
    }
    test_leq(kernel_config(seL4_KernelConfig_ArmMaxSpi), (seL4_Word) 1019);
    test_leq(kernel_config(seL4_KernelConfig_ArmPaBits), (seL4_Word) 48);
    test_geq(kernel_config(seL4_KernelConfig_ArmPaBits), (seL4_Word) 32);
    test_leq(kernel_config(seL4_KernelConfig_ArmPsciMethod), (seL4_Word) seL4_KernelConfig_ArmPsci_Hvc);
    test_check(online == 1 || kernel_config(seL4_KernelConfig_ArmPsciMethod) != seL4_KernelConfig_ArmPsci_Absent);
    seL4_Word hz;
    __asm__ volatile("mrs %0, cntfrq_el0" : "=r"(hz));
    test_eq(kernel_config(seL4_KernelConfig_ArmTimerFreqHz), hz & 0xffffffff);
    test_check(ipa == 40 || ipa == 44 || ipa == 48);
    test_leq(lrs, (seL4_Word) 16);
    /* Guests run only at EL2, in the kernel's mode of it, with a VGIC. */
    test_eq(backend == seL4_KernelConfig_VirtBackend_El2Vhe, vhe && reject == seL4_KernelConfig_VirtReject_None);
    test_eq(backend == seL4_KernelConfig_VirtBackend_El2Nvhe, nvhe && reject == seL4_KernelConfig_VirtReject_None);
    test_eq(reject == seL4_KernelConfig_VirtReject_El1Only, !vhe && !nvhe);
    test_eq(has(virt, seL4_KernelConfig_VirtFeature_ArmVirtReady), backend != seL4_KernelConfig_VirtBackend_None);
    test_eq(has(virt, seL4_KernelConfig_VirtFeature_ArmGicv2Vgic),
            backend != seL4_KernelConfig_VirtBackend_None && gic == 2);
    test_eq(has(virt, seL4_KernelConfig_VirtFeature_ArmGicv3Vgic),
            backend != seL4_KernelConfig_VirtBackend_None && gic == 3);
    test_check(backend == seL4_KernelConfig_VirtBackend_None || lrs > 0);
    test_check(vhe || nvhe || !has(virt, seL4_KernelConfig_VirtFeature_ArmVmid16));
    test_eq(cvm, (seL4_Word) seL4_KernelConfig_CvmType_None);
    printf("FL4KCFG0001: mitigations %#lx, platform %#lx, GICv%lu, %lu LRs, IPA %lu, timer %lu Hz\n",
           (unsigned long) mitigations, (unsigned long) platform, (unsigned long) gic, (unsigned long) lrs,
           (unsigned long) ipa, (unsigned long) hz);
#else
    seL4_Word status = kernel_config(seL4_KernelConfig_SpecStatus);
    seL4_Word spec_reject = kernel_config(seL4_KernelConfig_SpecReject);
    seL4_Word flags = kernel_config(seL4_KernelConfig_SpecFlags);
    seL4_Word entry = kernel_config(seL4_KernelConfig_SpecEntryActions);
    seL4_Word vmexit = kernel_config(seL4_KernelConfig_SpecVmexitActions);
    seL4_Word ctrl = kernel_config(seL4_KernelConfig_SpecCtrlMsr);
    seL4_Word efer = kernel_config(seL4_KernelConfig_SpecEferMsr);
    seL4_Word valid = kernel_config(seL4_KernelConfig_SpecMsrValid);
    seL4_Word vendor = kernel_config(seL4_KernelConfig_X86CpuVendor);
    seL4_Word features = kernel_config(seL4_KernelConfig_X86CpuFeatures);
    int skim = has(flags, seL4_KernelConfig_SpecFlag_Skim);
    test_leq(status, (seL4_Word) seL4_KernelConfig_SpecStatus_Complete);
    test_eq(status == seL4_KernelConfig_SpecStatus_Complete, spec_reject == seL4_KernelConfig_SpecReject_None);
    test_leq(spec_reject, (seL4_Word) seL4_KernelConfig_SpecReject_Lfence);
    test_eq(flags >> 13, (seL4_Word) 0);
    test_eq(entry >> 6, (seL4_Word) 0);
    test_eq(vmexit >> 6, (seL4_Word) 0);
    /* What the flags say of IA32_SPEC_CTRL (where firmware may have set
     * more) and EFER, and of each other. */
    test_check(!has(flags, seL4_KernelConfig_SpecFlag_Eibrs | seL4_KernelConfig_SpecFlag_LegacyIbrs) || has(ctrl, 1));
    test_check(!(has(flags, seL4_KernelConfig_SpecFlag_Eibrs) && has(flags, seL4_KernelConfig_SpecFlag_LegacyIbrs)));
    test_check(!has(flags, seL4_KernelConfig_SpecFlag_LegacyIbrs)
               || has(entry, seL4_KernelConfig_SpecAction_LegacyIbrs));
    test_check(!has(flags, seL4_KernelConfig_SpecFlag_Stibp) || has(ctrl, 2));
    test_check(!has(flags, seL4_KernelConfig_SpecFlag_BhiDisS) || has(ctrl, 1 << 10));
    test_check(!has(flags, seL4_KernelConfig_SpecFlag_AutoIbrs) || has(efer, 1 << 21));
    test_check(!has(flags, seL4_KernelConfig_SpecFlag_Retpoline) || has(flags, seL4_KernelConfig_SpecFlag_SafeRet));
    test_eq(has(flags, seL4_KernelConfig_SpecFlag_EagerFpu), vendor == seL4_KernelConfig_X86Vendor_Intel);
    /* Long mode with SYSCALL, and NX and AMD-V as the kernel says. */
    test_eq(efer & 0x501, (seL4_Word) 0x501);
    test_eq(has(efer, 1 << 11), has(features, seL4_KernelConfig_X86Feature_Nx));
    test_eq(has(efer, 1 << 12), backend == seL4_KernelConfig_VirtBackend_AmdV);
    /* An MSR that is not valid reads 0; EFER always is. */
    test_eq(valid >> 7, (seL4_Word) 0);
    test_check(has(valid, seL4_KernelConfig_SpecMsrValid_Efer));
    test_check(has(valid, seL4_KernelConfig_SpecMsrValid_SpecCtrl) || ctrl == 0);
    test_check(has(valid, seL4_KernelConfig_SpecMsrValid_ArchCapabilities)
               || kernel_config(seL4_KernelConfig_X86ArchCapabilities) == 0);
    test_check(has(valid, seL4_KernelConfig_SpecMsrValid_TsxCtrl)
               || kernel_config(seL4_KernelConfig_SpecTsxCtrlMsr) == 0);
    test_check(has(valid, seL4_KernelConfig_SpecMsrValid_McuOptCtrl)
               || kernel_config(seL4_KernelConfig_SpecMcuOptCtrlMsr) == 0);
    test_check(has(valid, seL4_KernelConfig_SpecMsrValid_AmdDeCfg)
               || kernel_config(seL4_KernelConfig_SpecAmdDeCfgMsr) == 0);
    test_check(has(valid, seL4_KernelConfig_SpecMsrValid_AmdBpCfg)
               || kernel_config(seL4_KernelConfig_SpecAmdBpCfgMsr) == 0);
    /* Intel's and AMD's own. */
    test_check(vendor == seL4_KernelConfig_X86Vendor_Intel
               || !has(valid, seL4_KernelConfig_SpecMsrValid_ArchCapabilities
                       | seL4_KernelConfig_SpecMsrValid_TsxCtrl | seL4_KernelConfig_SpecMsrValid_McuOptCtrl));
    test_check((vendor == seL4_KernelConfig_X86Vendor_Amd
                && !has(features, seL4_KernelConfig_X86Feature_Hypervisor))
               || !has(valid, seL4_KernelConfig_SpecMsrValid_AmdDeCfg | seL4_KernelConfig_SpecMsrValid_AmdBpCfg));
    /* Without a plan the kernel clears the buffers, and runs no guest. */
    test_check(status == seL4_KernelConfig_SpecStatus_Complete
               || has(flags, seL4_KernelConfig_SpecFlag_VerwBuffers));
    test_check(backend == seL4_KernelConfig_VirtBackend_None || status == seL4_KernelConfig_SpecStatus_Complete);
    test_check(backend == seL4_KernelConfig_VirtBackend_None || (!skim && cvm == seL4_KernelConfig_CvmType_None));
    test_eq(vmexit != 0, backend != seL4_KernelConfig_VirtBackend_None);
    test_check(backend != seL4_KernelConfig_VirtBackend_None
               || !has(flags, seL4_KernelConfig_SpecFlag_VmexitIbpbDeferred | seL4_KernelConfig_SpecFlag_NoSmt));
    test_leq(backend, (seL4_Word) seL4_KernelConfig_VirtBackend_AmdV);
    test_eq(reject == seL4_KernelConfig_VirtReject_CvmActive, cvm != seL4_KernelConfig_CvmType_None);
    test_eq(reject == seL4_KernelConfig_VirtReject_SkimActive, skim && cvm == seL4_KernelConfig_CvmType_None);
    test_check(backend != seL4_KernelConfig_VirtBackend_None || virt == 0);

    test_leq(vendor, (seL4_Word) seL4_KernelConfig_X86Vendor_Hygon);
    test_eq(features >> 11, (seL4_Word) 0);
    test_check(!has(features, seL4_KernelConfig_X86Feature_Invpcid)
               || has(features, seL4_KernelConfig_X86Feature_Pcid));
    test_check(!has(features, seL4_KernelConfig_X86Feature_IdlePoll)
               || (has(features, seL4_KernelConfig_X86Feature_Hypervisor) && online > 1));
    test_leq(kernel_config(seL4_KernelConfig_X86FpuSaveInsn), (seL4_Word) seL4_KernelConfig_X86FpuInsn_Xsaves);
    test_eq(kernel_config(seL4_KernelConfig_X86FpuXcr0) == 0,
            kernel_config(seL4_KernelConfig_X86FpuSaveInsn) == seL4_KernelConfig_X86FpuInsn_Fxsave);
    test_geq(kernel_config(seL4_KernelConfig_X86TscMhz), (seL4_Word) 1);
    test_geq(kernel_config(seL4_KernelConfig_X86TscSource), (seL4_Word) seL4_KernelConfig_X86TscSource_Cpuid);
    test_leq(kernel_config(seL4_KernelConfig_X86TscSource), (seL4_Word) seL4_KernelConfig_X86TscSource_Kvm);
    test_geq(kernel_config(seL4_KernelConfig_X86MaxPaddrBits), (seL4_Word) 36);
    test_leq(kernel_config(seL4_KernelConfig_X86MaxPaddrBits), (seL4_Word) 52);
    test_check(!has(features, seL4_KernelConfig_X86Feature_Hypervisor)
               || kernel_config(seL4_KernelConfig_X86MicrocodeRev) == 0);
    (void) kernel_config(seL4_KernelConfig_X86IoapicCount);
    /* IA32_ARCH_CAPABILITIES is read on Intel only, where RDCL_NO (bit 0)
     * decides the skim window. */
    seL4_Word arch = kernel_config(seL4_KernelConfig_X86ArchCapabilities);
    if (vendor == seL4_KernelConfig_X86Vendor_Intel) {
        test_eq(skim, !has(arch, 1));
    } else {
        test_eq(arch, (seL4_Word) 0);
    }
    printf("FL4KCFG0001: spec %lu (reject %lu), flags %#lx, entry %#lx, vmexit %#lx, SPEC_CTRL %#lx, "
           "vendor %lu, features %#lx, xcr0 %#lx (%lu), TSC %lu MHz (%lu), microcode %#lx, "
           "%lu bits, %lu IOAPIC(s), ARCH_CAPABILITIES %#lx, EFER %#lx, "
           "MSRs valid %#lx\n",
           (unsigned long) status, (unsigned long) spec_reject, (unsigned long) flags, (unsigned long) entry,
           (unsigned long) vmexit, (unsigned long) ctrl, (unsigned long) vendor, (unsigned long) features,
           (unsigned long) kernel_config(seL4_KernelConfig_X86FpuXcr0),
           (unsigned long) kernel_config(seL4_KernelConfig_X86FpuSaveInsn),
           (unsigned long) kernel_config(seL4_KernelConfig_X86TscMhz),
           (unsigned long) kernel_config(seL4_KernelConfig_X86TscSource),
           (unsigned long) kernel_config(seL4_KernelConfig_X86MicrocodeRev),
           (unsigned long) kernel_config(seL4_KernelConfig_X86MaxPaddrBits),
           (unsigned long) kernel_config(seL4_KernelConfig_X86IoapicCount), (unsigned long) arch,
           (unsigned long) efer, (unsigned long) valid);
#endif
    return sel4test_get_result();
}
DEFINE_TEST(FL4KCFG0001, "seL4_KernelConfig answers every key of this architecture, and no other", test_kernel_config, true)

/* The call by registers: the error in the capability register, a message
 * info of length 1 and the value in the first message register; the other
 * message registers and the IPC buffer are the caller's. */
static int test_kernel_config_registers(env_t env)
{
    seL4_IPCBuffer *buffer = seL4_GetIPCBuffer();
    seL4_Word before[seL4_MsgMaxLength];
    for (int i = 0; i < seL4_MsgMaxLength; i++) {
        buffer->msg[i] = 0x5a5a0000 + i;
        before[i] = buffer->msg[i];
    }
    for (int known = 0; known <= 1; known++) {
        seL4_Word key = known ? seL4_KernelConfig_MaxCpus : 0xdeadbeef;
        seL4_Word error = ~0ul, info = ~0ul;
        seL4_Word mr0 = 0x1111, mr1 = 0x2222, mr2 = 0x3333, mr3 = 0x4444;
#ifdef CONFIG_ARCH_AARCH64
        arm_sys_send_recv(seL4_SysKernelConfig, key, &error, 0x7f, &info, &mr0, &mr1, &mr2, &mr3, 0);
#else
        x64_sys_send_recv(seL4_SysKernelConfig, key, &error, 0x7f, &info, &mr0, &mr1, &mr2, &mr3, 0);
#endif
        test_eq(error, (seL4_Word)(known ? seL4_NoError : seL4_InvalidArgument));
        test_eq(info, seL4_MessageInfo_new(0, 0, 0, 1).words[0]);
        test_eq(mr0, (seL4_Word)(known ? CONFIG_MAX_NUM_NODES : 0));
        test_eq(mr1, (seL4_Word) 0x2222);
        test_eq(mr2, (seL4_Word) 0x3333);
        test_eq(mr3, (seL4_Word) 0x4444);
    }
    for (int i = 0; i < seL4_MsgMaxLength; i++) {
        test_eq(buffer->msg[i], before[i]);
    }
    return sel4test_get_result();
}
DEFINE_TEST(FL4KCFG0002, "seL4_KernelConfig answers in registers and leaves the IPC buffer alone",
            test_kernel_config_registers, true)

static int kernel_config_once(seL4_Word key, seL4_Word b, seL4_Word c, seL4_Word d)
{
    seL4_KernelConfig_Result_t r = seL4_KernelConfig(key);
    /* Not reached under trapSyscalls. */
    return r.error == seL4_NoError ? 1 : 2;
}

/* A thread with trapSyscalls set makes no seL4 calls, this one included:
 * its fault handler gets it, not the kernel's answer. */
static int test_trap_kernel_config(env_t env)
{
    for (int known = 0; known <= 1; known++) {
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
        seL4_Word key = known ? seL4_KernelConfig_Arch : 0xdeadbeef;
        start_helper(env, &t, kernel_config_once, key, 0, 0, 0);
        seL4_Word badge;
        seL4_MessageInfo_t tag = api_recv(fault_ep, &badge, reply.cptr);
        test_eq(seL4_MessageInfo_get_label(tag), (seL4_Word) seL4_Fault_UnknownSyscall);
        /* The call's own registers, unanswered. */
#ifdef CONFIG_ARCH_AARCH64
        test_eq((seL4_Word) seL4_GetMR(seL4_UnknownSyscall_X7), (seL4_Word) seL4_SysKernelConfig);
        test_eq((seL4_Word) seL4_GetMR(seL4_UnknownSyscall_X0), key);
        test_eq((seL4_Word) seL4_GetMR(seL4_UnknownSyscall_X1), (seL4_Word) 0);
#else
        test_eq((seL4_Word) seL4_GetMR(seL4_UnknownSyscall_Syscall), (seL4_Word) seL4_SysKernelConfig);
        test_eq((seL4_Word) seL4_GetMR(seL4_UnknownSyscall_RDI), key);
        test_eq((seL4_Word) seL4_GetMR(seL4_UnknownSyscall_RSI), (seL4_Word) 0);
#endif
        cleanup_helper(env, &t);
    }
    return sel4test_get_result();
}
DEFINE_TEST(FL4KCFG0003, "trapSyscalls sends seL4_KernelConfig to the fault handler", test_trap_kernel_config, true)

#ifdef CONFIG_ARCH_AARCH64
/* PACGA x0, x1, x2 (FEAT_PAuth), as an encoding so any assembler takes it.
 * Unlike PACIA and AUTIA, PACGA has no SCTLR_EL1 enable: at EL0 it runs,
 * or traps to EL2 when HCR_EL2.API is clear (ARM ARM, AddPACGA). */
static seL4_Word pacga(seL4_Word x, seL4_Word y)
{
    register seL4_Word x0 __asm__("x0");
    register seL4_Word x1 __asm__("x1") = x;
    register seL4_Word x2 __asm__("x2") = y;
    __asm__ volatile(".inst 0x9ac23020" : "=r"(x0) : "r"(x1), "r"(x2));
    return x0;
}

#define PACGA_LABEL 0x5ac

/* One PACGA, its result sent on `ep` (the thread's fault endpoint too:
 * where PAuth is absent the instruction is UNDEFINED and faults there). */
static int pacga_report(seL4_Word ep, seL4_Word b, seL4_Word c, seL4_Word d)
{
    seL4_Word r = pacga(0x0123456789abcdefull, 0x42);
    seL4_Word r2 = pacga(0x0123456789abcdefull, 0x42);
    seL4_SetMR(0, r);
    seL4_SetMR(1, r2);
    seL4_Send(ep, seL4_MessageInfo_new(PACGA_LABEL, 0, 0, 2));
    return 0;
}

/* An EL0 PACGA on every core finishes at EL0 with one result: FL4 owns
 * EL2 when it boots there, sets HCR_EL2.API and clears the generic key on
 * each core. Before, the boot core's PACGA trapped to EL2 and ran at the
 * VBAR_EL2 the firmware left in memory FL4 hands to user space (another
 * core's at whatever its VBAR_EL2 reset to), and never came back. Without
 * PAuth (tcg-a57) PACGA is UNDEFINED: a user exception fault, and nothing
 * to check (as is any trap to EL2 FL4 did not foresee, which its EL2
 * vectors pass on to EL1). */
static int test_el0_pacga_stays_at_el0(env_t env)
{
    seL4_Word first = 0;
    for (int core = 0; core < env->cores; core++) {
        helper_thread_t t;
        vka_object_t reply;
        test_error_eq(vka_alloc_reply(&env->vka, &reply), 0);
        seL4_CPtr ep = vka_alloc_endpoint_leaky(&env->vka);
        create_helper_thread(env, &t);
        test_error_eq(api_tcb_set_space(get_helper_tcb(&t), ep, env->cspace_root,
                                        api_make_guard_skip_word(seL4_WordBits - env->cspace_size_bits),
                                        env->page_directory, seL4_NilData), seL4_NoError);
        set_helper_affinity(env, &t, core);
        start_helper(env, &t, pacga_report, ep, 0, 0, 0);
        seL4_Word badge;
        seL4_MessageInfo_t tag = api_recv(ep, &badge, reply.cptr);
        seL4_Word label = seL4_MessageInfo_get_label(tag);
        if (label == seL4_Fault_UserException) {
            printf("FL4TRAP0004: no PAuth on core %d\n", core);
            test_eq(core, 0);
            cleanup_helper(env, &t);
            break;
        }
        test_eq(label, (seL4_Word) PACGA_LABEL);
        seL4_Word r = seL4_GetMR(0);
        printf("FL4TRAP0004: PACGA at EL0 on core %d: %#lx\n", core, (unsigned long) r);
        test_eq(r, seL4_GetMR(1));
        test_eq(r & 0xffffffffull, (seL4_Word) 0);
        if (core == 0) {
            first = r;
        }
        test_eq(r, first);
        wait_for_helper(&t);
        cleanup_helper(env, &t);
    }
    return sel4test_get_result();
}
DEFINE_TEST(FL4TRAP0004, "EL0 PACGA runs at EL0 with the same zero key on every core (EL2 boot)",
            test_el0_pacga_stays_at_el0, true)
#endif

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

#ifdef CONFIG_ARCH_AARCH64
/* AArch64: an image written to a thread reads back, V0-V31 then FPSR and
 * FPCR, with their undefined bits cleared. */
static int test_fpu_read_write(env_t env)
{
    helper_thread_t t;
    create_helper_thread(env, &t);
    seL4_CPtr fcap;
    uint8_t *frame = map_frame(env, &fcap);
    test_assert(frame != NULL);
    test_error_eq(seL4_TCB_ReadFPU(get_helper_tcb(&t), fcap, 0), seL4_NoError);
    for (int i = 0; i < 16; i++) {
        frame[16 + i] = 0xa0 + i;
    }
    uint32_t fpsr = 0xffffffffu, fpcr = 0xffffffffu;
    memcpy(frame + 512, &fpsr, 4);
    memcpy(frame + 516, &fpcr, 4);
    test_error_eq(seL4_TCB_WriteFPU(get_helper_tcb(&t), fcap, 0), seL4_NoError);
    memset(frame, 0, FPU_BYTES);
    test_error_eq(seL4_TCB_ReadFPU(get_helper_tcb(&t), fcap, 0), seL4_NoError);
    for (int i = 0; i < 16; i++) {
        test_eq((int) frame[16 + i], 0xa0 + i);
    }
    memcpy(&fpsr, frame + 512, 4);
    memcpy(&fpcr, frame + 516, 4);
    test_eq(fpsr, 0xf800009fu);
    test_eq(fpcr, 0x07ff9f07u);
    test_neq(seL4_TCB_ReadFPU(get_helper_tcb(&t), fcap, 8), seL4_NoError);
    cleanup_helper(env, &t);
    return sel4test_get_result();
}
DEFINE_TEST(FL4FPU0001, "TCB_ReadFPU and TCB_WriteFPU round trip, sanitised (l4h 0002)", test_fpu_read_write, true)

static int read_fpcr(seL4_Word a, seL4_Word b, seL4_Word c, seL4_Word d)
{
    uint64_t v;
    __asm__ volatile("mrs %0, fpcr" : "=r"(v));
    return (int)(v & 0xffffffff);
}

/* A thread starts with the FP/SIMD state written to it. */
static int test_fpu_write_runs(env_t env)
{
    helper_thread_t t;
    create_helper_thread(env, &t);
    seL4_CPtr fcap;
    uint8_t *frame = map_frame(env, &fcap);
    test_assert(frame != NULL);
    test_error_eq(seL4_TCB_ReadFPU(get_helper_tcb(&t), fcap, 0), seL4_NoError);
    /* Flush-to-zero and default NaN. */
    uint32_t fpcr = (1u << 24) | (1u << 25);
    memcpy(frame + 516, &fpcr, 4);
    test_error_eq(seL4_TCB_WriteFPU(get_helper_tcb(&t), fcap, 0), seL4_NoError);
    start_helper(env, &t, read_fpcr, 0, 0, 0, 0);
    test_eq(wait_for_helper(&t), (int) fpcr);
    cleanup_helper(env, &t);
    return sel4test_get_result();
}
DEFINE_TEST(FL4FPU0002, "A thread runs with the FPU state written to it (l4h 0002)", test_fpu_write_runs, true)
#else
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
    /* XSTATE_BV bit 1 marks the XMM payload as present in this image. */
    frame[512] |= 2;
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
#endif

/* ---- l4h 0009: seL4_X86_ExecuteNever; 0023: TestAndClearAccessed ----- */

/* Map `cap` at `vaddr` with `attr`, after vspace has made the page tables. */
static int remap(env_t env, seL4_CPtr cap, void *vaddr, seL4_Word attr)
{
    int err = PAGE_UNMAP(cap);
    if (err) {
        return err;
    }
    return PAGE_MAP(cap, env->page_directory, (seL4_Word) vaddr, seL4_AllRights, attr);
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
#ifdef CONFIG_ARCH_AARCH64
    uint32_t ret = 0xd65f03c0;
    memcpy(page, &ret, 4);
#else
    page[0] = 0xc3; /* ret */
#endif
    test_error_eq(remap(env, fcap, page, DEFAULT_ATTR | EXECUTE_NEVER), seL4_NoError);

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
    test_and_clear_t r = PAGE_TEST_AND_CLEAR_ACCESSED(fcap);
#ifdef CONFIG_ARCH_AARCH64
    if (r.error == seL4_IllegalOperation) {
        /* Without hardware access-flag management (TCR_EL1.HA) a cleared
         * flag would fault, so the kernel refuses. */
        printf("No hardware access flags; skipping\n");
        return sel4test_get_result();
    }
#endif
    test_error_eq(r.error, seL4_NoError);
    test_eq(r.accessed, (seL4_Word) 1);
    r = PAGE_TEST_AND_CLEAR_ACCESSED(fcap);
    test_error_eq(r.error, seL4_NoError);
    test_eq(r.accessed, (seL4_Word) 0);
    /* The bit was cleared without a flush: drop the TLB entry, then touch. */
    test_error_eq(remap(env, fcap, (void *) page, DEFAULT_ATTR), seL4_NoError);
    (void) page[1];
    r = PAGE_TEST_AND_CLEAR_ACCESSED(fcap);
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
    int err = PAGE_DERIVE_SUBFRAME(large, env->cspace_root, cn.cptr, seL4_WordBits, 0, 0x3000, 4, seL4_AllRights);
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

#ifdef CONFIG_ARCH_X86_64
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

/* A far return to 0x23, Linux's 32-bit user code selector. */
extern char fl4sel_lret_ip[];
static int far_return_to_compat(seL4_Word a, seL4_Word b, seL4_Word c, seL4_Word d)
{
    __asm__ volatile("pushq $0x23\n\t"
                     "leaq 1f(%%rip), %%rax\n\t"
                     "pushq %%rax\n"
                     "fl4sel_lret_ip: lretq\n"
                     "1: ud2"
                     : : : "rax", "memory");
    return 0;
}

/* User code runs in 64-bit mode only: 0x23 names no code segment, so the
 * far return raises #GP with the selector as its error code instead of
 * entering compatibility mode (whose SYSCALL and 32-bit EIP the entry
 * code does not expect), where the ud2 would fault. */
static int test_no_compat_mode(env_t env)
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
    start_helper(env, &t, far_return_to_compat, 0, 0, 0, 0);
    seL4_Word badge;
    seL4_MessageInfo_t tag = api_recv(fault_ep, &badge, reply.cptr);
    test_eq(seL4_MessageInfo_get_label(tag), (seL4_Word) seL4_Fault_UserException);
    test_eq((seL4_Word) seL4_GetMR(seL4_UserException_Number), (seL4_Word) 13);
    test_eq((seL4_Word) seL4_GetMR(seL4_UserException_Code), (seL4_Word) 0x20);
    test_eq((seL4_Word) seL4_GetMR(seL4_UserException_FaultIP), (seL4_Word) fl4sel_lret_ip);
    cleanup_helper(env, &t);
    return sel4test_get_result();
}
DEFINE_TEST(FL4SEL0002, "A far return to the 32-bit user selector faults: no compatibility mode", test_no_compat_mode, true)

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
#endif

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

/* ---- l4h 0008: error replies start with an empty message ------------ */

/* With KernelInvocationReportErrorIPC, the error string in the IPC buffer
 * belongs to the invocation that failed: whatever the buffer held before,
 * a failed invocation leaves it empty (FL4 keeps no error strings). */
static int test_error_string_empty(env_t env)
{
#ifdef CONFIG_KERNEL_INVOCATION_REPORT_ERROR_IPC
    char *s = seL4_GetDebugError();
    strcpy(s, "stale");
    char old = seL4_CanPrintError();
    seL4_SetPrintError(0);
    /* Slot 0 is always empty: suspending it fails with InvalidCapability. */
    int error = seL4_TCB_Suspend(seL4_CapNull);
    seL4_SetPrintError(old);
    test_eq(error, seL4_InvalidCapability);
    test_eq(s[0], 0);
#endif
    return sel4test_get_result();
}
DEFINE_TEST(FL4ERR0001, "A failed invocation reports no stale error string (l4h 0008)", test_error_string_empty, true)

/* ---- IPC round trips (DESIGN.md §12, performance) ------------------- */

static int ipc_server(seL4_Word ep, seL4_Word reply, seL4_Word c, seL4_Word d)
{
    seL4_Word badge;
    seL4_Recv(ep, &badge, reply);
    while (1) {
        seL4_ReplyRecv(ep, seL4_MessageInfo_new(0, 0, 0, 0), &badge, reply);
    }
    return 0;
}

/* Not a pass/fail check: prints the cost of a same-address-space
 * Call/ReplyRecv round trip, and gives a profiler a steady IPC loop. */
static int test_ipc_round_trip(env_t env)
{
    enum { N = 2000000 };
    helper_thread_t server;
    vka_object_t reply;
    test_error_eq(vka_alloc_reply(&env->vka, &reply), 0);
    seL4_CPtr ep = vka_alloc_endpoint_leaky(&env->vka);
    create_helper_thread(env, &server);
    set_helper_priority(env, &server, env->priority);
    start_helper(env, &server, ipc_server, ep, reply.cptr, 0, 0);
    seL4_Call(ep, seL4_MessageInfo_new(0, 0, 0, 0));
    uint64_t t0 = rdtsc();
    for (int i = 0; i < N; i++) {
        seL4_Call(ep, seL4_MessageInfo_new(0, 0, 0, 0));
    }
    uint64_t t1 = rdtsc();
    printf("FL4 IPC: %lu TSC ticks per Call/ReplyRecv round trip\n", (unsigned long)((t1 - t0) / N));
    cleanup_helper(env, &server);
    return sel4test_get_result();
}
DEFINE_TEST(FL4PERF0001, "IPC round trip cost (printed, not checked)", test_ipc_round_trip, true)

/* ---- Lazy FPU switching (DESIGN.md §3) ------------------------------ */

/* xmm1 on x86_64, d1 (the low half of v1) on AArch64. */
static inline void xmm1_set(uint64_t v)
{
#ifdef CONFIG_ARCH_AARCH64
    __asm__ volatile("fmov d1, %0" :: "r"(v) : "v1");
#else
    __asm__ volatile("movq %0, %%xmm1" :: "r"(v) : "xmm1");
#endif
}

static inline uint64_t xmm1_get(void)
{
    uint64_t v;
#ifdef CONFIG_ARCH_AARCH64
    __asm__ volatile("fmov %0, d1" : "=r"(v));
#else
    __asm__ volatile("movq %%xmm1, %0" : "=r"(v));
#endif
    return v;
}

static int fpu_pong(seL4_Word ep, seL4_Word reply, seL4_Word c, seL4_Word d)
{
    seL4_Word badge;
    seL4_Recv(ep, &badge, reply);
    xmm1_set(0x5e5e5e5e00000000ull);
    seL4_Word bad = 0;
    while (1) {
        if (xmm1_get() != 0x5e5e5e5e00000000ull) {
            bad++;
        }
        seL4_SetMR(0, bad);
        seL4_ReplyRecv(ep, seL4_MessageInfo_new(0, 0, 0, 1), &badge, reply);
    }
    return 0;
}

/* Two threads keep different values in xmm1 across IPCs: each must see its
 * own after every switch, whichever way the FPU is switched. */
static int test_fpu_ping_pong(env_t env)
{
    helper_thread_t server;
    vka_object_t reply;
    test_error_eq(vka_alloc_reply(&env->vka, &reply), 0);
    seL4_CPtr ep = vka_alloc_endpoint_leaky(&env->vka);
    create_helper_thread(env, &server);
    set_helper_priority(env, &server, env->priority);
    start_helper(env, &server, fpu_pong, ep, reply.cptr, 0, 0);
    seL4_Call(ep, seL4_MessageInfo_new(0, 0, 0, 0));
    int mine_bad = 0;
    for (int i = 0; i < 10000; i++) {
        xmm1_set(0xc1c1c1c100000000ull + i);
        seL4_Call(ep, seL4_MessageInfo_new(0, 0, 0, 0));
        if (xmm1_get() != 0xc1c1c1c100000000ull + i) {
            mine_bad++;
        }
    }
    test_eq(mine_bad, 0);
    test_eq((int) seL4_GetMR(0), 0);
    cleanup_helper(env, &server);
    return sel4test_get_result();
}
DEFINE_TEST(FL4FPU0003, "Threads keep their own FPU registers across IPC", test_fpu_ping_pong, true)

/* ---- 20-bit ASIDs (DESIGN.md §3) ------------------------------------- */

static int add_one(seL4_Word a, seL4_Word b, seL4_Word c, seL4_Word d)
{
    return a + 1;
}

/*
 * Make 200 ASID pools: the last one's ASIDs are above 2^16, past what
 * seL4 has, so a process there runs on a PCID of its core's cache and its
 * mapping caps carry the high ASID bits. Remapping a frame checks that its
 * cap still names the process's ASID.
 */
#ifdef CONFIG_ARCH_AARCH64
/* AArch64 has 16-bit ASIDs (l4h 0016): 128 pools. Make all the rest, so a
 * process in the last one runs with an ASID near 2^16. */
#define ASID_POOLS 127
#else
#define ASID_POOLS 200
#endif

static int test_high_asids(env_t env)
{
    seL4_CPtr pool = 0;
    for (int i = 0; i < ASID_POOLS; i++) {
        seL4_CPtr ut = vka_alloc_untyped_leaky(&env->vka, seL4_ASIDPoolBits);
        test_assert(ut);
        cspacepath_t path;
        test_eq(vka_cspace_alloc_path(&env->vka, &path), 0);
        test_eq(ASID_MAKE_POOL(env->asid_ctrl, ut, env->cspace_root, path.capPtr, path.capDepth),
                seL4_NoError);
        pool = path.capPtr;
    }
    helper_thread_t t;
    create_helper_process_custom_asid(env, &t, pool);
    void *v = vspace_new_pages(&t.process.vspace, seL4_AllRights, 1, seL4_PageBits);
    test_assert(v != NULL);
    seL4_CPtr frame = vspace_get_cap(&t.process.vspace, v);
    test_eq(PAGE_MAP(frame, t.process.pd.cptr, (seL4_Word) v, seL4_AllRights, DEFAULT_ATTR),
            seL4_NoError);
    start_helper(env, &t, add_one, 41, 0, 0, 0);
    test_eq(wait_for_helper(&t), 42);
    cleanup_helper(env, &t);
    return sel4test_get_result();
}
DEFINE_TEST(FL4ASID0001, "A process with an ASID in the last pool runs, and its mapping caps keep the ASID", test_high_asids, true)

/* ---- A deleted address space stops its threads on other cores -------- */

/* About 0.1 s of the counter rdtsc reads. */
static uint64_t settle_ticks(void)
{
#ifdef CONFIG_ARCH_AARCH64
    uint64_t f;
    __asm__ volatile("mrs %0, cntfrq_el0" : "=r"(f));
    return f / 10;
#else
    return 200000000ull;
#endif
}
#define SETTLE_TICKS settle_ticks()

static int spin_count(seL4_Word addr, seL4_Word b, seL4_Word c, seL4_Word d)
{
    volatile seL4_Word *p = (volatile seL4_Word *) addr;
    for (;;) {
        *p = *p + 1;
    }
    return 0;
}

/* The counter once it moves past `from`, or `from` after `ticks`. */
static seL4_Word count_after(volatile seL4_Word *p, seL4_Word from, uint64_t ticks)
{
    uint64_t end = rdtsc() + ticks;
    while (*p == from && rdtsc() < end) {
    }
    return *p;
}

/*
 * A thread runs alone on another core while its VSpace is deleted by
 * revoking the cap its TCB's copy was derived from, which reaches the TCB
 * without a TCB invocation. The core must stop using the deleted tables
 * (the thread then faults); running on would let it walk them after their
 * memory is reused.
 */
static int test_deleted_vspace_on_other_core(env_t env)
{
    if (env->cores < 2) {
        return sel4test_get_result();
    }
    helper_thread_t t;
    create_helper_process(env, &t);
    /* Its fault, once the VSpace is gone, goes where no one waits. */
    seL4_CPtr fault_ep = vka_alloc_endpoint_leaky(&env->vka);
    test_error_eq(api_tcb_set_space(get_helper_tcb(&t), fault_ep, t.process.cspace.cptr,
                                    api_make_guard_skip_word(seL4_WordBits - t.process.cspace_size),
                                    t.process.pd.cptr, seL4_NilData), seL4_NoError);
    seL4_CPtr fcap;
    volatile seL4_Word *counter = map_frame(env, &fcap);
    test_assert(counter != NULL);
    *counter = 0;
    void *there = vspace_share_mem(&env->vspace, &t.process.vspace, (void *) counter, 1, seL4_PageBits,
                                   seL4_AllRights, true);
    test_assert(there != NULL);
    set_helper_affinity(env, &t, 1);
    start_helper(env, &t, spin_count, (seL4_Word) there, 0, 0, 0);
    test_assert(count_after(counter, 0, 50 * SETTLE_TICKS) != 0);

    test_error_eq(seL4_CNode_Revoke(env->cspace_root, t.process.pd.cptr, seL4_WordBits), seL4_NoError);
    test_error_eq(seL4_CNode_Delete(env->cspace_root, t.process.pd.cptr, seL4_WordBits), seL4_NoError);
    seL4_Word before = count_after(counter, (seL4_Word) -1, SETTLE_TICKS);
    seL4_Word after = count_after(counter, before, 5 * SETTLE_TICKS);
    test_eq(after, before);

    /* The process cannot be torn down without its VSpace: stop and leak it. */
    test_error_eq(seL4_TCB_Suspend(get_helper_tcb(&t)), seL4_NoError);
    return sel4test_get_result();
}
DEFINE_TEST(FL4ASID0002, "A VSpace deleted while its thread runs on another core stops that thread",
            test_deleted_vspace_on_other_core, true)

#ifdef CONFIG_ARCH_X86_64
/* ---- Unmap of PAT mappings ------------------------------------------- */

static int read_byte(seL4_Word addr, seL4_Word b, seL4_Word c, seL4_Word d)
{
    return *(volatile uint8_t *) addr;
}

/*
 * A 4 KiB mapping with the PAT bit (write-combining) is really unmapped:
 * bit 7 of a 4K entry is PAT, which FL4 once mistook for the large-page
 * bit and left the entry in place.
 */
static int test_unmap_pat(env_t env)
{
    seL4_CPtr fcap;
    volatile uint8_t *page = map_frame(env, &fcap);
    test_assert(page != NULL);
    test_error_eq(remap(env, fcap, (void *) page, seL4_X86_WriteCombining), seL4_NoError);
    page[0] = 1;
    test_error_eq(seL4_X86_Page_Unmap(fcap), seL4_NoError);

    helper_thread_t t;
    vka_object_t reply;
    test_error_eq(vka_alloc_reply(&env->vka, &reply), 0);
    seL4_CPtr fault_ep = vka_alloc_endpoint_leaky(&env->vka);
    create_helper_thread(env, &t);
    int error = api_tcb_set_space(get_helper_tcb(&t), fault_ep, env->cspace_root,
                                  api_make_guard_skip_word(seL4_WordBits - env->cspace_size_bits),
                                  env->page_directory, seL4_NilData);
    test_error_eq(error, seL4_NoError);
    start_helper(env, &t, read_byte, (seL4_Word) page, 0, 0, 0);
    seL4_Word badge;
    seL4_MessageInfo_t tag = api_recv(fault_ep, &badge, reply.cptr);
    test_eq(seL4_MessageInfo_get_label(tag), (seL4_Word) seL4_Fault_VMFault);
    test_eq(seL4_GetMR(seL4_VMFault_Addr), (seL4_Word) page);
    cleanup_helper(env, &t);
    return sel4test_get_result();
}
DEFINE_TEST(FL4VM0005, "Unmapping a 4K page mapped with PAT removes the mapping", test_unmap_pat, true)

/* ---- Security audit: debug exceptions and FS/GS bases at the boundary - */

#define RFLAGS_TF 0x100
#define FL4_DONE_LABEL 0x7d

/* Give `t` `fault_ep` as its fault handler. */
static int set_fault_ep(env_t env, helper_thread_t *t, seL4_CPtr fault_ep)
{
    return api_tcb_set_space(get_helper_tcb(t), fault_ep, env->cspace_root,
                             api_make_guard_skip_word(seL4_WordBits - env->cspace_size_bits),
                             env->page_directory, seL4_NilData);
}

static void reply_to(seL4_CPtr reply, seL4_MessageInfo_t info)
{
#ifdef CONFIG_KERNEL_MCS
    seL4_Send(reply, info);
#else
    (void) reply;
    seL4_Reply(info);
#endif
}

/* Answer a single-step or breakpoint fault so the thread goes on without
 * stepping: with the debug API, stop single-stepping; without it (a plain
 * #DB UserException), resume after the trap with TF clear. Returns 0 if
 * `tag` was such a fault. */
static int resume_after_debug_fault(seL4_MessageInfo_t tag, seL4_CPtr reply)
{
    seL4_Word label = seL4_MessageInfo_get_label(tag);
#ifdef CONFIG_HARDWARE_DEBUG_API
    if (label == seL4_Fault_DebugException) {
        seL4_SetMR(0, 0);
        reply_to(reply, seL4_MessageInfo_new(0, 0, 0, 1));
        return 0;
    }
#endif
    if (label == seL4_Fault_UserException && seL4_GetMR(seL4_UserException_Number) == 1) {
        seL4_Word ip = seL4_GetMR(seL4_UserException_FaultIP);
        seL4_Word sp = seL4_GetMR(seL4_UserException_SP);
        seL4_Word flags = seL4_GetMR(seL4_UserException_FLAGS) & ~(seL4_Word) RFLAGS_TF;
        seL4_SetMR(seL4_UserException_FaultIP, ip);
        seL4_SetMR(seL4_UserException_SP, sp);
        seL4_SetMR(seL4_UserException_FLAGS, flags);
        reply_to(reply, seL4_MessageInfo_new(0, 0, 0, 3));
        return 0;
    }
    return -1;
}

/* Set TF itself: the next instruction raises #DB from user mode, on the
 * #DB IST stack. */
static int set_trap_flag(seL4_Word a, seL4_Word b, seL4_Word c, seL4_Word d)
{
    __asm__ volatile("pushfq\n\torq $0x100, (%%rsp)\n\tpopfq\n\tnop" ::: "memory", "cc");
    return 0x5a5a;
}

/* A user #DB on another core is that core's entry: the kernel must not run
 * it as core 0 (whose current thread, state and gate slot it would use). */
static int test_user_debug_trap_on_ap(env_t env)
{
    helper_thread_t t;
    vka_object_t reply;
    test_error_eq(vka_alloc_reply(&env->vka, &reply), 0);
    seL4_CPtr fault_ep = vka_alloc_endpoint_leaky(&env->vka);
    create_helper_thread(env, &t);
    test_error_eq(set_fault_ep(env, &t, fault_ep), seL4_NoError);
    if (env->cores >= 2) {
        set_helper_affinity(env, &t, 1);
    }
    start_helper(env, &t, set_trap_flag, 0, 0, 0, 0);
    seL4_Word badge;
    seL4_MessageInfo_t tag = api_recv(fault_ep, &badge, reply.cptr);
#ifdef CONFIG_HARDWARE_DEBUG_API
    test_eq(seL4_MessageInfo_get_label(tag), (seL4_Word) seL4_Fault_DebugException);
    test_eq(seL4_GetMR(seL4_DebugException_ExceptionReason), (seL4_Word) seL4_SingleStep);
#else
    test_eq(seL4_MessageInfo_get_label(tag), (seL4_Word) seL4_Fault_UserException);
    test_eq(seL4_GetMR(seL4_UserException_Number), (seL4_Word) 1);
#endif
    test_eq(resume_after_debug_fault(tag, reply.cptr), 0);
    test_eq(wait_for_helper(&t), 0x5a5a);
    cleanup_helper(env, &t);
    return sel4test_get_result();
}
DEFINE_TEST(FL4SMP0002, "A user-set trap flag on another core faults on that core", test_user_debug_trap_on_ap, true)

/* The selector MOV SS loads, under a data breakpoint. */
static volatile uint16_t fl4_ss_selector = 0x2b;

/* Path 0: single-step a SYSCALL. Path 1: MOV SS from a watched word, then
 * SYSCALL, so the #DB the CPU holds back for MOV SS arrives after SYSCALL
 * has switched to kernel mode (CVE-2018-8897). Either #DB belongs to user
 * mode; the thread then says it is done on `done_ep`. */
static int debug_across_syscall(seL4_Word path, seL4_Word done_ep, seL4_Word c, seL4_Word d)
{
    seL4_Word rax = 0;
    if (path == 0) {
        __asm__ volatile("pushfq\n\torq $0x100, (%%rsp)\n\tpopfq\n\tsyscall"
                         : "+a"(rax) : "d"((seL4_Word) seL4_SysYield) : "rcx", "r11", "memory", "cc");
    } else {
        __asm__ volatile("movw (%1), %%ss\n\tsyscall"
                         : "+a"(rax) : "r"(&fl4_ss_selector), "d"((seL4_Word) seL4_SysYield)
                         : "rcx", "r11", "memory");
    }
    seL4_Send(done_ep, seL4_MessageInfo_new(FL4_DONE_LABEL, 0, 0, 0));
    return 0x7e57;
}

/* A kernel-mode #DB at the SYSCALL entry is user mode's: the kernel goes
 * on with the syscall instead of stopping at a kernel exception. */
static int test_debug_across_syscall(env_t env)
{
    int paths = 1;
#ifdef CONFIG_HARDWARE_DEBUG_API
    paths = 2;
#endif
    for (int path = 0; path < paths; path++) {
        helper_thread_t t;
        vka_object_t reply;
        test_error_eq(vka_alloc_reply(&env->vka, &reply), 0);
        seL4_CPtr fault_ep = vka_alloc_endpoint_leaky(&env->vka);
        create_helper_thread(env, &t);
        test_error_eq(set_fault_ep(env, &t, fault_ep), seL4_NoError);
#ifdef CONFIG_HARDWARE_DEBUG_API
        if (path == 1) {
            int err = seL4_TCB_SetBreakpoint(get_helper_tcb(&t), 0, (seL4_Word) &fl4_ss_selector,
                                             seL4_DataBreakpoint, 2, seL4_BreakOnReadWrite);
            test_error_eq(err, seL4_NoError);
        }
#endif
        start_helper(env, &t, debug_across_syscall, path, fault_ep, 0, 0);
        /* Debug faults, if the CPU reports the #DB in user mode, then done. */
        for (int faults = 0; ; faults++) {
            test_assert(faults < 4);
            seL4_Word badge;
            seL4_MessageInfo_t tag = api_recv(fault_ep, &badge, reply.cptr);
            if (seL4_MessageInfo_get_label(tag) == FL4_DONE_LABEL) {
                break;
            }
            test_eq(resume_after_debug_fault(tag, reply.cptr), 0);
        }
        test_eq(wait_for_helper(&t), 0x7e57);
        cleanup_helper(env, &t);
    }
    return sel4test_get_result();
}
DEFINE_TEST(FL4DBG0001, "A #DB held across SYSCALL (single step, MOV SS) is not a kernel fault",
            test_debug_across_syscall, true)

/* Raw syscalls that touch no thread-local storage: these threads run with
 * an FS base that is not their TLS. */
static inline __attribute__((always_inline)) void raw_recv(seL4_Word ep, seL4_Word reply)
{
    register seL4_Word r12 __asm__("r12") = reply;
    seL4_Word src = ep, info;
    __asm__ volatile("movq %%rsp, %%rbx\n\tsyscall\n\tmovq %%rbx, %%rsp"
                     : "+D"(src), "=S"(info)
                     : "d"((seL4_Word) seL4_SysRecv), "r"(r12)
                     : "rbx", "rcx", "r11", "r10", "r8", "r9", "r15", "memory");
}

static inline __attribute__((always_inline)) void raw_send(seL4_Word ep, seL4_Word mr0)
{
    register seL4_Word r10 __asm__("r10") = mr0;
    __asm__ volatile("movq %%rsp, %%rbx\n\tsyscall\n\tmovq %%rbx, %%rsp"
                     :
                     : "d"((seL4_Word) seL4_SysSend), "D"(ep), "S"(seL4_MessageInfo_new(0, 0, 0, 1).words[0]), "r"(r10)
                     : "rbx", "rcx", "r11", "memory");
}

/* Waits for `go`, loads FS with a selector (which sets the hidden base to
 * the descriptor's, 0), then wakes the reader. */
__attribute__((no_stack_protector))
static int fs_clobberer(seL4_Word ready, seL4_Word go, seL4_Word reply, seL4_Word next)
{
    seL4_Send(ready, seL4_MessageInfo_new(0, 0, 0, 0));
    raw_recv(go, reply);
    __asm__ volatile("movw %0, %%fs" : : "r"((uint16_t) 0x2b));
    raw_send(next, 0);
    raw_recv(go, reply);
    return 0;
}

/* Waits to be woken, then reads the word at its FS base and sends it. */
__attribute__((no_stack_protector))
static int fs_reader(seL4_Word ready, seL4_Word go, seL4_Word reply, seL4_Word result)
{
    seL4_Send(ready, seL4_MessageInfo_new(0, 0, 0, 0));
    raw_recv(go, reply);
    seL4_Word v;
    __asm__ volatile("movq %%fs:0, %0" : "=r"(v));
    raw_send(result, v);
    raw_recv(go, reply);
    return 0;
}

/* Two threads with the same FS base: the first changes its hidden FS base
 * by loading a selector (which needs no FSGSBASE), then switches to the
 * second, which must run with the base it was given. */
static int test_fs_base_after_selector_load(env_t env)
{
    const uint64_t magic = 0x1122334455667788ULL;
    seL4_CPtr fcap;
    uint64_t *page = map_frame(env, &fcap);
    test_assert(page != NULL);
    page[0] = magic;
    seL4_CPtr ready = vka_alloc_endpoint_leaky(&env->vka);
    seL4_CPtr go1 = vka_alloc_endpoint_leaky(&env->vka);
    seL4_CPtr go2 = vka_alloc_endpoint_leaky(&env->vka);
    seL4_CPtr result = vka_alloc_endpoint_leaky(&env->vka);
    vka_object_t r1, r2, rmain;
    test_error_eq(vka_alloc_reply(&env->vka, &r1), 0);
    test_error_eq(vka_alloc_reply(&env->vka, &r2), 0);
    test_error_eq(vka_alloc_reply(&env->vka, &rmain), 0);
    helper_thread_t t1, t2;
    create_helper_thread(env, &t1);
    create_helper_thread(env, &t2);
    /* A fault of the reader (reading through a stale base) comes here too. */
    test_error_eq(set_fault_ep(env, &t2, result), seL4_NoError);
    /* Below this thread: once it waits for the result, only they run on
     * this core, the reader right after the writer. */
    set_helper_priority(env, &t1, env->priority - 1);
    set_helper_priority(env, &t2, env->priority - 1);
    start_helper(env, &t2, fs_reader, ready, go2, r2.cptr, result);
    start_helper(env, &t1, fs_clobberer, ready, go1, r1.cptr, go2);
    seL4_Word badge;
    api_recv(ready, &badge, rmain.cptr);
    api_recv(ready, &badge, rmain.cptr);
    /* Both are past their last use of their TLS. */
    test_error_eq(seL4_TCB_SetTLSBase(get_helper_tcb(&t1), (seL4_Word) page), seL4_NoError);
    test_error_eq(seL4_TCB_SetTLSBase(get_helper_tcb(&t2), (seL4_Word) page), seL4_NoError);
    seL4_Send(go1, seL4_MessageInfo_new(0, 0, 0, 0));
    seL4_MessageInfo_t tag = api_recv(result, &badge, rmain.cptr);
    test_eq(seL4_MessageInfo_get_label(tag), (seL4_Word) 0);
    test_eq((uint64_t) seL4_GetMR(0), magic);
    cleanup_helper(env, &t1);
    cleanup_helper(env, &t2);
    return sel4test_get_result();
}
DEFINE_TEST(FL4TLS0001, "A selector load in one thread does not change the FS base of the next",
            test_fs_base_after_selector_load, true)
#endif

#ifdef CONFIG_ARCH_AARCH64
/* ---- TCR_EL1.TBI0: tagged EL0 pointers ------------------------------ */

/* EL0 data addresses ignore their top byte: a store through a tagged
 * pointer and a load through the plain one (and the other way round)
 * reach the same word. */
static int test_tbi0(env_t env)
{
    seL4_CPtr fcap;
    volatile seL4_Word *page = map_frame(env, &fcap);
    test_assert(page != NULL);
    volatile seL4_Word *tagged = (volatile seL4_Word *)((uintptr_t) page | (0xabull << 56));
    *tagged = 0x5eed;
    test_eq(page[0], (seL4_Word) 0x5eed);
    page[1] = 0xbeef;
    test_eq(tagged[1], (seL4_Word) 0xbeef);
    volatile seL4_Word *tagged2 = (volatile seL4_Word *)((uintptr_t) page | (0x01ull << 56));
    test_eq(tagged2[0], (seL4_Word) 0x5eed);
    return sel4test_get_result();
}
DEFINE_TEST(FL4TBI0001, "EL0 loads and stores ignore the top byte of the address (TCR_EL1.TBI0)", test_tbi0, true)

/* ---- seL4_TCB_SetPACKeys ---------------------------------------------- */

/* PACIA, PACDA, AUTIA, AUTDA x0, x1 as encodings (any assembler). */
#define PAC_OP(name, enc)                                                   \
    static seL4_Word name(seL4_Word p, seL4_Word m)                         \
    {                                                                       \
        register seL4_Word x0 __asm__("x0") = p;                            \
        register seL4_Word x1 __asm__("x1") = m;                            \
        __asm__ volatile(".inst " #enc : "+r"(x0) : "r"(x1) : "memory");   \
        return x0;                                                          \
    }
PAC_OP(pacia, 0xdac10020)
PAC_OP(pacda, 0xdac10820)
PAC_OP(autia, 0xdac11020)
PAC_OP(autda, 0xdac11820)

#define PAC_LABEL 0x9ac
/* A probe's load through a pointer that should not have authenticated did
 * not fault. */
#define PAC_NO_FAULT 0x9ad
/* Fixed modifiers, for checking that a thread signs the same before and
 * after others ran on its core. */
#define PAC_NMODS 4
static const seL4_Word pac_mods[PAC_NMODS] = {0x5a5a, 0x1234, 0xbeef, 0x7777};
/* A data pointer's code is only 7 bits (TBID0): a signature can be the
 * unsigned pointer, or two keys' signatures can agree, by chance (1 in 128).
 * Where the checks need a modifier for which they differ, they search
 * PAC_SEARCH modifiers from PAC_SEARCH_BASE, in order. */
#define PAC_SEARCH 64
#define PAC_SEARCH_BASE 0x10000

/* What the reply to a probe's report asks for next (MR 0). */
#define PAC_CMD_REPORT 0  /* report the fixed modifiers again */
#define PAC_CMD_SEARCH 1  /* data-sign with the search modifiers */
#define PAC_CMD_FINAL 2   /* authenticate MR 1 with modifier MR 2, load */
#define PAC_CMD_SEARCH_IA 3 /* instruction-sign with the search modifiers */

static seL4_Word pac_target;

/* The report: for every fixed modifier, &pac_target signed with the
 * instruction and data A keys; whether all of them authenticate (and the
 * data ones load pac_target); PACGA. */
static void pac_report_fixed(seL4_Word ep, seL4_Word ptr)
{
    seL4_Word ok = 1;
    for (int k = 0; k < PAC_NMODS; k++) {
        seL4_Word m = pac_mods[k];
        seL4_Word ia = pacia(ptr, m);
        seL4_Word da = pacda(ptr, m);
        seL4_SetMR(k, ia);
        seL4_SetMR(PAC_NMODS + k, da);
        if (autia(ia, m) != ptr || autda(da, m) != ptr || *(volatile seL4_Word *) autda(da, m) != pac_target) {
            ok = 0;
        }
    }
    seL4_SetMR(2 * PAC_NMODS, ok);
    seL4_SetMR(2 * PAC_NMODS + 1, pacga(ptr, pac_mods[0]));
    seL4_Call(ep, seL4_MessageInfo_new(PAC_LABEL, 0, 0, 2 * PAC_NMODS + 2));
}

/* Report, then do what each reply asks. The last step authenticates a
 * pointer (MR 1; 0: this thread's own data pointer with its code changed)
 * and loads through it: a fault, at the AUT itself with FEAT_FPAC. A load
 * that does not fault sends PAC_NO_FAULT on `ep`, where the test waits. */
static int pac_probe(seL4_Word ep, seL4_Word b, seL4_Word c, seL4_Word d)
{
    seL4_Word ptr = (seL4_Word) &pac_target;
    pac_report_fixed(ep, ptr);
    for (;;) {
        seL4_Word cmd = seL4_GetMR(0);
        if (cmd == PAC_CMD_REPORT) {
            pac_report_fixed(ep, ptr);
        } else if (cmd == PAC_CMD_SEARCH || cmd == PAC_CMD_SEARCH_IA) {
            for (int i = 0; i < PAC_SEARCH; i++) {
                seL4_Word m = PAC_SEARCH_BASE + i;
                seL4_SetMR(i, cmd == PAC_CMD_SEARCH ? pacda(ptr, m) : pacia(ptr, m));
            }
            seL4_Call(ep, seL4_MessageInfo_new(PAC_LABEL, 0, 0, PAC_SEARCH));
        } else {
            seL4_Word other = seL4_GetMR(1);
            seL4_Word m = seL4_GetMR(2);
            seL4_Word bad = other ? autda(other, m) : autda(pacda(ptr, m) ^ (1ull << 50), m);
            seL4_Word v = *(volatile seL4_Word *) bad;
            seL4_SetMR(0, v);
            seL4_Send(ep, seL4_MessageInfo_new(PAC_NO_FAULT, 0, 0, 1));
            return 0;
        }
    }
    return 0;
}

struct pac_report {
    seL4_Word ia[PAC_NMODS], da[PAC_NMODS], ok, ga;
};

static void pac_read(struct pac_report *r)
{
    for (int k = 0; k < PAC_NMODS; k++) {
        r->ia[k] = seL4_GetMR(k);
        r->da[k] = seL4_GetMR(PAC_NMODS + k);
    }
    r->ok = seL4_GetMR(2 * PAC_NMODS);
    r->ga = seL4_GetMR(2 * PAC_NMODS + 1);
}

/* Receive a message on `ep`; anything but a report (a fault) is printed. */
static seL4_Word pac_recv(seL4_CPtr ep, seL4_CPtr reply)
{
    seL4_Word badge;
    seL4_Word label = seL4_MessageInfo_get_label(api_recv(ep, &badge, reply));
    if (label != PAC_LABEL) {
        printf("FL4PAC0001: message %lu: %#lx %#lx %#lx %#lx %#lx\n", (unsigned long) label, (unsigned long) seL4_GetMR(0),
               (unsigned long) seL4_GetMR(1), (unsigned long) seL4_GetMR(2), (unsigned long) seL4_GetMR(3),
               (unsigned long) seL4_GetMR(4));
    }
    return label;
}

/* Reply to a probe's report with the next command. */
static void pac_reply(seL4_CPtr reply, seL4_Word cmd, seL4_Word x, seL4_Word y)
{
    seL4_SetMR(0, cmd);
    seL4_SetMR(1, x);
    seL4_SetMR(2, y);
    api_reply(reply, seL4_MessageInfo_new(0, 0, 0, 3));
}

/* A probe's data (or with `ia`, instruction) signatures with the search
 * modifiers (it waits in its Call after a report). */
static seL4_Word pac_search_cmd(seL4_CPtr ep, seL4_CPtr reply, seL4_Word *out, int ia)
{
    pac_reply(reply, ia ? PAC_CMD_SEARCH_IA : PAC_CMD_SEARCH, 0, 0);
    seL4_Word label = pac_recv(ep, reply);
    for (int i = 0; i < PAC_SEARCH; i++) {
        out[i] = seL4_GetMR(i);
    }
    return label;
}

static seL4_Word pac_search(seL4_CPtr ep, seL4_CPtr reply, seL4_Word *out)
{
    return pac_search_cmd(ep, reply, out, 0);
}

static seL4_Word pac_search_ia(seL4_CPtr ep, seL4_CPtr reply, seL4_Word *out)
{
    return pac_search_cmd(ep, reply, out, 1);
}

/* The first search modifier whose signatures in `x` and `y` differ, or -1. */
static int pac_first_differing(const seL4_Word *x, const seL4_Word *y, int n)
{
    for (int i = 0; i < n; i++) {
        if (x[i] != y[i]) {
            return i;
        }
    }
    return -1;
}

static int pac_thread(env_t env, helper_thread_t *t, seL4_CPtr ep, seL4_Word flags, seL4_Word k)
{
    create_helper_thread(env, t);
    int error = api_tcb_set_space(get_helper_tcb(t), ep, env->cspace_root,
                                  api_make_guard_skip_word(seL4_WordBits - env->cspace_size_bits),
                                  env->page_directory, seL4_NilData);
    if (error) {
        return error;
    }
    set_helper_affinity(env, t, 0);
    return seL4_TCB_SetPACKeys(get_helper_tcb(t), flags, k + 1, k + 2, k + 3, k + 4, k + 5, k + 6, k + 7, k + 8,
                               k + 9, k + 10);
}

#define PAC_ALL (seL4_ARM_PAC_EnIA | seL4_ARM_PAC_EnIB | seL4_ARM_PAC_EnDA | seL4_ARM_PAC_EnDB)

/* The last step of a probe waiting after a report: a fault expected. */
static void pac_expect_fault(seL4_CPtr ep, seL4_CPtr reply, seL4_Word other, seL4_Word m, const char *what)
{
    pac_reply(reply, PAC_CMD_FINAL, other, m);
    seL4_Word label = pac_recv(ep, reply);
    printf("FL4PAC0001: %s: message %lu\n", what, (unsigned long) label);
    test_check(label == seL4_Fault_VMFault || label == seL4_Fault_UserException);
}

/* Threads with their own keys sign differently, cannot authenticate each
 * other's pointers, and get their own keys back after others ran on the
 * core; a thread with pointer authentication off signs nothing and runs
 * PACGA with the zero key, as one that never had keys. */
static int test_pac_keys(env_t env)
{
    pac_target = 0x7a76e7;
    seL4_Word ptr = (seL4_Word) &pac_target;
    seL4_Word unsigned_ptrs[PAC_SEARCH];
    for (int i = 0; i < PAC_SEARCH; i++) {
        unsigned_ptrs[i] = ptr;
    }
    seL4_CPtr ep = vka_alloc_endpoint_leaky(&env->vka);
    vka_object_t reply;
    test_error_eq(vka_alloc_reply(&env->vka, &reply), 0);
    /* Argument checks. */
    test_error_eq(seL4_TCB_SetPACKeys(env->tcb, 0x10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0), seL4_InvalidArgument);
    int err = seL4_TCB_SetPACKeys(env->tcb, seL4_ARM_PAC_EnIA, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10);
    test_error_eq(seL4_TCB_SetPACKeys(env->tcb, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0), seL4_NoError);
    if (err == seL4_IllegalOperation) {
        printf("FL4PAC0001: no FEAT_PAuth\n");
        return sel4test_get_result();
    }
    test_error_eq(err, seL4_NoError);

    helper_thread_t d, a, b, c;
    struct pac_report rd, ra, rb, rb2, rc, ra2;
    seL4_Word sa[PAC_SEARCH], sb[PAC_SEARCH], sd[PAC_SEARCH];
    seL4_Word ia_a[PAC_SEARCH], ia_b[PAC_SEARCH], ia_a2[PAC_SEARCH], ia_d[PAC_SEARCH];
    vka_object_t reply_d, reply_b, reply_c;
    test_error_eq(vka_alloc_reply(&env->vka, &reply_d), 0);
    test_error_eq(vka_alloc_reply(&env->vka, &reply_b), 0);
    test_error_eq(vka_alloc_reply(&env->vka, &reply_c), 0);

    /* D: never had keys (the zero APGA key): signs nothing. */
    test_error_eq(pac_thread(env, &d, ep, 0, 0), seL4_NoError);
    start_helper(env, &d, pac_probe, ep, 0, 0, 0);
    test_eq(pac_recv(ep, reply_d.cptr), (seL4_Word) PAC_LABEL);
    pac_read(&rd);
    test_eq(rd.ok, (seL4_Word) 1);
    test_eq(pac_first_differing(rd.ia, unsigned_ptrs, PAC_NMODS), -1);
    test_eq(pac_first_differing(rd.da, unsigned_ptrs, PAC_NMODS), -1);
    test_eq(pac_search(ep, reply_d.cptr, sd), (seL4_Word) PAC_LABEL);
    test_eq(pac_first_differing(sd, unsigned_ptrs, PAC_SEARCH), -1);
    test_eq(pac_search_ia(ep, reply_d.cptr, ia_d), (seL4_Word) PAC_LABEL);
    test_eq(pac_first_differing(ia_d, unsigned_ptrs, PAC_SEARCH), -1);
    cleanup_helper(env, &d);

    /* A: its own keys, all four enables. */
    test_error_eq(pac_thread(env, &a, ep, PAC_ALL, 0x1000), seL4_NoError);
    start_helper(env, &a, pac_probe, ep, 0, 0, 0);
    test_eq(pac_recv(ep, reply.cptr), (seL4_Word) PAC_LABEL);
    pac_read(&ra);
    printf("FL4PAC0001: A signs %#lx as %#lx (I) %#lx (D)\n", (unsigned long) ptr, (unsigned long) ra.ia[0],
           (unsigned long) ra.da[0]);
    test_eq(ra.ok, (seL4_Word) 1);
    if (pac_first_differing(ra.ia, unsigned_ptrs, PAC_NMODS) < 0) {
        printf("FL4PAC0001: A's instruction signatures with the fixed modifiers all came out unsigned\n");
    }
    test_check(ra.ga != rd.ga);
    test_eq(pac_search(ep, reply.cptr, sa), (seL4_Word) PAC_LABEL);
    int ka = pac_first_differing(sa, unsigned_ptrs, PAC_SEARCH);
    if (ka < 0) {
        printf("FL4PAC0001: A's data signatures all came out unsigned: not checked\n");
    }
    /* A's instruction (APIA) signatures: signed. */
    test_eq(pac_search_ia(ep, reply.cptr, ia_a), (seL4_Word) PAC_LABEL);
    if (pac_first_differing(ia_a, unsigned_ptrs, PAC_SEARCH) < 0) {
        printf("FL4PAC0001: A's APIA signatures all came out unsigned: not checked\n");
    }

    /* A waits in its Call. B: other keys. */
    test_error_eq(pac_thread(env, &b, ep, PAC_ALL, 0x2000), seL4_NoError);
    start_helper(env, &b, pac_probe, ep, 0, 0, 0);
    test_eq(pac_recv(ep, reply_b.cptr), (seL4_Word) PAC_LABEL);
    pac_read(&rb);
    test_eq(rb.ok, (seL4_Word) 1);
    test_check(rb.ga != ra.ga);
    test_eq(pac_search(ep, reply_b.cptr, sb), (seL4_Word) PAC_LABEL);
    int kb = pac_first_differing(sb, sa, PAC_SEARCH);
    if (kb < 0) {
        printf("FL4PAC0001: B's data signatures all equal A's: the cross-key check is not covered\n");
    }
    /* B's instruction (APIA) signatures differ from A's: their APIA keys
     * are their own. */
    test_eq(pac_search_ia(ep, reply_b.cptr, ia_b), (seL4_Word) PAC_LABEL);
    if (pac_first_differing(ia_b, ia_a, PAC_SEARCH) < 0) {
        printf("FL4PAC0001: APIA cross-thread isolation uncovered\n");
    }
    /* B again: its own signatures. */
    pac_reply(reply_b.cptr, PAC_CMD_REPORT, 0, 0);
    test_eq(pac_recv(ep, reply_b.cptr), (seL4_Word) PAC_LABEL);
    pac_read(&rb2);
    test_eq(pac_first_differing(rb2.ia, rb.ia, PAC_NMODS), -1);
    test_eq(pac_first_differing(rb2.da, rb.da, PAC_NMODS), -1);
    /* A's data pointer, where B's signature differs from it, authenticated
     * with B's keys: a fault. */
    if (kb >= 0) {
        pac_expect_fault(ep, reply_b.cptr, sa[kb], PAC_SEARCH_BASE + kb, "A's pointer with B's keys");
    }
    cleanup_helper(env, &b);

    /* C: keys set, then pointer authentication off. */
    test_error_eq(pac_thread(env, &c, ep, PAC_ALL, 0x3000), seL4_NoError);
    test_error_eq(seL4_TCB_SetPACKeys(get_helper_tcb(&c), 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1), seL4_NoError);
    start_helper(env, &c, pac_probe, ep, 0, 0, 0);
    test_eq(pac_recv(ep, reply_c.cptr), (seL4_Word) PAC_LABEL);
    pac_read(&rc);
    test_eq(rc.ok, (seL4_Word) 1);
    test_eq(pac_first_differing(rc.ia, unsigned_ptrs, PAC_NMODS), -1);
    test_eq(pac_first_differing(rc.da, unsigned_ptrs, PAC_NMODS), -1);
    test_eq(rc.ga, rd.ga);
    /* AUTDA does nothing there: A's signed pointer stays signed, and the
     * load through it faults. */
    if (ka >= 0) {
        pac_reply(reply_c.cptr, PAC_CMD_FINAL, sa[ka], PAC_SEARCH_BASE + ka);
        test_eq(pac_recv(ep, reply_c.cptr), (seL4_Word) seL4_Fault_VMFault);
    }
    cleanup_helper(env, &c);

    /* A again, after B and C ran on its core: its own keys. */
    pac_reply(reply.cptr, PAC_CMD_REPORT, 0, 0);
    test_eq(pac_recv(ep, reply.cptr), (seL4_Word) PAC_LABEL);
    pac_read(&ra2);
    test_eq(ra2.ok, (seL4_Word) 1);
    test_eq(pac_first_differing(ra2.ia, ra.ia, PAC_NMODS), -1);
    test_eq(pac_first_differing(ra2.da, ra.da, PAC_NMODS), -1);
    test_eq(ra2.ga, ra.ga);
    /* And all of A's APIA signatures, after B's key ran on its core. */
    test_eq(pac_search_ia(ep, reply.cptr, ia_a2), (seL4_Word) PAC_LABEL);
    test_eq(pac_first_differing(ia_a2, ia_a, PAC_SEARCH), -1);
    /* A tampered pointer: a fault (at the load, or at AUTDA with FPAC). */
    pac_expect_fault(ep, reply.cptr, 0, pac_mods[0], "A's tampered pointer");
    cleanup_helper(env, &a);
    return sel4test_get_result();
}
DEFINE_TEST(FL4PAC0001, "TCB_SetPACKeys: per-thread keys and enables, switched with the thread", test_pac_keys, true)

/* ---- ArmHighVSpace: EL0 mappings in the TTBR1 half -------------------- */

static int read_word(seL4_Word addr, seL4_Word b, seL4_Word c, seL4_Word d)
{
    return (int) *(volatile seL4_Word *) addr;
}

#define HIGH_LABEL 0x41

/* In the window: store and load word 1, run the code at +0x800, read word
 * 0 (the test's), report; after the reply load word 1 again. */
static int high_probe(seL4_Word ep, seL4_Word base, seL4_Word c, seL4_Word d)
{
    volatile seL4_Word *p = (volatile seL4_Word *) base;
    p[1] = 0x1234;
    seL4_Word r = p[1];
    seL4_Word code = ((seL4_Word(*)(void))(base + 0x800))();
    seL4_SetMR(0, r);
    seL4_SetMR(1, code);
    seL4_SetMR(2, p[0]);
    seL4_Call(ep, seL4_MessageInfo_new(HIGH_LABEL, 0, 0, 3));
    return (int) p[1];
}

/* An ArmHighVSpace, retyped from an untyped of its size (vka does not
 * know the type). */
static int alloc_high_vspace(env_t env, vka_object_t *o)
{
    seL4_CPtr ut = vka_alloc_untyped_leaky(&env->vka, seL4_ARM_HighVSpaceBits);
    if (!ut) {
        return -1;
    }
    cspacepath_t path;
    if (vka_cspace_alloc_path(&env->vka, &path)) {
        return -1;
    }
    o->cptr = path.capPtr;
    return seL4_Untyped_Retype(ut, seL4_ARM_HighVSpaceObject, seL4_ARM_HighVSpaceBits, path.root, path.dest,
                               path.destDepth, path.offset, 1);
}

static int fault_thread(env_t env, helper_thread_t *t, seL4_CPtr ep)
{
    create_helper_thread(env, t);
    set_helper_affinity(env, t, 0);
    return api_tcb_set_space(get_helper_tcb(t), ep, env->cspace_root,
                             api_make_guard_skip_word(seL4_WordBits - env->cspace_size_bits),
                             env->page_directory, seL4_NilData);
}

/* A thread with an ArmHighVSpace reads, writes and runs its pages in the
 * TTBR1 half at EL0. No other thread sees them: not one on another
 * VSpace, not one on the same VSpace without the window (same TTBR0 ASID,
 * right after it on its core), not the thread itself once a page is
 * unmapped. */
static int test_high_vspace(env_t env)
{
    const seL4_Word base = seL4_ARM_HighVSpaceBase;
    vka_object_t hv, l2, l3;
    test_error_eq(alloc_high_vspace(env, &hv), 0);
    test_error_eq(seL4_ARM_ASIDPool_Assign(env->asid_pool, hv.cptr), seL4_NoError);
    test_error_eq(vka_alloc_page_table(&env->vka, &l2), 0);
    test_error_eq(vka_alloc_page_table(&env->vka, &l3), 0);
    /* Only inside the window. */
    test_error_eq(seL4_ARM_PageTable_Map(l2.cptr, hv.cptr, base - (1ull << 30), seL4_ARM_Default_VMAttributes),
                  seL4_InvalidArgument);
    test_error_eq(seL4_ARM_PageTable_Map(l2.cptr, hv.cptr, seL4_ARM_HighVSpaceTop, seL4_ARM_Default_VMAttributes),
                  seL4_InvalidArgument);
    test_error_eq(seL4_ARM_PageTable_Map(l2.cptr, hv.cptr, base, seL4_ARM_Default_VMAttributes), seL4_NoError);
    test_error_eq(seL4_ARM_PageTable_Map(l3.cptr, hv.cptr, base, seL4_ARM_Default_VMAttributes), seL4_NoError);

    /* One frame, also mapped here: word 0 for the thread to read, code at +0x800. */
    seL4_CPtr fcap;
    volatile seL4_Word *low = map_frame(env, &fcap);
    test_assert(low != NULL);
    low[0] = 0xfeed;
    low[1] = 0;
    const uint32_t code[] = {0xd2800ee0, 0xd65f03c0}; /* mov x0, #0x77; ret */
    memcpy((void *)((uintptr_t) low + 0x800), code, sizeof(code));
    cspacepath_t copy, src;
    test_eq(vka_cspace_alloc_path(&env->vka, &copy), 0);
    vka_cspace_make_path(&env->vka, fcap, &src);
    test_eq(vka_cnode_copy(&copy, &src, seL4_AllRights), seL4_NoError);
    test_error_eq(seL4_ARM_Page_Map(copy.capPtr, hv.cptr, base - 0x1000, seL4_AllRights, seL4_ARM_Default_VMAttributes),
                  seL4_InvalidArgument);
    test_error_eq(seL4_ARM_Page_Map(copy.capPtr, hv.cptr, seL4_ARM_HighVSpaceTop, seL4_AllRights,
                                    seL4_ARM_Default_VMAttributes), seL4_InvalidArgument);
    test_error_eq(seL4_ARM_Page_Map(copy.capPtr, hv.cptr, base, seL4_AllRights, seL4_ARM_Default_VMAttributes),
                  seL4_NoError);
    test_error_eq(seL4_ARM_Page_Unify_Instruction(copy.capPtr, 0x800, 0x808), seL4_NoError);
    /* Not a window, or not assigned: refused. */
    vka_object_t hv2;
    test_error_eq(alloc_high_vspace(env, &hv2), 0);
    test_error_eq(seL4_TCB_SetHighVSpace(env->tcb, fcap), seL4_InvalidCapability);
    test_error_eq(seL4_TCB_SetHighVSpace(env->tcb, hv2.cptr), seL4_InvalidCapability);

    seL4_CPtr ep = vka_alloc_endpoint_leaky(&env->vka);
    vka_object_t reply;
    test_error_eq(vka_alloc_reply(&env->vka, &reply), 0);
    seL4_Word badge;
    /* K: the window. */
    helper_thread_t k;
    test_error_eq(fault_thread(env, &k, ep), seL4_NoError);
    test_error_eq(seL4_TCB_SetHighVSpace(get_helper_tcb(&k), hv.cptr), seL4_NoError);
    start_helper(env, &k, high_probe, ep, base, 0, 0);
    seL4_MessageInfo_t tag = api_recv(ep, &badge, reply.cptr);
    test_eq(seL4_MessageInfo_get_label(tag), (seL4_Word) HIGH_LABEL);
    test_eq(seL4_GetMR(0), (seL4_Word) 0x1234);
    test_eq(seL4_GetMR(1), (seL4_Word) 0x77);
    test_eq(seL4_GetMR(2), (seL4_Word) 0xfeed);
    test_eq(low[1], (seL4_Word) 0x1234);

    /* K2: the same VSpace (and ASID), no window, on K's core after it. */
    helper_thread_t k2;
    vka_object_t reply2;
    test_error_eq(vka_alloc_reply(&env->vka, &reply2), 0);
    test_error_eq(fault_thread(env, &k2, ep), seL4_NoError);
    start_helper(env, &k2, read_word, base, 0, 0, 0);
    tag = api_recv(ep, &badge, reply2.cptr);
    test_eq(seL4_MessageInfo_get_label(tag), (seL4_Word) seL4_Fault_VMFault);
    test_eq(seL4_GetMR(seL4_VMFault_Addr), base);
    cleanup_helper(env, &k2);

    /* U: another VSpace, no window. */
    helper_thread_t u;
    create_helper_process(env, &u);
    set_helper_affinity(env, &u, 0);
    test_error_eq(api_tcb_set_space(get_helper_tcb(&u), ep, u.process.cspace.cptr,
                                    api_make_guard_skip_word(seL4_WordBits - u.process.cspace_size),
                                    u.process.pd.cptr, seL4_NilData), seL4_NoError);
    vka_object_t reply3;
    test_error_eq(vka_alloc_reply(&env->vka, &reply3), 0);
    start_helper(env, &u, read_word, base, 0, 0, 0);
    tag = api_recv(ep, &badge, reply3.cptr);
    test_eq(seL4_MessageInfo_get_label(tag), (seL4_Word) seL4_Fault_VMFault);
    test_eq(seL4_GetMR(seL4_VMFault_Addr), base);
    cleanup_helper(env, &u);

    /* The page unmapped: K faults on it at once. */
    test_error_eq(seL4_ARM_Page_Unmap(copy.capPtr), seL4_NoError);
    api_reply(reply.cptr, seL4_MessageInfo_new(0, 0, 0, 0));
    tag = api_recv(ep, &badge, reply.cptr);
    test_eq(seL4_MessageInfo_get_label(tag), (seL4_Word) seL4_Fault_VMFault);
    test_eq(seL4_GetMR(seL4_VMFault_Addr), base + 8);
    cleanup_helper(env, &k);
    /* The window deleted with its last cap. */
    test_error_eq(seL4_CNode_Delete(env->cspace_root, hv.cptr, seL4_WordBits), seL4_NoError);
    return sel4test_get_result();
}
DEFINE_TEST(FL4HVS0001, "ArmHighVSpace: EL0 pages in the TTBR1 half, seen only by its thread", test_high_vspace, true)

/* Read the window's first word forever, counting the reads at `counter`
 * (atomically: the test reads it from another core). */
static int high_spin(seL4_Word base, seL4_Word counter, seL4_Word c, seL4_Word d)
{
    volatile seL4_Word *p = (volatile seL4_Word *) base;
    seL4_Word *n = (seL4_Word *) counter;
    for (;;) {
        (void) p[0];
        __atomic_fetch_add(n, 1, __ATOMIC_SEQ_CST);
    }
    return 0;
}

/* The count at `n` once it is past `from`, or after `ticks`. */
static seL4_Word atomic_count_after(seL4_Word *n, seL4_Word from, uint64_t ticks)
{
    uint64_t end = rdtsc() + ticks;
    seL4_Word v = __atomic_load_n(n, __ATOMIC_SEQ_CST);
    while (v == from && rdtsc() < end) {
        v = __atomic_load_n(n, __ATOMIC_SEQ_CST);
    }
    return v;
}

/* One run of FL4HVS0002: a thread on core 1 reads its window in a loop
 * while this core (0) takes the window from it, by unmapping its last page
 * table (`retire_pool` 0) or by deleting the window's ASID pool. Core 1
 * leaves the window before the invocation returns: its thread faults on its
 * next read of the window, having counted at most the one read it had
 * already made. */
static int high_retire_once(env_t env, int retire_pool)
{
    const seL4_Word base = seL4_ARM_HighVSpaceBase;
    seL4_CPtr pool = env->asid_pool;
    if (retire_pool) {
        seL4_CPtr ut = vka_alloc_untyped_leaky(&env->vka, seL4_ASIDPoolBits);
        test_assert(ut);
        cspacepath_t path;
        test_eq(vka_cspace_alloc_path(&env->vka, &path), 0);
        int e = ASID_MAKE_POOL(env->asid_ctrl, ut, env->cspace_root, path.capPtr, path.capDepth);
        if (e == seL4_DeleteFirst) {
            printf("FL4HVS0002: no ASID pool left, pool deletion not run\n");
            return sel4test_get_result();
        }
        test_error_eq(e, seL4_NoError);
        pool = path.capPtr;
    }
    vka_object_t hv, l2, l3;
    test_error_eq(alloc_high_vspace(env, &hv), 0);
    test_error_eq(seL4_ARM_ASIDPool_Assign(pool, hv.cptr), seL4_NoError);
    test_error_eq(vka_alloc_page_table(&env->vka, &l2), 0);
    test_error_eq(vka_alloc_page_table(&env->vka, &l3), 0);
    test_error_eq(seL4_ARM_PageTable_Map(l2.cptr, hv.cptr, base, seL4_ARM_Default_VMAttributes), seL4_NoError);
    test_error_eq(seL4_ARM_PageTable_Map(l3.cptr, hv.cptr, base, seL4_ARM_Default_VMAttributes), seL4_NoError);
    seL4_CPtr hcap = vka_alloc_frame_leaky(&env->vka, seL4_PageBits);
    test_assert(hcap);
    test_error_eq(seL4_ARM_Page_Map(hcap, hv.cptr, base, seL4_AllRights, seL4_ARM_Default_VMAttributes), seL4_NoError);
    seL4_CPtr ccap;
    seL4_Word *counter = map_frame(env, &ccap);
    test_assert(counter != NULL);
    __atomic_store_n(counter, 0, __ATOMIC_SEQ_CST);

    seL4_CPtr ep = vka_alloc_endpoint_leaky(&env->vka);
    vka_object_t reply;
    test_error_eq(vka_alloc_reply(&env->vka, &reply), 0);
    helper_thread_t k;
    create_helper_thread(env, &k);
    test_error_eq(api_tcb_set_space(get_helper_tcb(&k), ep, env->cspace_root,
                                    api_make_guard_skip_word(seL4_WordBits - env->cspace_size_bits),
                                    env->page_directory, seL4_NilData), seL4_NoError);
    test_error_eq(seL4_TCB_SetHighVSpace(get_helper_tcb(&k), hv.cptr), seL4_NoError);
    set_helper_affinity(env, &k, 1);
    start_helper(env, &k, high_spin, base, (seL4_Word) counter, 0, 0);
    /* Core 1 reads the window. */
    test_assert(atomic_count_after(counter, 0, 50 * SETTLE_TICKS) != 0);

    if (retire_pool) {
        test_error_eq(seL4_CNode_Delete(env->cspace_root, pool, seL4_WordBits), seL4_NoError);
    } else {
        test_error_eq(seL4_ARM_PageTable_Unmap(l3.cptr), seL4_NoError);
    }
    seL4_Word at_retire = __atomic_load_n(counter, __ATOMIC_SEQ_CST);
    /* Its next read of the window faults (were it to run on, no fault
     * would come and the test would time out). */
    seL4_Word badge;
    seL4_MessageInfo_t tag = api_recv(ep, &badge, reply.cptr);
    test_eq(seL4_MessageInfo_get_label(tag), (seL4_Word) seL4_Fault_VMFault);
    test_eq(seL4_GetMR(seL4_VMFault_Addr), base);
    /* At most the one read already made when the window went is counted
     * after it; then nothing. */
    seL4_Word at_fault = __atomic_load_n(counter, __ATOMIC_SEQ_CST);
    test_leq(at_fault, at_retire + 1);
    test_eq(atomic_count_after(counter, at_fault, 5 * SETTLE_TICKS), at_fault);
    printf("FL4HVS0002: %s retired the window on core 1 after %lu reads (%lu at the fault)\n",
           retire_pool ? "pool deletion" : "page table unmap", (unsigned long) at_retire, (unsigned long) at_fault);
    cleanup_helper(env, &k);
    return sel4test_get_result();
}

static int test_high_vspace_retired_on_another_core(env_t env)
{
    if (env->cores < 2) {
        return sel4test_get_result();
    }
    high_retire_once(env, 0);
    high_retire_once(env, 1);
    return sel4test_get_result();
}
DEFINE_TEST(FL4HVS0002, "ArmHighVSpace: a window taken away on one core is left at once by another core running it",
            test_high_vspace_retired_on_another_core, true)

/* ---- FL4HVS0003: TLB isolation as windows and ASIDs alternate ---------- */

#define HVS_PING 0x77
#define HVS_MAGIC 0x600df00dull
#define HVS_ROUNDS 200

/* `rounds` times: read the window's first word and send it in a Call, so
 * the test's own thread (its own ASID, the kernel's TTBR1) runs in the
 * kernel between two reads. */
static int high_ping(seL4_Word ep, seL4_Word base, seL4_Word rounds, seL4_Word d)
{
    volatile seL4_Word *p = (volatile seL4_Word *) base;
    for (seL4_Word i = 0; i < rounds; i++) {
        seL4_SetMR(0, p[0]);
        seL4_Call(ep, seL4_MessageInfo_new(HVS_PING, 0, 0, 1));
    }
    return 0;
}

#define HVS_BAD_VALUE 0x78
#define HVS_NO_FAULT 0x79

/* One link of FL4HVS0003's chain: wait for the previous link on `in` (0:
 * none, the first), read the window unless `read` is 0 (a link without the
 * window), hand over to the next link on `out` with a Send, then park on
 * `park` for good. A link that reads a wrong value sends HVS_BAD_VALUE on
 * `report`; the last link (no `out`) sends HVS_NO_FAULT there if its read
 * does not fault. No other thread runs between two links on the core: the
 * test's own thread waits on `report`. */
/* The CPtrs come in pairs, 32 bits each: `io` in and out, `pr` park and
 * report, all in the link's own CSpace. */
static int hvs_chain_link(seL4_Word io, seL4_Word pr, seL4_Word base, seL4_Word read)
{
    seL4_CPtr in = io & 0xffffffff, out = io >> 32;
    seL4_CPtr park = pr & 0xffffffff, report = pr >> 32;
    seL4_Word badge;
    if (in) {
        seL4_Wait(in, &badge);
    }
    if (read) {
        seL4_Word v = *(volatile seL4_Word *) base;
        if (!out) {
            seL4_SetMR(0, v);
            seL4_Send(report, seL4_MessageInfo_new(HVS_NO_FAULT, 0, 0, 1));
        } else if (v != HVS_MAGIC) {
            seL4_SetMR(0, v);
            seL4_Send(report, seL4_MessageInfo_new(HVS_BAD_VALUE, 0, 0, 1));
        }
    }
    if (out) {
        seL4_Send(out, seL4_MessageInfo_new(0, 0, 0, 0));
    }
    seL4_Wait(park, &badge);
    return 0;
}

/* A window assigned from the test's pool with HVS_MAGIC in its first word
 * at seL4_ARM_HighVSpaceBase. */
static int make_window(env_t env, vka_object_t *hv)
{
    const seL4_Word base = seL4_ARM_HighVSpaceBase;
    vka_object_t l2, l3;
    int e = alloc_high_vspace(env, hv);
    e = e ? e : seL4_ARM_ASIDPool_Assign(env->asid_pool, hv->cptr);
    e = e ? e : vka_alloc_page_table(&env->vka, &l2);
    e = e ? e : vka_alloc_page_table(&env->vka, &l3);
    e = e ? e : seL4_ARM_PageTable_Map(l2.cptr, hv->cptr, base, seL4_ARM_Default_VMAttributes);
    e = e ? e : seL4_ARM_PageTable_Map(l3.cptr, hv->cptr, base, seL4_ARM_Default_VMAttributes);
    if (e) {
        return e;
    }
    seL4_CPtr fcap;
    volatile seL4_Word *low = map_frame(env, &fcap);
    if (low == NULL) {
        return -1;
    }
    low[0] = HVS_MAGIC;
    cspacepath_t copy, src;
    if (vka_cspace_alloc_path(&env->vka, &copy)) {
        return -1;
    }
    vka_cspace_make_path(&env->vka, fcap, &src);
    e = vka_cnode_copy(&copy, &src, seL4_AllRights);
    return e ? e : seL4_ARM_Page_Map(copy.capPtr, hv->cptr, base, seL4_AllRights, seL4_ARM_Default_VMAttributes);
}

/* Answer `rounds` pings on `ep`, each carrying HVS_MAGIC; false at the
 * first other message (a VM fault: the window was not there). */
static int answer_pings(seL4_CPtr ep, seL4_CPtr reply, int rounds, const char *what)
{
    for (int i = 0; i < rounds; i++) {
        seL4_Word badge;
        seL4_MessageInfo_t tag = api_recv(ep, &badge, reply);
        seL4_Word label = seL4_MessageInfo_get_label(tag);
        if (label != HVS_PING || seL4_GetMR(0) != HVS_MAGIC) {
            printf("FL4HVS0003: %s, round %d: message %lu, %#lx %#lx\n", what, i, (unsigned long) label,
                   (unsigned long) seL4_GetMR(0), (unsigned long) seL4_GetMR(1));
            return 0;
        }
        api_reply(reply, seL4_MessageInfo_new(0, 0, 0, 0));
    }
    return 1;
}

/* A thread of a new process (its own VSpace and ASID) on core 0, faults
 * to `ep`, with window `hv` (0: none), running `fn`(ep, base, rounds). */
static int window_process(env_t env, helper_thread_t *t, seL4_CPtr ep, seL4_CPtr hv, helper_fn_t fn, seL4_Word rounds)
{
    create_helper_process(env, t);
    set_helper_affinity(env, t, 0);
    int e = api_tcb_set_space(get_helper_tcb(t), ep, t->process.cspace.cptr,
                              api_make_guard_skip_word(seL4_WordBits - t->process.cspace_size),
                              t->process.pd.cptr, seL4_NilData);
    if (!e && hv) {
        e = seL4_TCB_SetHighVSpace(get_helper_tcb(t), hv);
    }
    if (e) {
        return e;
    }
    seL4_CPtr ep_p = sel4utils_copy_cap_to_process(&t->process, &env->vka, ep);
    start_helper(env, t, fn, ep_p, seL4_ARM_HighVSpaceBase, rounds, 0);
    return 0;
}

/* The same in the test's own VSpace (and ASID). */
static int window_thread(env_t env, helper_thread_t *t, seL4_CPtr ep, seL4_CPtr hv, helper_fn_t fn, seL4_Word rounds)
{
    int e = fault_thread(env, t, ep);
    if (!e && hv) {
        e = seL4_TCB_SetHighVSpace(get_helper_tcb(t), hv);
    }
    if (e) {
        return e;
    }
    start_helper(env, t, fn, ep, seL4_ARM_HighVSpaceBase, rounds, 0);
    return 0;
}

/* `ep` minted with `badge`. */
static seL4_CPtr mint_badged(env_t env, seL4_CPtr ep, seL4_Word badge)
{
    cspacepath_t src, dest;
    vka_cspace_make_path(&env->vka, ep, &src);
    if (vka_cspace_alloc_path(&env->vka, &dest)) {
        return 0;
    }
    return vka_cnode_mint(&dest, &src, seL4_AllRights, badge) ? 0 : dest.capPtr;
}

/* One run of C: four threads on core 0, chained so that each hands the
 * core straight to the next with no other thread between them:
 * (a1, W) -> (a2, W) -> (a3, kernel) -> (a1, kernel). The last, of the
 * first's ASID but without the window, must fault on the window. Returns
 * SUCCESS or FAILURE (and records why). */
static int hvs_chain(env_t env, seL4_CPtr hv)
{
    const seL4_Word base = seL4_ARM_HighVSpaceBase;
    /* a1: the test's VSpace; a2, a3: two new processes. */
    const int in_process[4] = {0, 1, 1, 0};
    const int window[4] = {1, 1, 0, 0};
    helper_thread_t t[4];
    int made = 0;
    int result = FAILURE;
    seL4_CPtr report = vka_alloc_endpoint_leaky(&env->vka);
    seL4_CPtr park = vka_alloc_notification_leaky(&env->vka);
    seL4_CPtr link_ep[3];
    seL4_CPtr badged[4];
    seL4_Word io[4], pr[4];
    vka_object_t reply;
    int ok = report != 0 && park != 0 && vka_alloc_reply(&env->vka, &reply) == 0;
    for (int i = 0; ok && i < 3; i++) {
        link_ep[i] = vka_alloc_endpoint_leaky(&env->vka);
        ok = link_ep[i] != 0;
    }
    /* Faults and reports of link i arrive on `report` with badge i + 1. */
    for (int i = 0; ok && i < 4; i++) {
        badged[i] = mint_badged(env, report, i + 1);
        ok = badged[i] != 0;
    }
    if (!ok) {
        printf("FL4HVS0003: C: could not allocate the chain's objects\n");
        goto out;
    }
    for (int i = 0; i < 4; i++) {
        int e;
        if (in_process[i]) {
            create_helper_process(env, &t[i]);
            made = i + 1;
            e = api_tcb_set_space(get_helper_tcb(&t[i]), badged[i], t[i].process.cspace.cptr,
                                  api_make_guard_skip_word(seL4_WordBits - t[i].process.cspace_size),
                                  t[i].process.pd.cptr, seL4_NilData);
        } else {
            create_helper_thread(env, &t[i]);
            made = i + 1;
            e = api_tcb_set_space(get_helper_tcb(&t[i]), badged[i], env->cspace_root,
                                  api_make_guard_skip_word(seL4_WordBits - env->cspace_size_bits),
                                  env->page_directory, seL4_NilData);
        }
        set_helper_affinity(env, &t[i], 0);
        if (!e && window[i]) {
            e = seL4_TCB_SetHighVSpace(get_helper_tcb(&t[i]), hv);
        }
        if (e) {
            printf("FL4HVS0003: C: link %d: setup error %d\n", i, e);
            goto out;
        }
    }
    /* The links' caps, in each one's own CSpace: every one there and in
     * 32 bits, but the first link's `in` and the last's `out` (none). */
    for (int i = 0; i < 4; i++) {
        seL4_CPtr in = i > 0 ? link_ep[i - 1] : 0;
        seL4_CPtr out = i < 3 ? link_ep[i] : 0;
        seL4_CPtr pk = park, rp = badged[i];
        if (in_process[i]) {
            in = in ? sel4utils_copy_cap_to_process(&t[i].process, &env->vka, in) : 0;
            out = out ? sel4utils_copy_cap_to_process(&t[i].process, &env->vka, out) : 0;
            pk = sel4utils_copy_cap_to_process(&t[i].process, &env->vka, park);
            rp = sel4utils_copy_cap_to_process(&t[i].process, &env->vka, badged[i]);
        }
        int present = (i == 0 || in != 0) && (i == 3 || out != 0) && pk != 0 && rp != 0;
        int fits = in < (1ull << 32) && out < (1ull << 32) && pk < (1ull << 32) && rp < (1ull << 32);
        if (!present || !fits) {
            printf("FL4HVS0003: C: link %d: CPtrs in %#lx out %#lx park %#lx report %#lx\n", i, (unsigned long) in,
                   (unsigned long) out, (unsigned long) pk, (unsigned long) rp);
            goto out;
        }
        io[i] = in | ((seL4_Word) out << 32);
        pr[i] = pk | ((seL4_Word) rp << 32);
    }
    /* Last link first: each waits for the one before it. Links 0, 1 (the
     * window's) and 3 (the probe) read the window; 2 does not. */
    for (int i = 3; i >= 0; i--) {
        start_helper(env, &t[i], hvs_chain_link, io[i], pr[i], base, i != 2);
    }
    seL4_Word badge;
    seL4_MessageInfo_t tag = api_recv(report, &badge, reply.cptr);
    seL4_Word label = seL4_MessageInfo_get_label(tag);
    if (badge == 4 && label == seL4_Fault_VMFault && seL4_GetMR(seL4_VMFault_Addr) == base) {
        result = SUCCESS;
    } else {
        printf("FL4HVS0003: C: link %lu, message %lu, %#lx\n", (unsigned long) badge - 1, (unsigned long) label,
               (unsigned long) seL4_GetMR(0));
    }
out:
    for (int i = 0; i < made; i++) {
        cleanup_helper(env, &t[i]);
    }
    test_eq(result, SUCCESS);
    return result;
}

/* On one core, a window's translations never reach a thread without it,
 * and the window always works for its threads:
 * A: a thread of another ASID with the window alternates with the test's
 *    thread (its own ASID, the kernel's TTBR1, kernel entries in between);
 * B: the same with a window thread of the test's own ASID;
 * C: (a1, W) -> (a2, W) -> (a3, kernel) -> (a1, kernel) with nothing else
 *    between them (`hvs_chain`): the last faults on the window. */
static int test_high_vspace_tlb_isolation(env_t env)
{
    vka_object_t hv;
    test_error_eq(make_window(env, &hv), 0);
    seL4_CPtr ep = vka_alloc_endpoint_leaky(&env->vka);
    vka_object_t reply;
    test_error_eq(vka_alloc_reply(&env->vka, &reply), 0);

    /* A: another ASID with the window <-> this thread. */
    helper_thread_t a;
    test_error_eq(window_process(env, &a, ep, hv.cptr, high_ping, HVS_ROUNDS), 0);
    if (!answer_pings(ep, reply.cptr, HVS_ROUNDS, "A (other ASID, window)")) {
        test_check(0);
        cleanup_helper(env, &a);
        return sel4test_get_result();
    }
    test_eq(wait_for_helper(&a), 0);
    cleanup_helper(env, &a);

    /* B: this thread's ASID with the window <-> this thread. */
    helper_thread_t b;
    test_error_eq(window_thread(env, &b, ep, hv.cptr, high_ping, HVS_ROUNDS), 0);
    if (!answer_pings(ep, reply.cptr, HVS_ROUNDS, "B (same ASID, window)")) {
        test_check(0);
        cleanup_helper(env, &b);
        return sel4test_get_result();
    }
    test_eq(wait_for_helper(&b), 0);
    cleanup_helper(env, &b);

    /* C, three times. */
    for (int round = 0; round < 3; round++) {
        if (hvs_chain(env, hv.cptr) != SUCCESS) {
            return sel4test_get_result();
        }
    }
    printf("FL4HVS0003: A and B %d rounds each, C 3 times: isolated\n", HVS_ROUNDS);
    return sel4test_get_result();
}
DEFINE_TEST(FL4HVS0003, "ArmHighVSpace: TLB isolation as windows and ASIDs alternate on a core", test_high_vspace_tlb_isolation, true)
#endif
