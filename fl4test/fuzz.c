/*
 * Differential fuzzing against seL4 (DESIGN.md §2, §12). Each seed is a
 * generated program of seL4 API calls on objects the program creates
 * itself. The test uses only the seL4 API, so `cargo xtask fuzz` builds it
 * against upstream libsel4 for seL4 and FL4's libsel4 for FL4, runs both
 * under QEMU and compares the traces it prints.
 *
 * A program runs in a helper thread whose CSpace is a fresh 256-slot
 * CNode holding only itself (slot 1), a private 64 KiB untyped (slot 2)
 * and two unconfigured TCBs (slots 3 and 4, made by the root task), so capability pointers are slot numbers on both kernels and
 * nothing depends on how the root task's memory was laid out. The trace
 * records each call, its error code, the message registers a failed call
 * returns, and in debug builds the type of the capability in the slot it
 * touched. Nothing records an address. Retypes avoid TCBs and frames,
 * whose sizes differ between the kernels (FL4's TCB is 4 KiB).
 */
#include <stdio.h>
#include <sel4/sel4.h>
#include <vka/object.h>
#include <vka/capops.h>
#include <sel4test/testutil.h>
#include <sel4test/macros.h>

#include "../helpers.h"

#define FUZZ_SEEDS 40
#define FUZZ_STEPS 400
#define FUZZ_DEPTH 8

struct fuzz_rec {
    uint16_t op;
    uint16_t a, b, c;
    uint32_t err;
    uint32_t cap;
    uint64_t mr0, mr1;
    /* A fault the call raised: its label and two of its message words
     * (not the instruction address, which differs between the builds). */
    uint32_t fault;
    uint64_t fmr0, fmr1;
};

struct fuzz_run {
    uint64_t seed;
    volatile int done;
    volatile int cur;
    struct fuzz_rec rec[FUZZ_STEPS];
};

static uint64_t rnd(uint64_t *s)
{
    uint64_t x = *s;
    x ^= x >> 12;
    x ^= x << 25;
    x ^= x >> 27;
    *s = x;
    return x * 0x2545F4914F6CDD1Dull;
}

static uint32_t identify(seL4_CPtr slot)
{
#ifdef CONFIG_DEBUG_BUILD
    return seL4_DebugCapIdentify(slot);
#else
    return 0;
#endif
}

/* seL4_DebugCapIdentify's value for a thread capability (the C kernel's
 * cap_thread_cap tag). */
#define FUZZ_CAP_THREAD 12

static const seL4_Word fuzz_types[] = {
    seL4_EndpointObject, seL4_NotificationObject, seL4_ReplyObject,
    seL4_CapTableObject, seL4_UntypedObject, seL4_SchedContextObject,
};

static int fuzz_program(seL4_Word arg, seL4_Word b, seL4_Word c, seL4_Word d)
{
    struct fuzz_run *run = (struct fuzz_run *) arg;
    uint64_t s = run->seed * 0x9E3779B97F4A7C15ull | 1;
    for (int i = 0; i < FUZZ_STEPS; i++) {
        struct fuzz_rec *r = &run->rec[i];
        int op = rnd(&s) % 18;
        /* Mostly slots that are in use, sometimes any slot. */
        seL4_Word x = rnd(&s) % 4 ? rnd(&s) % 24 : rnd(&s) % 256;
        seL4_Word y = rnd(&s) % 4 ? rnd(&s) % 24 : rnd(&s) % 256;
        seL4_Word z = rnd(&s) % 24;
        seL4_Word w = rnd(&s);
        int err = 0;
        /* An invocation is a Call on the capability: on an endpoint it is
         * an IPC that waits forever. Thread operations only go to slots
         * known to hold a thread capability (debug builds). */
        if (op >= 10 && op <= 15 && identify(x) != FUZZ_CAP_THREAD) {
            op = 8;
        }
        r->mr0 = r->mr1 = 0;
        r->fault = 0;
        r->fmr0 = r->fmr1 = 0;
        run->cur = i;
        r->op = op;
        r->a = x;
        r->b = y;
        r->c = z;
        switch (op) {
        case 0: {
            seL4_Word type = fuzz_types[w % 6];
            seL4_Word bits = type == seL4_CapTableObject ? 1 + (w >> 8) % 4 :
                             type == seL4_UntypedObject ? 4 + (w >> 8) % 9 :
                             type == seL4_SchedContextObject ? 7 + (w >> 8) % 2 : 0;
            err = seL4_Untyped_Retype(2, type, bits, 1, 0, 0, x, 1 + (w >> 16) % 4);
            break;
        }
        case 1:
            err = seL4_CNode_Copy(1, x, FUZZ_DEPTH, 1, y, FUZZ_DEPTH, seL4_CapRights_new(!!(w & 1), !!(w & 2), !!(w & 4), !!(w & 8)));
            break;
        case 2:
            err = seL4_CNode_Mint(1, x, FUZZ_DEPTH, 1, y, FUZZ_DEPTH, seL4_CapRights_new(!!(w & 1), !!(w & 2), !!(w & 4), !!(w & 8)),
                                  (w >> 8) % 3);
            break;
        case 3:
            /* Slots 1 and 2 (the program's CNode and untyped) are never
             * moved away. */
            err = y > 2 ? seL4_CNode_Move(1, x, FUZZ_DEPTH, 1, y, FUZZ_DEPTH) : -1;
            break;
        case 4:
            err = y > 2 ? seL4_CNode_Mutate(1, x, FUZZ_DEPTH, 1, y, FUZZ_DEPTH, (w >> 8) % 3) : -1;
            break;
        case 5:
            /* Never the two capabilities the program runs on. */
            err = x > 2 ? seL4_CNode_Delete(1, x, FUZZ_DEPTH) : -1;
            break;
        case 6:
            err = x > 2 ? seL4_CNode_Revoke(1, x, FUZZ_DEPTH) : -1;
            break;
        case 7:
            err = x > 2 && z > 2 && y > 2 ? seL4_CNode_Rotate(1, x, FUZZ_DEPTH, (w >> 8) % 3, 1, y, FUZZ_DEPTH, 1, z, FUZZ_DEPTH,
                                                    (w >> 16) % 3) : -1;
            break;
        case 8:
            err = seL4_CNode_CancelBadgedSends(1, x, FUZZ_DEPTH);
            break;
        case 9:
            /* Non-blocking, label 0: delivers to a waiting receiver or
             * does nothing; never an object invocation. */
            seL4_SetMR(0, w);
            seL4_NBSend(x, seL4_MessageInfo_new(0, 0, 0, 1));
            break;
        case 10: {
            /* The values too: register initialisation and sanitising
             * must match. */
            seL4_UserContext regs;
            err = seL4_TCB_ReadRegisters(x, 0, 0, 1 + w % (sizeof(regs) / sizeof(seL4_Word)), &regs);
            if (err == 0) {
                r->mr0 = regs.rip ^ regs.rsp << 1 ^ regs.rflags << 2 ^ regs.rax << 3;
                r->mr1 = regs.fs_base ^ regs.gs_base << 1 ^ regs.r15;
            }
            break;
        }
        case 11: {
            seL4_UserContext regs;
            seL4_Word *v = (seL4_Word *) &regs;
            for (int k = 0; k < sizeof(regs) / sizeof(seL4_Word); k++) {
                v[k] = rnd(&s) % 3 == 0 ? rnd(&s) : rnd(&s) % 4096;
            }
            err = seL4_TCB_WriteRegisters(x, 0, 0, 1 + w % (sizeof(regs) / sizeof(seL4_Word)), &regs);
            break;
        }
        case 12:
            err = seL4_TCB_Suspend(x);
            break;
        case 13:
            err = seL4_TCB_SetPriority(x, y, w % 300);
            break;
        case 14:
            err = seL4_TCB_BindNotification(x, y);
            break;
        case 15:
            err = seL4_TCB_UnbindNotification(x);
            break;
        case 16: {
            /* Faults (a capability that cannot receive, a missing reply
             * object) go to the root task, which records them and
             * resumes the program after the call. */
            seL4_Word badge = 0;
            seL4_MessageInfo_t info = seL4_NBRecv(x, &badge, y);
            r->mr0 = badge;
            r->mr1 = seL4_MessageInfo_get_label(info) << 8 | seL4_MessageInfo_get_length(info);
            break;
        }
        case 17: {
            seL4_Word badge = 0;
            seL4_MessageInfo_t info = seL4_NBWait(x, &badge);
            r->mr0 = badge;
            r->mr1 = seL4_MessageInfo_get_label(info) << 8 | seL4_MessageInfo_get_length(info);
            break;
        }
        default:
            break;
        }
        r->err = err;
        if (err > 0) {
            r->mr0 = seL4_GetMR(0);
            r->mr1 = seL4_GetMR(1);
        }
        r->cap = identify(x) | identify(y) << 8;
    }
    run->done = 1;
    while (1) {
        seL4_Yield();
    }
    return 0;
}

static int test_fuzz(env_t env)
{
    static struct fuzz_run run;
    for (uint64_t seed = 1; seed <= FUZZ_SEEDS; seed++) {
        vka_object_t cn, ut;
        test_error_eq(vka_alloc_cnode_object(&env->vka, FUZZ_DEPTH, &cn), 0);
        test_error_eq(vka_alloc_untyped(&env->vka, 16, &ut), 0);
        test_error_eq(seL4_CNode_Copy(cn.cptr, 1, FUZZ_DEPTH, env->cspace_root, cn.cptr, seL4_WordBits,
                                      seL4_AllRights), seL4_NoError);
        test_error_eq(seL4_CNode_Copy(cn.cptr, 2, FUZZ_DEPTH, env->cspace_root, ut.cptr, seL4_WordBits,
                                      seL4_AllRights), seL4_NoError);
        for (int k = 0; k < 2; k++) {
            vka_object_t tcb;
            test_error_eq(vka_alloc_tcb(&env->vka, &tcb), 0);
            test_error_eq(seL4_CNode_Move(cn.cptr, 3 + k, FUZZ_DEPTH, env->cspace_root, tcb.cptr, seL4_WordBits),
                          seL4_NoError);
        }
        helper_thread_t t;
        create_helper_thread(env, &t);
        set_helper_priority(env, &t, env->priority);
        seL4_CPtr fault_ep = vka_alloc_endpoint_leaky(&env->vka);
        vka_object_t reply;
        test_error_eq(vka_alloc_reply(&env->vka, &reply), 0);
        test_error_eq(api_tcb_set_space(get_helper_tcb(&t), fault_ep, cn.cptr,
                                        api_make_guard_skip_word(seL4_WordBits - FUZZ_DEPTH),
                                        env->page_directory, seL4_NilData), seL4_NoError);
        run.seed = seed;
        run.done = 0;
        start_helper(env, &t, fuzz_program, (seL4_Word) &run, 0, 0, 0);
        while (!run.done) {
            seL4_Word badge;
            seL4_MessageInfo_t info = seL4_NBRecv(fault_ep, &badge, reply.cptr);
            if (seL4_MessageInfo_get_label(info) == 0) {
                seL4_Yield();
                continue;
            }
            /* The program faulted in call run.cur: record it, and resume
             * the program after its syscall instruction. */
            struct fuzz_rec *r = &run.rec[run.cur];
            r->fault = seL4_MessageInfo_get_label(info);
            r->fmr0 = seL4_GetMR(1);
            r->fmr1 = seL4_GetMR(2);
            seL4_UserContext regs;
            test_error_eq(seL4_TCB_ReadRegisters(get_helper_tcb(&t), 0, 0, sizeof(regs) / sizeof(seL4_Word), &regs), 0);
            regs.rip += 2;
            test_error_eq(seL4_TCB_WriteRegisters(get_helper_tcb(&t), 1, 0, sizeof(regs) / sizeof(seL4_Word), &regs), 0);
        }
        for (int i = 0; i < FUZZ_STEPS; i++) {
            struct fuzz_rec *r = &run.rec[i];
            printf("FUZZ %lu %d op %u %u %u %u -> %d cap %x mr %lx %lx fault %u %lx %lx\n", (unsigned long) seed, i, r->op,
                   r->a, r->b, r->c, (int) r->err, r->cap, (unsigned long) r->mr0, (unsigned long) r->mr1, r->fault,
                   (unsigned long) r->fmr0, (unsigned long) r->fmr1);
        }
        cleanup_helper(env, &t);
    }
    return sel4test_get_result();
}
DEFINE_TEST(FL4FUZZ0001, "Differential fuzzing: seL4 API programs (traces compared by cargo xtask fuzz)", test_fuzz, true)
