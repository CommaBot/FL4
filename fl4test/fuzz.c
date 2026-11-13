/*
 * Differential fuzzing against seL4 (DESIGN.md §2, §12). Each seed is a
 * generated program of seL4 API calls on objects the program creates
 * itself. The test uses only the seL4 API, so `cargo xtask fuzz` builds it
 * against upstream libsel4 for seL4 and FL4's libsel4 for FL4, runs both
 * under QEMU and compares the traces it prints.
 *
 * A program runs in a helper thread whose CSpace is a fresh 256-slot
 * CNode holding only itself (slot 1) and a private 64 KiB untyped
 * (slot 2), so capability pointers are slot numbers on both kernels and
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
};

struct fuzz_run {
    uint64_t seed;
    volatile int done;
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
        int op = rnd(&s) % 10;
        /* Mostly slots that are in use, sometimes any slot. */
        seL4_Word x = rnd(&s) % 4 ? rnd(&s) % 24 : rnd(&s) % 256;
        seL4_Word y = rnd(&s) % 4 ? rnd(&s) % 24 : rnd(&s) % 256;
        seL4_Word z = rnd(&s) % 24;
        seL4_Word w = rnd(&s);
        int err = 0;
        r->mr0 = r->mr1 = 0;
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
            /* Slot 1 is the program's CNode: never moved away. */
            err = y != 1 ? seL4_CNode_Move(1, x, FUZZ_DEPTH, 1, y, FUZZ_DEPTH) : -1;
            break;
        case 4:
            err = y != 1 ? seL4_CNode_Mutate(1, x, FUZZ_DEPTH, 1, y, FUZZ_DEPTH, (w >> 8) % 3) : -1;
            break;
        case 5:
            /* Never the two capabilities the program runs on. */
            err = x > 2 ? seL4_CNode_Delete(1, x, FUZZ_DEPTH) : -1;
            break;
        case 6:
            err = x > 2 ? seL4_CNode_Revoke(1, x, FUZZ_DEPTH) : -1;
            break;
        case 7:
            err = x > 2 && z > 2 && y != 1 ? seL4_CNode_Rotate(1, x, FUZZ_DEPTH, (w >> 8) % 3, 1, y, FUZZ_DEPTH, 1, z, FUZZ_DEPTH,
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
        default:
            /* Receives are left out: one through an endpoint or
             * notification capability without the Read right is a
             * capability fault, and the program has no fault handler. */
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
        helper_thread_t t;
        create_helper_thread(env, &t);
        set_helper_priority(env, &t, env->priority);
        test_error_eq(api_tcb_set_space(get_helper_tcb(&t), seL4_CapNull, cn.cptr,
                                        api_make_guard_skip_word(seL4_WordBits - FUZZ_DEPTH),
                                        env->page_directory, seL4_NilData), seL4_NoError);
        run.seed = seed;
        run.done = 0;
        start_helper(env, &t, fuzz_program, (seL4_Word) &run, 0, 0, 0);
        while (!run.done) {
            seL4_Yield();
        }
        for (int i = 0; i < FUZZ_STEPS; i++) {
            struct fuzz_rec *r = &run.rec[i];
            printf("FUZZ %lu %d op %u %u %u %u -> %d cap %x mr %lx %lx\n", (unsigned long) seed, i, r->op, r->a,
                   r->b, r->c, (int) r->err, r->cap, (unsigned long) r->mr0, (unsigned long) r->mr1);
        }
        cleanup_helper(env, &t);
    }
    return sel4test_get_result();
}
DEFINE_TEST(FL4FUZZ0001, "Differential fuzzing: seL4 API programs (traces compared by cargo xtask fuzz)", test_fuzz, true)
