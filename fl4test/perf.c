/*
 * Multi-core IPC scaling (DESIGN.md §12, performance): k independent
 * client/server pairs, pair i on core i, for k = 1 up to the number of
 * cores. Uses only the seL4 API, so the same test runs on FL4 and on
 * upstream seL4 (`FL4_KERNEL=sel4`): FL4 should scale, seL4's big kernel
 * lock should not. Prints throughput; nothing is checked.
 */
#include <stdio.h>
#include <sel4/sel4.h>
#include <vka/object.h>
#include <sel4test/testutil.h>
#include <sel4test/macros.h>

#include "../helpers.h"

#define CALLS 100000

static uint64_t tsc(void)
{
    return __builtin_ia32_rdtsc();
}

static int scale_server(seL4_Word ep, seL4_Word reply, seL4_Word c, seL4_Word d)
{
    seL4_Word badge;
    seL4_Recv(ep, &badge, reply);
    while (1) {
        seL4_ReplyRecv(ep, seL4_MessageInfo_new(0, 0, 0, 0), &badge, reply);
    }
    return 0;
}

struct span {
    volatile uint64_t start, end;
};

static int scale_client(seL4_Word ep, seL4_Word done, seL4_Word span, seL4_Word d)
{
    struct span *s = (struct span *) span;
    /* The first Call meets the server; time the rest. */
    seL4_Call(ep, seL4_MessageInfo_new(0, 0, 0, 0));
    s->start = tsc();
    for (int i = 0; i < CALLS; i++) {
        seL4_Call(ep, seL4_MessageInfo_new(0, 0, 0, 0));
    }
    s->end = tsc();
    seL4_Signal(done);
    while (1) {
        seL4_Yield();
    }
    return 0;
}

static int test_ipc_scaling(env_t env)
{
    int n = env->cores;
    for (int k = 1; k <= n; k++) {
        helper_thread_t servers[n], clients[n];
        vka_object_t replies[n];
        seL4_CPtr done[n];
        struct span spans[n];
        for (int i = 0; i < k; i++) {
            seL4_CPtr ep = vka_alloc_endpoint_leaky(&env->vka);
            test_error_eq(vka_alloc_reply(&env->vka, &replies[i]), 0);
            done[i] = vka_alloc_notification_leaky(&env->vka);
            spans[i].start = spans[i].end = 0;
            create_helper_thread(env, &servers[i]);
            create_helper_thread(env, &clients[i]);
            set_helper_priority(env, &servers[i], env->priority);
            set_helper_priority(env, &clients[i], env->priority);
            set_helper_affinity(env, &servers[i], i);
            set_helper_affinity(env, &clients[i], i);
            start_helper(env, &servers[i], scale_server, ep, replies[i].cptr, 0, 0);
            start_helper(env, &clients[i], scale_client, ep, done[i], (seL4_Word) &spans[i], 0);
        }
        uint64_t first = UINT64_MAX, last = 0;
        for (int i = 0; i < k; i++) {
            seL4_Wait(done[i], NULL);
            if (spans[i].start < first) {
                first = spans[i].start;
            }
            if (spans[i].end > last) {
                last = spans[i].end;
            }
        }
        uint64_t ticks = last - first;
        printf("IPC scaling: %d pair(s): %lu round trips per million TSC ticks\n", k,
               (unsigned long)((uint64_t) k * CALLS * 1000000 / (ticks ? ticks : 1)));
        for (int i = 0; i < k; i++) {
            cleanup_helper(env, &clients[i]);
            cleanup_helper(env, &servers[i]);
        }
    }
    return sel4test_get_result();
}
DEFINE_TEST(FL4PERF0002, "Multi-core IPC scaling (printed, not checked)", test_ipc_scaling,
            config_set(CONFIG_ENABLE_SMP_SUPPORT))
