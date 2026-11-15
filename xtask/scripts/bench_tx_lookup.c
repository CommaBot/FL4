// SPDX-License-Identifier: GPL-2.0-only
/* Host-only write-log lookup experiment for issue #11. This does not run
 * kernel code or measure FPU ownership, version checks, logging, or commit.
 * Keys model groups of nearby words in separately aligned kernel objects;
 * queries are deterministically shuffled, 50% hits and 50% misses. The
 * AVX2 scan compares 16 keys at a time and is guarded by a host CPU check.
 *
 * Build and run on an otherwise idle host (adjust CPU 2 as needed):
 *   mkdir -p build/scratch
 *   TMPDIR="$PWD/build/scratch" cc -O3 -fno-tree-vectorize -Wall -Wextra -Werror \
 *       xtask/scripts/bench_tx_lookup.c -o build/bench_tx_lookup
 *   taskset -c 2 build/bench_tx_lookup
 *
 * Report medians of the five trials. These synthetic lookup timings are
 * not substitutes for the issue's end-to-end QEMU probe.
 */
#include <immintrin.h>
#include <stdint.h>
#include <stdio.h>
#include <time.h>

#define WB 2048
static uint64_t keys[1024] __attribute__((aligned(64)));
static uint64_t hashkeys[WB], hashvalues[WB];
static unsigned stamps[WB];
static uint64_t queries[4096];
static volatile uint64_t result;

__attribute__((noinline)) static uint64_t hashed(uint64_t key, unsigned n)
{
    (void)n;
    unsigned i = ((key >> 3) ^ (key >> 12)) & (WB - 1);
    while (stamps[i]) {
        if (hashkeys[i] == key) return hashvalues[i];
        i = (i + 1) & (WB - 1);
    }
    return 0;
}

__attribute__((noinline)) static uint64_t scalar(uint64_t key, unsigned n)
{
    while (n) if (keys[--n] == key) return n + 1;
    return 0;
}

__attribute__((noinline,target("avx2"))) static uint64_t vector(uint64_t key, unsigned n)
{
    const __m256i needle = _mm256_set1_epi64x(key);
    while (n >= 16) {
        n -= 16;
        __m256i a = _mm256_cmpeq_epi64(needle, _mm256_loadu_si256((const __m256i *)(keys + n)));
        __m256i b = _mm256_cmpeq_epi64(needle, _mm256_loadu_si256((const __m256i *)(keys + n + 4)));
        __m256i c = _mm256_cmpeq_epi64(needle, _mm256_loadu_si256((const __m256i *)(keys + n + 8)));
        __m256i d = _mm256_cmpeq_epi64(needle, _mm256_loadu_si256((const __m256i *)(keys + n + 12)));
        __m256i any = _mm256_or_si256(_mm256_or_si256(a, b), _mm256_or_si256(c, d));
        if (_mm256_movemask_pd(_mm256_castsi256_pd(any))) {
            unsigned mask = _mm256_movemask_pd(_mm256_castsi256_pd(a))
                | (_mm256_movemask_pd(_mm256_castsi256_pd(b)) << 4)
                | (_mm256_movemask_pd(_mm256_castsi256_pd(c)) << 8)
                | (_mm256_movemask_pd(_mm256_castsi256_pd(d)) << 12);
            return n + __builtin_ctz(mask) + 1;
        }
    }
    while (n >= 4) {
        n -= 4;
        __m256i found = _mm256_cmpeq_epi64(needle, _mm256_loadu_si256((const __m256i *)(keys + n)));
        unsigned mask = _mm256_movemask_pd(_mm256_castsi256_pd(found));
        if (mask) return n + __builtin_ctz(mask) + 1;
    }
    while (n) if (keys[--n] == key) return n + 1;
    return 0;
}

static uint64_t nanos(void)
{
    struct timespec now;
    clock_gettime(CLOCK_MONOTONIC_RAW, &now);
    return now.tv_sec * 1000000000ull + now.tv_nsec;
}

int main(void)
{
    if (!__builtin_cpu_supports("avx2")) return 77;
    unsigned sizes[] = {6, 8, 13, 16, 25, 29, 32, 43, 48, 52, 64, 128, 256, 512};
    uint64_t (*methods[])(uint64_t, unsigned) = {hashed, scalar, vector};
    puts("words,trial,hash_ns,scalar_ns,avx2_ns");
    for (unsigned s = 0; s < sizeof(sizes)/sizeof(*sizes); s++) {
        unsigned n = sizes[s];
        for (unsigned i = 0; i < WB; i++) stamps[i] = 0;
        for (unsigned i = 0; i < n; i++) {
            keys[i] = 0xffff800000000000ull + (i / 8) * 0x4000 + (i % 8) * 8;
            unsigned slot = ((keys[i] >> 3) ^ (keys[i] >> 12)) & (WB - 1);
            while (stamps[slot]) slot = (slot + 1) & (WB - 1);
            stamps[slot] = 1; hashkeys[slot] = keys[i]; hashvalues[slot] = i + 1;
        }
        uint64_t random = 42;
        for (unsigned i = 0; i < 4096; i++) {
            random ^= random << 13; random ^= random >> 7; random ^= random << 17;
            queries[i] = keys[(random >> 1) % n] + ((random & 1) ? 0 : 0x100000ull);
            if (hashed(queries[i], n) != scalar(queries[i], n) || scalar(queries[i], n) != vector(queries[i], n)) return 1;
        }
        for (unsigned trial = 0; trial < 5; trial++) {
            double ns[3];
            for (unsigned m = 0; m < 3; m++) {
                uint64_t acc = 0, start = nanos();
                for (unsigned repeat = 0; repeat < 500; repeat++)
                    for (unsigned i = 0; i < 4096; i++) acc += methods[m](queries[i], n);
                ns[m] = (double)(nanos() - start) / (500 * 4096);
                result = acc;
            }
            printf("%u,%u,%.3f,%.3f,%.3f\n", n, trial, ns[0], ns[1], ns[2]);
        }
    }
}
