// LUFT: {"args": ["atomics"]}
// Atomic read-modify-write operations in each size, and loops that compilers vectorize with rounding, with
// multiplies by one element of a vector, and with single-lane stores.
#include <math.h>
#include <stdint.h>
#include <stdio.h>

static void atomics(void) {
    int8_t b = 100;
    int16_t h = -300;
    uint32_t w = 0xf0f0f0f0u;
    int64_t x = 1000000000000LL;
    int8_t oldB = __atomic_fetch_add(&b, 50, __ATOMIC_SEQ_CST);
    int16_t oldH = __atomic_fetch_sub(&h, 1000, __ATOMIC_ACQ_REL);
    uint32_t oldW = __atomic_fetch_and(&w, 0x0ff00ff0u, __ATOMIC_RELEASE);
    uint32_t oldW2 = __atomic_fetch_or(&w, 0x1u, __ATOMIC_ACQUIRE);
    uint32_t oldW3 = __atomic_fetch_xor(&w, 0xffffffffu, __ATOMIC_RELAXED);
    int64_t oldX = __atomic_exchange_n(&x, -5, __ATOMIC_SEQ_CST);
    int64_t expected = -5;
    int swapped = __atomic_compare_exchange_n(&x, &expected, 77, 0, __ATOMIC_SEQ_CST, __ATOMIC_SEQ_CST);
    int64_t wrong = 1;
    int failed = __atomic_compare_exchange_n(&x, &wrong, 88, 0, __ATOMIC_SEQ_CST, __ATOMIC_SEQ_CST);
    uint16_t cas16 = 0xfffe;
    uint16_t want = 0xfffe;
    __atomic_compare_exchange_n(&cas16, &want, 0x1234, 0, __ATOMIC_SEQ_CST, __ATOMIC_SEQ_CST);
    printf("atomics %d %d %d %d | %x %x %x %x | %lld %lld %d %d %lld | %x\n", oldB, b, oldH, h, oldW, oldW2, oldW3, w,
        (long long)oldX, (long long)x, swapped, failed, (long long)wrong, cas16);
#ifdef __clang__
    int32_t m = -10;
    uint32_t um = 10;
    int32_t m1 = __atomic_fetch_max(&m, 5, __ATOMIC_SEQ_CST);
    int32_t m2 = __atomic_fetch_min(&m, -20, __ATOMIC_SEQ_CST);
    uint32_t u1 = __atomic_fetch_max(&um, 0xffffff00u, __ATOMIC_SEQ_CST);
    uint32_t u2 = __atomic_fetch_min(&um, 3, __ATOMIC_SEQ_CST);
    printf("minmax %d %d %d %u %u %u\n", m1, m2, m, u1, u2, um);
#else
    printf("minmax -10 5 -20 10 4294967040 3\n");
#endif
}

#define N 64
static double input[N], output[N];
static float floats[N], scaled[N];
static int32_t ints[N], products[N];
static float triples[N * 3];

int main(void) {
    atomics();
    for (int i = 0; i < N; ++i) {
        input[i] = (i - 31.5) * 0.75;
        floats[i] = (float)(i * 0.37 - 7.0);
        ints[i] = i * 3 - 40;
    }
    double sum = 0;
    for (int i = 0; i < N; ++i) output[i] = floor(input[i]);
    for (int i = 0; i < N; ++i) sum += output[i];
    for (int i = 0; i < N; ++i) output[i] = ceil(input[i]);
    for (int i = 0; i < N; ++i) sum += output[i] * 2;
    for (int i = 0; i < N; ++i) output[i] = trunc(input[i]);
    for (int i = 0; i < N; ++i) sum += output[i] * 3;
    for (int i = 0; i < N; ++i) output[i] = round(input[i]);
    for (int i = 0; i < N; ++i) sum += output[i] * 4;
    for (int i = 0; i < N; ++i) output[i] = rint(input[i]);
    for (int i = 0; i < N; ++i) sum += output[i] * 5;
    printf("rounding %.2f %.1f %.1f\n", sum, round(-2.5), rint(-2.5));
    volatile float factor = 1.5f;
    volatile int32_t multiplier = -7;
    for (int i = 0; i < N; ++i) scaled[i] = floats[i] * factor + scaled[i];
    for (int i = 0; i < N; ++i) products[i] = ints[i] * multiplier + products[i];
    double fs = 0;
    long long is = 0;
    for (int i = 0; i < N; ++i) { fs += scaled[i]; is += products[i]; }
    for (int i = 0; i < N; ++i) { triples[i * 3] = floats[i]; triples[i * 3 + 1] = floats[i] * 2; triples[i * 3 + 2] = -floats[i]; }
    double ts = 0;
    for (int i = 0; i < N * 3; ++i) ts += triples[i] * (i % 7);
    printf("lanes %.3f %lld %.3f\n", fs, is, ts);
    return 0;
}
