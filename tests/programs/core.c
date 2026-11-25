// Differential test functions. Every export takes two 64-bit integers and returns one.
#include <setjmp.h>
#include <stdarg.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

typedef uint64_t u64;
typedef int64_t i64;
typedef uint32_t u32;
typedef int32_t i32;

#define EXPORT __attribute__((noinline, used)) u64

EXPORT add64(u64 a, u64 b) { return a + b; }
EXPORT sub64(u64 a, u64 b) { return a - b; }
EXPORT mul64(u64 a, u64 b) { return a * b; }
EXPORT mul32(u64 a, u64 b) { return (u32)a * (u32)b; }
EXPORT smul32(u64 a, u64 b) { return (u64)(i64)((i32)a * (i64)(i32)b); }
EXPORT udiv64(u64 a, u64 b) { return b ? a / b : 0; }
EXPORT umod64(u64 a, u64 b) { return b ? a % b : 0; }
EXPORT sdiv64(u64 a, u64 b) { return (b && !(a == (u64)INT64_MIN && b == (u64)-1)) ? (u64)((i64)a / (i64)b) : 0; }
EXPORT smod64(u64 a, u64 b) { return (b && !(a == (u64)INT64_MIN && b == (u64)-1)) ? (u64)((i64)a % (i64)b) : 0; }
EXPORT udiv32(u64 a, u64 b) { return (u32)b ? (u32)a / (u32)b : 0; }
EXPORT sdiv32(u64 a, u64 b) { return ((i32)b && !((i32)a == INT32_MIN && (i32)b == -1)) ? (u64)(i64)((i32)a / (i32)b) : 0; }
EXPORT smod32(u64 a, u64 b) { return ((i32)b && !((i32)a == INT32_MIN && (i32)b == -1)) ? (u64)(i64)((i32)a % (i32)b) : 0; }
EXPORT divconst(u64 a, u64 b) { return a / 7 + a / 10 + (u64)((i64)a / 3) + (u32)a / 13 + (u64)((i64)b % 9); }
// x86 byte multiplies (GCC divides bytes by constants with MUL r/m8) and ADC/SBB with memory operands; the C
// fallback computes the same values elsewhere.
EXPORT bytemul(u64 a, u64 b) {
    u64 mem = b ^ 0x5555, sum = a, diff = b, into = a ^ b;
    unsigned short ax1 = (uint8_t)a, ax2 = (uint16_t)a, ax3 = (uint8_t)(a >> 16);
    uint8_t f1, f2, f3, factor = (uint8_t)(b >> 8);
#if defined(__x86_64__)
    __asm__("mulb %2\n\tsetc %1" : "+a"(ax1), "=r"(f1) : "q"((uint8_t)b) : "cc");
    __asm__("mulb %%ah\n\tseto %1" : "+a"(ax2), "=r"(f2) : : "cc");
    __asm__("imulb %2\n\tsetc %1" : "+a"(ax3), "=r"(f3) : "m"(factor) : "cc");
    __asm__("addq %[b], %[s]\n\tadcq %[m], %[s]" : [s] "+r"(sum) : [b] "r"(b), [m] "m"(mem) : "cc");
    __asm__("cmpq %[a], %[d]\n\tsbbq %[m], %[d]" : [d] "+r"(diff) : [a] "r"(a), [m] "m"(mem) : "cc");
    __asm__("cmpl %k[a], %k[b]\n\tadcq %[a], %[m]\n\tsbbl %k[b], %k[i]" : [m] "+m"(mem), [i] "+r"(into)
            : [a] "r"(a), [b] "r"(b) : "cc");
#else
    u64 p1 = (u64)(uint8_t)a * (uint8_t)b, p2 = (u64)(uint8_t)a * (uint8_t)(a >> 8);
    i64 p3 = (i64)(int8_t)(a >> 16) * (int8_t)factor;
    ax1 = (unsigned short)p1, f1 = p1 > 255;
    ax2 = (unsigned short)p2, f2 = p2 > 255;
    ax3 = (unsigned short)p3, f3 = p3 < -128 || p3 > 127;
    u64 carry = a + b < a;
    sum = a + b + mem + carry;
    u64 borrow = b < a;
    diff = b - mem - borrow;
    u64 carry32 = (u32)b < (u32)a;
    u64 wide = mem + a + carry32;
    u64 carry64 = wide < mem || (carry32 && wide == mem);
    mem = wide;
    into = (u32)((u32)into - (u32)b - (u32)carry64);
#endif
    return ax1 ^ ((u64)ax2 << 16) ^ ((u64)ax3 << 32) ^ ((u64)(f1 | f2 << 1 | f3 << 2) << 48) ^ sum * 3 ^ diff * 5 ^
        mem * 7 ^ into * 11;
}
EXPORT shifts(u64 a, u64 b) {
    unsigned s = b & 63;
    return (a << s) ^ (a >> s) ^ (u64)((i64)a >> s) ^ ((u32)a << (s & 31)) ^ ((u32)a >> (s & 31)) ^
        (u64)(i64)((i32)a >> (s & 31));
}
EXPORT rotates(u64 a, u64 b) {
    unsigned s = b & 63;
    u64 r = (a << s) | (a >> ((64 - s) & 63));
    u32 x = (u32)a; unsigned t = b & 31;
    u32 y = (x >> t) | (x << ((32 - t) & 31));
    return r ^ ((u64)y << 7);
}
EXPORT bits(u64 a, u64 b) {
    u64 r = (u64)__builtin_popcountll(a) + ((u64)__builtin_popcount((u32)b) << 8);
    if (a) r += (u64)__builtin_ctzll(a) << 16 | (u64)__builtin_clzll(a) << 24;
    if ((u32)b) r += (u64)__builtin_ctz((u32)b) << 32 | (u64)__builtin_clz((u32)b) << 40;
    return r ^ __builtin_bswap64(a) ^ __builtin_bswap32((u32)b);
}
EXPORT narrow(u64 a, u64 b) {
    uint8_t x = (uint8_t)a; int8_t y = (int8_t)b; uint16_t z = (uint16_t)(a >> 8); int16_t w = (int16_t)(b >> 4);
    x += 200; y -= 100; z *= 3; w = (int16_t)(w * -7);
    return (u64)x | (u64)(uint8_t)y << 8 | (u64)z << 16 | (u64)(uint16_t)w << 32 | (u64)(i64)y << 48;
}
EXPORT compare(u64 a, u64 b) {
    u64 r = 0;
    r |= (u64)(a < b) << 0; r |= (u64)(a <= b) << 1; r |= (u64)(a > b) << 2; r |= (u64)(a >= b) << 3;
    r |= (u64)((i64)a < (i64)b) << 4; r |= (u64)((i64)a <= (i64)b) << 5; r |= (u64)((i64)a > (i64)b) << 6;
    r |= (u64)((i64)a >= (i64)b) << 7; r |= (u64)(a == b) << 8; r |= (u64)(a != b) << 9;
    r |= (u64)((u32)a < (u32)b) << 10; r |= (u64)((i32)a < (i32)b) << 11;
    r |= (u64)((uint8_t)a < (uint8_t)b) << 12; r |= (u64)((int16_t)a > (int16_t)b) << 13;
    return r;
}
EXPORT choose(u64 a, u64 b) {
    u64 m = (i64)a < (i64)b ? a : b;
    u64 x = a > b ? a - b : b - a;
    i64 c = (i64)a; c = c < -100 ? -100 : c > 100 ? 100 : c;
    return m * 3 + x + (u64)c + ((a & 1) ? 17 : 5);
}
EXPORT wide(u64 a, u64 b) {
    unsigned __int128 p = (unsigned __int128)a * b;
    __int128 q = (__int128)(i64)a * (i64)b;
    return (u64)(p >> 64) ^ (u64)p ^ (u64)(q >> 64) * 31;
}
EXPORT wide_div(u64 a, u64 b) {
    unsigned __int128 n = ((unsigned __int128)a << 64) | b;
    u64 d = (b | 1) & 0xffffffff;
    return (u64)(n / d) ^ (u64)(n % d);
}
EXPORT carries(u64 a, u64 b) {
    u64 lo, hi = 0;
    if (__builtin_add_overflow(a, b, &lo)) hi = 1;
    u64 d; int borrow = __builtin_sub_overflow(a, b, &d);
    i64 s; int ov = __builtin_add_overflow((i64)a, (i64)b, &s);
    i64 m; int mo = __builtin_mul_overflow((i64)a, (i64)b, &m);
    return lo ^ hi << 63 ^ d ^ (u64)borrow << 62 ^ (u64)ov << 61 ^ (u64)mo << 60 ^ (u64)s;
}
EXPORT loops(u64 a, u64 b) {
    u64 s = 0;
    for (u64 i = 0; i < (a & 255); i++) {
        if (i % 3 == 0) continue;
        for (u64 j = 0; j < (b & 15); j++) {
            if (j == 11) break;
            s += i * j ^ (s >> 3);
        }
        if (s > 1000000000) break;
    }
    u64 n = a | 1, steps = 0;
    while (n != 1 && steps < 1000) { n = n & 1 ? 3 * n + 1 : n / 2; steps++; }
    do { s += steps; steps >>= 1; } while (steps);
    return s;
}
EXPORT dense_switch(u64 a, u64 b) {
    u64 r = 0;
    for (u64 i = 0; i < 16; i++) {
        switch ((a + i * b) % 12) {
            case 0: r += 1; break;
            case 1: r ^= 0x55; break;
            case 2: r *= 3; break;
            case 3: r -= 7; break;
            case 4: r = r << 1 | 1; break;
            case 5: r = ~r; break;
            case 6: r += i; /* fallthrough */
            case 7: r += 100; break;
            case 8: r >>= 2; break;
            case 9: r = r * r; break;
            case 10: r += a; break;
            default: r ^= b; break;
        }
    }
    return r;
}
EXPORT sparse_switch(u64 a, u64 b) {
    switch (a) {
        case 3: return b + 1;
        case 100: return b * 2;
        case 1000: return b ^ 0xffff;
        case 77777: return b - 9;
        case 0xffffffffff: return 5;
        case (u64)-1: return 6;
        default: return a + b;
    }
}
static u64 fib(u64 n) { return n < 2 ? n : fib(n - 1) + fib(n - 2); }
EXPORT recursion(u64 a, u64 b) { return fib(a % 24) + b; }
static u64 ack(u64 m, u64 n) { return m == 0 ? n + 1 : n == 0 ? ack(m - 1, 1) : ack(m - 1, ack(m, n - 1)); }
EXPORT ackermann(u64 a, u64 b) { return ack(a % 3, b % 6); }
static int is_even(u64 n);
static int is_odd(u64 n) { return n == 0 ? 0 : is_even(n - 1); }
static int is_even(u64 n) { return n == 0 ? 1 : is_odd(n - 1); }
EXPORT mutual(u64 a, u64 b) { return (u64)is_even(a % 500) * 10 + (u64)is_odd(b % 300); }

typedef u64 (*binop)(u64, u64);
static u64 op_add(u64 a, u64 b) { return a + b; }
static u64 op_xor(u64 a, u64 b) { return a ^ b; }
static u64 op_mul(u64 a, u64 b) { return a * b | 1; }
static u64 op_sub(u64 a, u64 b) { return a - b; }
static binop table[] = {op_add, op_xor, op_mul, op_sub};
EXPORT pointers(u64 a, u64 b) {
    u64 r = a;
    for (unsigned i = 0; i < 9; i++) r = table[(b + i) & 3](r, b + i);
    return r;
}
struct node { u64 value; struct node* left; struct node* right; };
static struct node* insert(struct node* root, u64 value) {
    if (!root) {
        struct node* n = malloc(sizeof *n);
        n->value = value; n->left = n->right = 0;
        return n;
    }
    if (value < root->value) root->left = insert(root->left, value);
    else root->right = insert(root->right, value);
    return root;
}
static u64 walk(struct node* n, u64 depth) {
    if (!n) return 0;
    u64 r = walk(n->left, depth + 1) * 31 + n->value * depth + walk(n->right, depth + 1);
    free(n);
    return r;
}
EXPORT tree(u64 a, u64 b) {
    struct node* root = 0;
    u64 x = a | 1;
    for (unsigned i = 0; i < (b % 64) + 1; i++) {
        x ^= x << 13; x ^= x >> 7; x ^= x << 17;
        root = insert(root, x % 1000);
    }
    return walk(root, 1);
}
EXPORT vector(u64 a, u64 b) {
    u64 count = 0, capacity = 2;
    u64* items = malloc(capacity * sizeof *items);
    for (u64 i = 0; i < (a % 300) + 3; i++) {
        if (count == capacity) { capacity *= 2; items = realloc(items, capacity * sizeof *items); }
        items[count++] = i * b + (i >> 1);
    }
    u64 s = 0;
    for (u64 i = 0; i < count; i++) s = s * 1099511628211ull ^ items[i];
    free(items);
    return s ^ capacity;
}
struct pair { i32 x; i32 y; };
static int compare_pairs(const void* a, const void* b) {
    const struct pair* p = a; const struct pair* q = b;
    return p->x != q->x ? (p->x < q->x ? -1 : 1) : (p->y > q->y) - (p->y < q->y);
}
EXPORT sorting(u64 a, u64 b) {
    struct pair items[40];
    u64 x = a ^ 0x9e3779b97f4a7c15ull;
    for (unsigned i = 0; i < 40; i++) {
        x = x * 6364136223846793005ull + b;
        items[i].x = (i32)(x >> 60) - 8;
        items[i].y = (i32)(x >> 20);
    }
    // Insertion sort keeps this test independent of libc qsort.
    for (unsigned i = 1; i < 40; i++)
        for (unsigned j = i; j > 0 && compare_pairs(&items[j - 1], &items[j]) > 0; j--) {
            struct pair t = items[j]; items[j] = items[j - 1]; items[j - 1] = t;
        }
    u64 h = 0;
    for (unsigned i = 0; i < 40; i++) h = h * 31 + (u32)items[i].x * 7 + (u32)items[i].y;
    return h;
}
static const char* const words[] = {"alpha", "bravo", "charlie", "delta", "echo", "foxtrot", "golf", "hotel"};
EXPORT strings(u64 a, u64 b) {
    char buffer[128];
    const char* w = words[a % 8];
    size_t n = strlen(w);
    memcpy(buffer, w, n + 1);
    memmove(buffer + 2, buffer, n + 1);
    memset(buffer, '*', 2);
    u64 h = 5381;
    for (const char* p = buffer; *p; p++) h = h * 33 + (unsigned char)*p;
    int c = strcmp(words[a % 8], words[b % 8]), m = memcmp(w, words[b % 8], 3);
    // Only the sign of strcmp and memcmp is specified.
    return h + (u64)(i64)((c > 0) - (c < 0)) * 1000 + n + (u64)(i64)((m > 0) - (m < 0));
}
EXPORT stack_array(u64 a, u64 b) {
    u64 grid[16][16];
    for (unsigned i = 0; i < 16; i++)
        for (unsigned j = 0; j < 16; j++)
            grid[i][j] = (a + i) * (b + j) % 1009;
    for (unsigned k = 0; k < 3; k++)
        for (unsigned i = 1; i < 15; i++)
            for (unsigned j = 1; j < 15; j++)
                grid[i][j] = (grid[i - 1][j] + grid[i + 1][j] + grid[i][j - 1] + grid[i][j + 1]) / 4 + grid[i][j] % 3;
    u64 s = 0;
    for (unsigned i = 0; i < 16; i++) s = s * 7 + grid[i][15 - i];
    return s;
}
static u64 counter;
static u32 lcg_state = 12345;
EXPORT globals(u64 a, u64 b) {
    counter += a;
    lcg_state = lcg_state * 1103515245u + 12345u + (u32)b;
    static u64 calls;
    calls++;
    return counter ^ lcg_state ^ calls << 40;
}
union bitsu { double d; u64 u; float f[2]; u32 w[2]; };
static u64 dbits(double d) { u64 u; memcpy(&u, &d, 8); return u; }
static double bitsd(u64 u) { double d; memcpy(&d, &u, 8); return d; }
EXPORT doubles(u64 a, u64 b) {
    double x = (double)(i64)a / 1000.0, y = (double)b * 0.25 + 1.5;
    double r = x * y - x / y + (x > y ? x : y);
    r += __builtin_sqrt(y * y + 1.0);
    return dbits(r);
}
EXPORT floats(u64 a, u64 b) {
    float x = (float)(i32)a * 0.5f, y = (float)(u32)b / 3.0f + 0.125f;
    float r = x * y + x - y / (x + 1000.0f);
    union bitsu u; u.f[0] = r; u.f[1] = x < y ? y : x;
    return u.u;
}
EXPORT conversions(u64 a, u64 b) {
    double d = bitsd(b);
    if (d != d || d > 1e18 || d < -1e18) d = 12.75;
    i64 t = (i64)d;
    u64 v = (u64)(d < 0 ? -d : d);
    float f = (float)(i64)a;
    i32 g = (i32)(f / 1e10f);
    double h = (double)a;
    return (u64)t ^ v << 3 ^ (u64)(i64)g << 20 ^ dbits(h) ^ dbits((double)(u32)a);
}
EXPORT float_compare(u64 a, u64 b) {
    double x = bitsd(a), y = bitsd(b);
    u64 r = 0;
    r |= (u64)(x < y) << 0; r |= (u64)(x <= y) << 1; r |= (u64)(x > y) << 2; r |= (u64)(x >= y) << 3;
    r |= (u64)(x == y) << 4; r |= (u64)(x != y) << 5; r |= (u64)(x != x) << 6;
    r |= (u64)__builtin_isless(x, y) << 7; r |= (u64)__builtin_isunordered(x, y) << 8;
    return r;
}
EXPORT rounding(u64 a, u64 b) {
    double x = (double)(i64)a / 7.0 + (double)(i64)b / 1e6;
    return dbits(__builtin_floor(x)) ^ dbits(__builtin_ceil(x)) * 3 ^ dbits(__builtin_trunc(x)) * 5 ^
        dbits(__builtin_fabs(x)) * 7 ^ (u64)__builtin_llround(x) * 11;
}
static u64 sum_va(int count, ...) {
    va_list list;
    va_start(list, count);
    u64 s = 0;
    for (int i = 0; i < count; i++) s = s * 3 + va_arg(list, u64);
    va_end(list);
    return s;
}
EXPORT varargs(u64 a, u64 b) { return sum_va(7, a, b, a + b, a * b, a ^ b, (u64)5, (u64)6) + sum_va(2, b, a); }
static jmp_buf jump;
static u64 jumped;
static void deep(u64 n) { if (n == 0) longjmp(jump, 7); jumped += n; deep(n - 1); }
EXPORT jumps(u64 a, u64 b) {
    jumped = 0;
    int r = setjmp(jump);
    if (r == 0) { deep(a % 20); return 1; }
    return jumped * 100 + (u64)r + b;
}
struct big { u64 a, b, c, d, e; u32 f; uint8_t g; };
static struct big make_big(u64 x) { struct big r = {x, x * 2, x * 3, x ^ 5, x + 9, (u32)x, (uint8_t)x}; return r; }
static u64 use_big(struct big v) { return v.a + v.b * 3 + v.c * 5 + v.d * 7 + v.e * 11 + v.f + v.g; }
EXPORT structs(u64 a, u64 b) { struct big x = make_big(a); x.c += b; return use_big(x); }
struct flags { unsigned a : 3; unsigned b : 7; signed c : 5; unsigned d : 17; };
EXPORT bitfields(u64 a, u64 b) {
    struct flags f;
    memset(&f, 0, sizeof f);
    f.a = a; f.b = b; f.c = (int)(a >> 8); f.d = (unsigned)(b >> 3);
    f.a += 5; f.c -= 3;
    return (u64)f.a | (u64)f.b << 8 | (u64)(i64)f.c << 16 | (u64)f.d << 40;
}
EXPORT memory_ops(u64 a, u64 b) {
    unsigned char buffer[300];
    for (unsigned i = 0; i < sizeof buffer; i++) buffer[i] = (unsigned char)(i * a + b);
    u64 x;
    memcpy(&x, buffer + (a % 200), sizeof x);
    u32 y;
    memcpy(&y, buffer + (b % 250) + 1, sizeof y);
    uint16_t z;
    memcpy(&z, buffer + 3, 2);
    memset(buffer + 10, (int)a, 100);
    u64 s = 0;
    for (unsigned i = 0; i < sizeof buffer; i += 7) s += buffer[i];
    return x ^ y ^ (u64)z << 32 ^ s;
}
EXPORT hashing(u64 a, u64 b) {
    u64 h = 0xcbf29ce484222325ull ^ b;
    for (unsigned i = 0; i < 64; i++) {
        h ^= (a >> (i % 57)) & 0xff;
        h *= 0x100000001b3ull;
        h = (h << 13 | h >> 51) + i;
    }
    u32 c = (u32)~0u;
    for (unsigned i = 0; i < 8; i++) {
        c ^= (uint8_t)(a >> (i * 8));
        for (unsigned k = 0; k < 8; k++) c = c >> 1 ^ (0xedb88320u & -(c & 1));
    }
    return h ^ ~c;
}
