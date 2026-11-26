// Compute-bound workloads that compilers vectorize and unroll: hashing, sorting, a hash table of strings,
// floating-point matrices, a bytecode interpreter, and a binary tree. Each prints a checksum.
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static uint32_t rotr(uint32_t x, int n) { return (x >> n) | (x << (32 - n)); }

static void sha256(const uint8_t* data, size_t length, uint32_t out[8]) {
    static const uint32_t k[64] = {
        0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
        0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
        0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
        0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
        0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
        0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
        0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
        0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2};
    uint32_t h[8] = {0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19};
    for (size_t block = 0; block + 64 <= length; block += 64) {
        uint32_t w[64];
        for (int i = 0; i < 16; ++i)
            w[i] = (uint32_t)data[block + 4 * i] << 24 | (uint32_t)data[block + 4 * i + 1] << 16 |
                (uint32_t)data[block + 4 * i + 2] << 8 | data[block + 4 * i + 3];
        for (int i = 16; i < 64; ++i) {
            uint32_t s0 = rotr(w[i - 15], 7) ^ rotr(w[i - 15], 18) ^ (w[i - 15] >> 3);
            uint32_t s1 = rotr(w[i - 2], 17) ^ rotr(w[i - 2], 19) ^ (w[i - 2] >> 10);
            w[i] = w[i - 16] + s0 + w[i - 7] + s1;
        }
        uint32_t a = h[0], b = h[1], c = h[2], d = h[3], e = h[4], f = h[5], g = h[6], hh = h[7];
        for (int i = 0; i < 64; ++i) {
            uint32_t t1 = hh + (rotr(e, 6) ^ rotr(e, 11) ^ rotr(e, 25)) + ((e & f) ^ (~e & g)) + k[i] + w[i];
            uint32_t t2 = (rotr(a, 2) ^ rotr(a, 13) ^ rotr(a, 22)) + ((a & b) ^ (a & c) ^ (b & c));
            hh = g; g = f; f = e; e = d + t1; d = c; c = b; b = a; a = t1 + t2;
        }
        h[0] += a; h[1] += b; h[2] += c; h[3] += d; h[4] += e; h[5] += f; h[6] += g; h[7] += hh;
    }
    memcpy(out, h, sizeof h);
}

static uint64_t state = 88172645463325252ull;
static uint64_t next(void) {
    state ^= state << 13;
    state ^= state >> 7;
    state ^= state << 17;
    return state;
}

static void quicksort(int* items, int low, int high) {
    while (low < high) {
        int pivot = items[(low + high) / 2], i = low, j = high;
        while (i <= j) {
            while (items[i] < pivot) ++i;
            while (items[j] > pivot) --j;
            if (i <= j) {
                int t = items[i]; items[i] = items[j]; items[j] = t;
                ++i; --j;
            }
        }
        if (j - low < high - i) { quicksort(items, low, j); low = i; }
        else { quicksort(items, i, high); high = j; }
    }
}

struct Entry { char key[16]; int count; struct Entry* next; };

static unsigned hashString(const char* s) {
    unsigned h = 2166136261u;
    while (*s) h = (h ^ (unsigned char)*s++) * 16777619u;
    return h;
}

static int words(void) {
    struct Entry* table[1024] = {0};
    char word[16];
    int distinct = 0;
    for (int i = 0; i < 6000; ++i) {
        int length = 1 + (int)(next() % 6);
        for (int j = 0; j < length; ++j) word[j] = (char)('a' + next() % 6);
        word[length] = 0;
        unsigned slot = hashString(word) & 1023;
        struct Entry* entry = table[slot];
        while (entry && strcmp(entry->key, word) != 0) entry = entry->next;
        if (!entry) {
            entry = malloc(sizeof *entry);
            strcpy(entry->key, word);
            entry->count = 0;
            entry->next = table[slot];
            table[slot] = entry;
            ++distinct;
        }
        ++entry->count;
    }
    int best = 0;
    for (int i = 0; i < 1024; ++i)
        for (struct Entry* entry = table[i]; entry;) {
            struct Entry* following = entry->next;
            if (entry->count > best) best = entry->count;
            free(entry);
            entry = following;
        }
    return distinct * 1000 + best;
}

static double matrix(void) {
    enum { N = 24 };
    static double a[N][N], b[N][N], c[N][N];
    for (int i = 0; i < N; ++i)
        for (int j = 0; j < N; ++j) {
            a[i][j] = (double)((i * 7 + j * 3) % 11) / 4.0;
            b[i][j] = (double)((i * 5 + j * 9) % 13) / 8.0;
        }
    for (int i = 0; i < N; ++i)
        for (int j = 0; j < N; ++j) {
            double sum = 0;
            for (int k = 0; k < N; ++k) sum += a[i][k] * b[k][j];
            c[i][j] = sum;
        }
    double trace = 0;
    for (int i = 0; i < N; ++i) trace += c[i][i] + c[i][N - 1 - i];
    return trace;
}

// A stack machine running a counted loop that sums a polynomial.
static int64_t interpret(int iterations) {
    enum { PUSH, LOAD, STORE, ADD, MUL, SUB, JNZ, HALT };
    const int program[] = {
        PUSH, 0, STORE, 1,          // acc = 0
        LOAD, 0, LOAD, 0, MUL,      // i * i
        PUSH, 3, LOAD, 0, MUL, ADD, // + 3 * i
        LOAD, 1, ADD, STORE, 1,     // acc += ...
        LOAD, 0, PUSH, 1, SUB, STORE, 0,
        LOAD, 0, JNZ, 4, HALT};
    int64_t stack[16], vars[2] = {iterations, 0};
    int sp = 0, pc = 0;
    for (;;) {
        switch (program[pc++]) {
            case PUSH: stack[sp++] = program[pc++]; break;
            case LOAD: stack[sp++] = vars[program[pc++]]; break;
            case STORE: vars[program[pc++]] = stack[--sp]; break;
            case ADD: --sp; stack[sp - 1] += stack[sp]; break;
            case MUL: --sp; stack[sp - 1] *= stack[sp]; break;
            case SUB: --sp; stack[sp - 1] -= stack[sp]; break;
            case JNZ: { int target = program[pc++]; if (stack[--sp]) pc = target; break; }
            case HALT: return vars[1];
        }
    }
}

struct Node { int key; struct Node* left; struct Node* right; };

static struct Node* insert(struct Node* root, int key) {
    struct Node** link = &root;
    while (*link) link = key < (*link)->key ? &(*link)->left : &(*link)->right;
    *link = calloc(1, sizeof **link);
    (*link)->key = key;
    return root;
}

static int64_t walk(const struct Node* node, int depth) {
    if (!node) return 0;
    return (int64_t)node->key * depth + walk(node->left, depth + 1) + walk(node->right, depth + 1);
}

static void release(struct Node* node) {
    if (!node) return;
    release(node->left);
    release(node->right);
    free(node);
}

// Windows has a 32-bit long, and msvcrt formats 64-bit integers differently: print both halves in hex.
static void printWide(const char* name, int64_t value) {
    printf("%s %08x%08x\n", name, (unsigned)((uint64_t)value >> 32), (unsigned)value);
}

int main(int argc, char** argv) {
    const char* only = argc > 1 ? argv[1] : "";
    if (!*only || !strcmp(only, "sha")) {
        static uint8_t data[64 * 64];
        for (size_t i = 0; i < sizeof data; ++i) data[i] = (uint8_t)(i * 31 + 7);
        uint32_t digest[8];
        sha256(data, sizeof data, digest);
        printf("sha %08x%08x\n", digest[0], digest[7]);
    }
    if (!*only || !strcmp(only, "sort")) {
        int* items = malloc(5000 * sizeof *items);
        for (int i = 0; i < 5000; ++i) items[i] = (int)(next() % 100000);
        quicksort(items, 0, 4999);
        int64_t check = 0;
        for (int i = 0; i < 5000; i += 97) check += (int64_t)items[i] * i;
        printWide("sort", check);
        free(items);
    }
    if (!*only || !strcmp(only, "words")) printf("words %d\n", words());
    if (!*only || !strcmp(only, "matrix")) printf("matrix %.4f\n", matrix());
    if (!*only || !strcmp(only, "interp")) printWide("interp", interpret(8000));
    if (!*only || !strcmp(only, "tree")) {
        struct Node* root = NULL;
        for (int i = 0; i < 3000; ++i) root = insert(root, (int)(next() % 1000000));
        printWide("tree", walk(root, 1));
        release(root);
    }
    return 0;
}
