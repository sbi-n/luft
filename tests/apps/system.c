// LUFT: {"args": ["system"], "skip": ["x86_64-pe"]}
// POSIX services that real programs such as SQLite and Lua rely on: pseudo-random sequences, the usable size of
// allocations across realloc, positioned I/O, fcntl locks, temporary files, file system statistics, signal sets,
// and tables of pointers to C library functions. It also exercises code shapes compilers emit for them: a switch
// over every value of an enumeration, which needs no bounds check, and byte loops that vectorize.
#include <ctype.h>
#include <fcntl.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mount.h>
#include <sys/resource.h>
#include <unistd.h>
#ifdef __APPLE__
#include <malloc/malloc.h>
#define usable(p) malloc_size(p)
#else
#include <malloc.h>
#include <sys/vfs.h>
#define usable(p) malloc_usable_size(p)
#endif

enum Shape { Circle, Square, Triangle, Hexagon, Star, Line, Dot, Ring, Cross, Arrow, Heart };

static int __attribute__((noinline)) corners(enum Shape shape) {
    switch (shape) {
        case Circle: return 0;
        case Square: return 4;
        case Triangle: return 3;
        case Hexagon: return 6;
        case Star: return 10;
        case Line: return 2;
        case Dot: return 1;
        case Ring: return 100;
        case Cross: return 12;
        case Arrow: return 7;
        case Heart: return 31;
    }
    __builtin_unreachable();
}

static int __attribute__((noinline)) dot(const signed char* a, const signed char* b, int n) {
    int sum = 0;
    for (int i = 0; i < n; ++i) sum += a[i] * b[i];
    return sum;
}

static uint32_t __attribute__((noinline)) swapHalves(uint32_t x) {
    return ((x & 0x00ff00ffu) << 8) | ((x >> 8) & 0x00ff00ffu);
}

// A table of C library functions, as SQLite keeps its system calls: code loads them at run time.
typedef size_t (*Length)(const char*);
typedef int (*Convert)(int);
static struct {
    const char* name;
    void (*function)(void);
} calls[] = {{"strlen", (void (*)(void))strlen}, {"toupper", (void (*)(void))toupper}, {"abs", (void (*)(void))abs}};

int main(void) {
    printf("rand %d %d", rand(), rand());
    srand(5);
    printf(" srand5 %d", rand());
    printf(" random %ld", random());
    srandom(9);
    printf(" srandom9 %ld %ld\n", random(), random());

    char* block = malloc(5);
    size_t size = usable(block);
    for (size_t i = 0; i < size; ++i) block[i] = (char)(i * 7 + 1);
    block = realloc(block, 4096);
    int kept = 1;
    for (size_t i = 0; i < size; ++i) kept &= block[i] == (char)(i * 7 + 1);
    printf("usable %d kept %d\n", size >= 5, kept);
    free(block);

    int fd = open("positioned.txt", O_CREAT | O_RDWR | O_TRUNC, 0644);
    write(fd, "hello world", 11);
    pwrite(fd, "WORLD", 5, 6);
    char text[16] = {0};
    pread(fd, text, 11, 0);
    printf("pread %s at %ld\n", text, (long)lseek(fd, 0, SEEK_CUR));
    struct flock lock = {0};
    lock.l_type = F_WRLCK;
    lock.l_whence = SEEK_SET;
    lock.l_len = 1;
    int set = fcntl(fd, F_SETLK, &lock);
    lock.l_type = F_RDLCK;
    int got = fcntl(fd, F_GETLK, &lock);
    printf("fcntl %d %d %d %d\n", (fcntl(fd, F_GETFL) & O_ACCMODE) == O_RDWR, set, got, lock.l_type == F_UNLCK);
    struct statfs volume;
    int statistics = fstatfs(fd, &volume);
    printf("fstatfs %d %d\n", statistics, volume.f_bsize > 0);
    close(fd);

    FILE* scratch = tmpfile();
    fputs("scratch data", scratch);
    rewind(scratch);
    char back[32] = {0};
    fgets(back, sizeof back, scratch);
    fclose(scratch);
    char first[L_tmpnam], second[L_tmpnam];
    printf("tmpfile %s tmpnam %d\n", back, tmpnam(first) && tmpnam(second) && strcmp(first, second) != 0);

    sigset_t signals, previous;
    sigemptyset(&signals);
    sigaddset(&signals, SIGINT);
    printf("sigset %d %d", sigismember(&signals, SIGINT), sigismember(&signals, SIGTERM));
    sigdelset(&signals, SIGINT);
    printf(" %d", sigismember(&signals, SIGINT));
    sigfillset(&signals);
    printf(" %d mask %d raise %d\n", sigismember(&signals, SIGUSR1), sigprocmask(SIG_BLOCK, &signals, &previous),
        raise(SIGCHLD));
    struct rusage usage;
    printf("rusage %d ids %d\n", getrusage(RUSAGE_SELF, &usage), getuid() == geteuid());

    int total = 0;
    for (int shape = Circle; shape <= Heart; ++shape) total = total * 3 + corners((enum Shape)shape);
    signed char a[61], b[61];
    for (int i = 0; i < 61; ++i) a[i] = (signed char)(i * 37 - 90), b[i] = (signed char)(100 - i * 11);
    uint32_t mixed = 0;
    for (uint32_t i = 0; i < 1000; ++i) mixed = mixed * 31 + swapHalves(i * 0x01020304u);
    printf("switch %d dot %d halves %u\n", total, dot(a, b, 61), mixed);

    volatile int pick = 0;
    size_t length = ((Length)calls[pick].function)("function pointers");
    pick = 1;
    int upper = ((Convert)calls[pick].function)('q');
    pick = 2;
    int absolute = ((Convert)calls[pick].function)(-42);
    printf("%s %zu %s %c %s %d\n", calls[0].name, length, calls[1].name, upper, calls[2].name, absolute);
    return 0;
}
