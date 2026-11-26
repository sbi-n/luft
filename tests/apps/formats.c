// LUFT: {"args": ["formats", "12345", "-3.25e2", "0x1f", "077", "junk"]}
// The C library's formatting and parsing: printf conversions, flags, widths, and precisions, vsnprintf with a
// va_list, strtol and strtod with bases and end pointers, sorting and searching, and string and memory routines.
// What msvcrt formats or parses differently from glibc, whose output Windows builds are compared with, is in
// posix_formats.c.
#include <ctype.h>
#include <errno.h>
#include <limits.h>
#include <stdarg.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int compare_ints(const void* a, const void* b) {
    const int x = *(const int*)a, y = *(const int*)b;
    return (x > y) - (x < y);
}

static int compare_names(const void* a, const void* b) { return strcmp(*(const char* const*)a, *(const char* const*)b); }

static void say(const char* format, ...) {
    char buffer[256];
    va_list list;
    va_start(list, format);
    const int n = vsnprintf(buffer, sizeof buffer, format, list);
    va_end(list);
    printf("%d:%s\n", n, buffer);
}

static void integers(void) {
    printf("[%d] [%5d] [%-5d|] [%05d] [%+d] [% d] [%i]\n", 42, 42, 42, -42, 42, 42, -0);
    printf("[%u] [%x] [%X] [%#x] [%#X] [%o] [%#o] [%#x]\n", 4000000000u, 0xdeadbeefu, 0xdeadbeefu, 255u, 255u, 8u, 8u, 0u);
    printf("[%lld] [%llu] [%llx] [%lli]\n", (long long)INT64_MIN, (unsigned long long)UINT64_MAX, 0x123456789abcdefULL,
        -1LL);
    printf("[%hhd] [%hhu] [%hd] [%hu]\n", (signed char)-56, (unsigned char)200, (short)-30000, (unsigned short)65000);
    printf("[%.0d] [%.3d] [%8.3d] [%-8.3d|] [%08.3d]\n", 0, 7, -7, 7, 7);
    printf("[%*d] [%-*d|] [%*d] [%.*d]\n", 6, 7, 6, 7, -6, 7, 4, 3);
}

static void strings(void) {
    printf("[%s] [%10s] [%-10s|] [%.3s] [%10.2s] [%c] [%3c] [%-3c|] [%%]\n", "abc", "abc", "abc", "abcdef", "abcdef",
        'Z', 'y', 'x');
    // A precision bounds arrays that need no terminator, here one that ends a heap block.
    char* raw = malloc(4096);
    memset(raw, 'r', 4096);
    printf("[%.*s] [%.3s]\n", 5, raw + 4091, raw + 4093);
    free(raw);
}

static void reals(void) {
    printf("[%f] [%.2f] [%10.3f] [%-10.1f|] [%+.1f] [% .1f] [%010.2f]\n", 3.14159, 2.675, -1.5, 0.05, 1.0, 1.0, -3.5);
    printf("[%.0f] [%.0f] [%.0f] [%.1f] [%.3f] [%#.0f]\n", 0.5, 1.5, 2.5, 0.25, 1e-10, 3.0);
    printf("[%f] [%.15f] [%.17g] [%.20f]\n", 1e15, 0.1, 0.1, 1.0 / 3);
    printf("[%g] [%g] [%g] [%g] [%.3g] [%.10g] [%#g] [%g]\n", 100000.0, 1e6, 1e-4, 1e-5, 3.14159, 1.0 / 3, 1.0, 0.0);
    printf("[%f] [%.2f] [%.120f]\n", -0.0, -0.001, 0.1);
    printf("[%120.3f]\n", 2.5);
}

static void formatting(void) {
    char small[8];
    int n = snprintf(small, sizeof small, "%s-%d", "truncate", 12345);
    printf("snprintf %d [%s]\n", n, small);
    n = snprintf(NULL, 0, "%d%s", 123456, "abc");
    printf("measure %d\n", n);
    say("%s=%d %.2f %c %lld", "say", 5, 2.5, 'q', 9876543210LL);
    say("%5s|%-5s|%05d", "ab", "cd", 42);
    say("%d %d %d %d %d %d %d %d %d %d %.1f %.1f %.1f %.1f %.1f %.1f %.1f %.1f %.1f %.1f", 1, 2, 3, 4, 5, 6, 7, 8, 9,
        10, 1.5, 2.5, 3.5, 4.5, 5.5, 6.5, 7.5, 8.5, 9.5, 10.5);
    char built[64];
    sprintf(built, "%d/%x/%s", 10, 10, "ten");
    printf("sprintf [%s] %d\n", built, (int)strlen(built));
}

static void parsing(int argc, char** argv) {
    for (int i = 1; i < argc; i++) {
        char* end;
        errno = 0;
        const long value = strtol(argv[i], &end, 0);
        printf("strtol(%s) = %ld rest [%s] errno %d\n", argv[i], value, end, errno != 0);
        const double d = strtod(argv[i], &end);
        printf("strtod(%s) = %.6g rest [%s]\n", argv[i], d, end);
    }
    const char* numbers[] = {"  -17", "+42xyz", "0x7fffffff", "zz", "1010", "777", "9223372036854775807",
        "99999999999999999999", "-0x10", "-9223372036854775809", ""};
    const int bases[] = {10, 10, 16, 36, 2, 8, 10, 10, 16, 10, 10};
    for (int i = 0; i < 11; i++) {
        char* end;
        errno = 0;
        const long long value = strtoll(numbers[i], &end, bases[i]);
        const int range = errno == ERANGE;
        const unsigned long long unsignedValue = strtoull(numbers[i], NULL, bases[i]);
        printf("strtoll(%s, %d) = %lld %llu rest [%s] range %d\n", numbers[i], bases[i], value, unsignedValue, end,
            range);
    }
    const char* texts[] = {"3.5", "-2.5e-3", "1e308", "  .5", "5.", "1e", "abc", "1e-400"};
    for (int i = 0; i < 8; i++) {
        char* end;
        const double d = strtod(texts[i], &end);
        printf("strtod(%s) = %g consumed %d\n", texts[i], d, (int)(end - texts[i]));
    }
    printf("atoi %d %d atol %ld atof %.3f\n", atoi(" 123abc"), atoi("-9"), atol("77"), atof("2.5e1"));
}

static void searching(void) {
    int values[] = {5, -3, 9, 0, 9, -100, 42, 7, 7, 1};
    qsort(values, 10, sizeof values[0], compare_ints);
    for (int i = 0; i < 10; i++)
        printf("%d%c", values[i], i == 9 ? '\n' : ' ');
    int key = 42;
    const int* found = bsearch(&key, values, 10, sizeof values[0], compare_ints);
    printf("bsearch 42 at %d\n", found ? (int)(found - values) : -1);
    key = 8;
    printf("bsearch 8 %s\n", bsearch(&key, values, 10, sizeof values[0], compare_ints) ? "found" : "missing");
    const char* names[] = {"pear", "apple", "fig", "banana", "cherry"};
    qsort(names, 5, sizeof names[0], compare_names);
    for (int i = 0; i < 5; i++)
        printf("%s%c", names[i], i == 4 ? '\n' : ',');
}

static void text(void) {
    char line[64] = "hello, world";
    printf("strchr [%s] strrchr [%s] strstr [%s] strpbrk [%s]\n", strchr(line, 'o'), strrchr(line, 'o'),
        strstr(line, "wor"), strpbrk(line, ", "));
    printf("strspn %d strcspn %d strncmp %d %d\n", (int)strspn(line, "leh"), (int)strcspn(line, " ,"),
        strncmp(line, "help", 3), strncmp(line, "help", 4) < 0);
    strcat(line, "!");
    strncat(line, "???", 2);
    printf("cat [%s]\n", line);
    char copy[16];
    strncpy(copy, "abc", sizeof copy);
    printf("strncpy [%s] %d\n", copy, copy[15]);
    for (char* token = strtok(line, " ,!"); token; token = strtok(NULL, " ,!"))
        printf("token [%s]\n", token);
    char* duplicate = strdup("duplicate");
    printf("strdup [%s] toupper %c tolower %c isdigit %d isspace %d isalpha %d isxdigit %d\n", duplicate,
        toupper('q'), tolower('Q'), isdigit('7') != 0, isspace('\t') != 0, isalpha('_') != 0, isxdigit('F') != 0);
    free(duplicate);
}

static void memory(void) {
    char block[32];
    memset(block, 'x', sizeof block);
    memcpy(block, "0123456789", 10);
    memmove(block + 2, block, 8);
    block[12] = 0;
    printf("memmove [%s] memcmp %d %d memchr %d\n", block, memcmp("abc", "abd", 3) < 0, memcmp("abc", "abc", 3),
        (int)((char*)memchr(block, '5', 12) - block));
    int* grow = NULL;
    for (int i = 1; i <= 100; i++) {
        grow = realloc(grow, i * sizeof *grow);
        grow[i - 1] = i * i;
    }
    long long sum = 0;
    for (int i = 0; i < 100; i++)
        sum += grow[i];
    free(grow);
    int* zeros = calloc(50, sizeof *zeros);
    int nonzero = 0;
    for (int i = 0; i < 50; i++)
        nonzero += zeros[i] != 0;
    free(zeros);
    printf("realloc sum %lld calloc nonzero %d\n", sum, nonzero);
}

int main(int argc, char** argv) {
    integers();
    strings();
    reals();
    formatting();
    parsing(argc, argv);
    searching();
    text();
    memory();
    return 0;
}
