// LUFT: {"args": ["posix_formats"], "skip": ["x86_64-pe"]}
// printf and strtod as glibc and Darwin implement them where msvcrt differs: %e exponents, infinities and NaNs,
// %a, hexadecimal floating-point input, the range errors of strtod and strtol, and long double arguments.
#include <errno.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>

static void say(const char* format, ...) {
    char buffer[256];
    va_list list;
    va_start(list, format);
    vsnprintf(buffer, sizeof buffer, format, list);
    va_end(list);
    printf("%s\n", buffer);
}

int main(void) {
    const double infinity = 1e308 * 10;
    printf("[%e] [%.3E] [%G] [%e] [%.0e] [%#.0e] [%.105e]\n", 12345.678, 0.000123, 1e20, 0.0, 5.5, 5.0, 1e-300);
    printf("[%f] [%F] [%e] [%g] [%5.1f] [%-6f|] [%+f]\n", infinity, -infinity, infinity, -infinity, infinity, infinity,
        infinity);
    printf("[%a] [%a] [%a] [%A] [%a] [%.2a] [%#a] [%.120g]\n", 1.0, 3.0, 0.1, -0.5, 0.0, 1.0 / 3, 2.0, 1.0 / 3);
    // Subnormals, which glibc and Darwin write differently, and zero padding, which follows the 0x.
    printf("[%a] [%a] [%.3a] [%020a] [%-12a] [%020.2a]\n", 4.9e-324, -1.5e-310, 2.2250738585072009e-308, 1.0, 0.5,
        -2.5);
    const char* texts[] = {"1e400", "-1e400", "0x1.8p1", "0X10", "0x1p", "0x.8", "inf", "-INF", "nan", "-nan",
        "nan(123)x", "Infinity", "infinit"};
    for (int i = 0; i < 13; i++) {
        char* end;
        errno = 0;
        const double d = strtod(texts[i], &end);
        printf("strtod(%s) = %g consumed %d range %d\n", texts[i], d, (int)(end - texts[i]), errno == ERANGE);
    }
    errno = 0;
    char* end;
    const long value = strtol("junk", &end, 10);
    printf("strtol(junk) = %ld consumed %d\n", value, (int)(end - "junk"));
    const long double third = (long double)2 / 3;
    printf("%Lf %d %f %Lg %.3Le %s %Lg\n", (long double)1.5, 7, 2.25, (long double)0.1, third, "end", -third * 1e10L);
    say("%d %Lf %.2f %Lg %Lg %Lg %Lg %Lg %Lg %Lg %Lg %Lg", 1, (long double)0.25, 0.5, third, third * 2, third * 3,
        third * 4, third * 5, third * 6, third * 7, third * 8, third * 9);
    return 0;
}
