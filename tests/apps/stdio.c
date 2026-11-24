// LUFT: {"args": ["stdio", "in.txt"], "stdin": "l1\nl2\n", "files": {"in.txt": "file contents\n"}, "env": ["HOME=/home/guest"], "outputs": ["out.txt"]}
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
static void bye(void) { printf("atexit ran\n"); }
int main(int argc, char** argv) {
    atexit(bye);
    printf("argc=%d\n", argc);
    for (int i = 0; i < argc; i++) printf("argv[%d]=%s\n", i, argv[i]);
    printf("%5d|%-5d|%05.1f|%x|%llu|%s|%c|%.3e|%g\n", 42, -7, 3.14159, 255, 18446744073709551615ull, "str", 'Z', 12345.678, 0.0001);
    FILE* f = fopen(argc > 1 ? argv[1] : "in.txt", "rb");
    if (!f) { fprintf(stderr, "cannot open\n"); return 3; }
    char buffer[256]; size_t n = fread(buffer, 1, sizeof buffer - 1, f); buffer[n] = 0; fclose(f);
    printf("read %zu bytes: %s", n, buffer);
    char line[64];
    while (fgets(line, sizeof line, stdin)) printf("stdin: %s", line);
    FILE* out = fopen("out.txt", "w"); fprintf(out, "written %d\n", 99); fclose(out);
    const char* home = getenv("HOME"); printf("HOME=%s\n", home ? home : "(none)");
    return 5;
}
