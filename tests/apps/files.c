// LUFT: {"args": ["files"], "files": {"data/input.txt": "alpha 12 3.5\nbeta -7 0x1p3\n", "data/sub/deep.txt": "x"}, "outputs": ["data/moved.txt", "made/inner/note.txt"], "skip": ["x86_64-pe"]}
// The POSIX file system as programs walk it: paths relative to the working directory, directories listed and
// made, files renamed and removed, stat and access, realpath and getcwd, errors and their messages; and the
// calendar (gmtime, timegm, strftime) and formatted input (sscanf, fscanf).
#include <dirent.h>
#include <errno.h>
#include <fcntl.h>
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <time.h>
#include <unistd.h>

static int compare(const void* a, const void* b) { return strcmp(*(char* const*)a, *(char* const*)b); }

static void list(const char* path) {
    DIR* dir = opendir(path);
    if (!dir) { printf("opendir %s: %s\n", path, strerror(errno)); return; }
    char* names[32];
    int count = 0;
    struct dirent* entry;
    while ((entry = readdir(dir)) && count < 32)
        if (strcmp(entry->d_name, ".") && strcmp(entry->d_name, ".."))
            names[count++] = strdup(entry->d_name);
    closedir(dir);
    qsort(names, count, sizeof *names, compare);
    printf("%s:", path);
    for (int i = 0; i < count; ++i) { printf(" %s", names[i]); free(names[i]); }
    printf("\n");
}

static void describe(const char* path) {
    struct stat info;
    if (stat(path, &info) != 0) { printf("stat %s: %s\n", path, strerror(errno)); return; }
    printf("stat %s: %s size %lld\n", path, S_ISDIR(info.st_mode) ? "directory" : S_ISREG(info.st_mode) ? "file" : "other",
        S_ISREG(info.st_mode) ? (long long)info.st_size : 0LL);
}

int main(void) {
    char cwd[PATH_MAX], resolved[PATH_MAX];
    if (!getcwd(cwd, sizeof cwd)) return 1;
    if (!realpath("data/./sub/../input.txt", resolved)) return 2;
    printf("realpath relative to cwd: %s\n", strncmp(resolved, cwd, strlen(cwd)) == 0 ? resolved + strlen(cwd) : resolved);
    list("data");
    describe("data");
    describe("data/input.txt");
    describe("data/missing.txt");
    describe("data/input.txt/inside");
    printf("access %d %d\n", access("data/input.txt", F_OK), access("nothing", F_OK) == -1 && errno == ENOENT);
    printf("mkdir %d", mkdir("made", 0755));
    printf(" %d", mkdir("made", 0755) == -1 && errno == EEXIST);
    printf(" %d", mkdir("made/inner", 0755));
    printf(" %d\n", mkdir("absent/inner", 0755) == -1 && errno == ENOENT);
    FILE* note = fopen("made/inner/note.txt", "w");
    fprintf(note, "written %d\n", 42);
    fclose(note);
    printf("fopen missing dir: %d\n", fopen("absent/file.txt", "w") == NULL && errno == ENOENT);
    int fd = open("data/sub/deep.txt", O_RDONLY);
    char byte = 0;
    printf("open/read %d %c\n", fd >= 0 && read(fd, &byte, 1) == 1, byte);
    close(fd);
    printf("O_EXCL %d\n", open("data/sub/deep.txt", O_CREAT | O_EXCL | O_WRONLY, 0644) == -1 && errno == EEXIST);
    printf("rename %d\n", rename("data/sub/deep.txt", "data/moved.txt"));
    printf("rmdir %d\n", rmdir("data/sub"));
    printf("rmdir nonempty %d\n", rmdir("data") == -1 && (errno == ENOTEMPTY || errno == EEXIST));
    printf("unlink %d %d\n", unlink("data/moved.txt") == 0 ? 0 : -1, unlink("data/moved.txt") == -1 && errno == ENOENT);
    note = fopen("data/moved.txt", "w");
    fputs("moved\n", note);
    fclose(note);
    list("data");
    list(".");
    printf("chdir %d\n", chdir("made"));
    list(".");
    describe("inner/note.txt");
    printf("chdir back %d\n", chdir(".."));
    printf("strerror: [%s] [%s]\n", strerror(ENOENT), strerror(EISDIR));

    // Calendar time in UTC, which does not depend on the host's time zone.
    time_t moment = 1700000000;
    struct tm parts;
    gmtime_r(&moment, &parts);
    char text[128];
    strftime(text, sizeof text, "%Y-%m-%d %H:%M:%S %a %b %j %U %W %V %G %u %w %p %I %e|%C %y %D %F %T %R %%", &parts);
    printf("strftime %s\n", text);
    parts.tm_mday += 40;
    parts.tm_hour += 30;
    printf("timegm %lld\n", (long long)timegm(&parts));
    printf("normalized %d-%02d-%02d %02d wday %d yday %d\n", parts.tm_year + 1900, parts.tm_mon + 1, parts.tm_mday,
        parts.tm_hour, parts.tm_wday, parts.tm_yday);

    // Formatted input from strings and streams.
    int a = 0, b = 0, n = 0;
    unsigned u = 0;
    long l = 0;
    double d = 0;
    float f = 0;
    char word[16] = "", rest[16] = "";
    int got = sscanf("  42 -17 0x1F word123 3.25 -1e-2 tail", "%d %i %x %15s %lf %f%n %3[a-z]", &a, &b, &u, word, &d, &f,
        &n, rest);
    printf("sscanf %d: %d %d %u %s %g %g %d %s\n", got, a, b, u, word, d, (double)f, n, rest);
    printf("sscanf literal %d, %d, eof %d\n", sscanf("x=5,y=9", "x=%d,y=%d", &a, &b), a + b, sscanf("", "%d", &a));
    printf("sscanf partial %d %d\n", sscanf("12 abc", "%d %d", &a, &b), a);
    printf("sscanf %%c %%*d %%ld %d\n", sscanf("Q 99 1234567890123", "%c %*d %ld", rest, &l) + (l == 1234567890123L));
    FILE* input = fopen("data/input.txt", "r");
    char name[16];
    while (fscanf(input, "%15s %d %lf", name, &a, &d) == 3)
        printf("fscanf %s %d %g\n", name, a, d);
    fclose(input);
    return 0;
}
