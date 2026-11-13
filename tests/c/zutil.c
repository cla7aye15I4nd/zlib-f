/* C side of the differential test for zutil.c: links the REAL zlib (patched copy).
 * Lines: zlibVersion | zlibCompileFlags | zError <int> | zcalloc_free <items> <size> | malloc <n>
 * zcalloc_free allocates items*size bytes (unsigned product), fills them with a pattern, sums them, frees.
 * malloc calls the C library's malloc((size_t)n) and prints null or ok (and frees): the runtime model refuses a
 * request above PTRDIFF_MAX, as glibc does.
 * Under ASan (SAN=1) an oversized request aborts by default instead of returning NULL. The driver sets
 * allocator_may_return_null=1 through __asan_default_options, so the malloc rows run with the sanitiser as well; the
 * option affects only this driver, and an ASAN_OPTIONS variable in the environment still overrides it. */
#define _LARGEFILE64_SOURCE 1
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <errno.h>
#include "zutil.h"

#if defined(__SANITIZE_ADDRESS__)
#define DIFF_ASAN 1
#elif defined(__has_feature)
#if __has_feature(address_sanitizer)
#define DIFF_ASAN 1
#endif
#endif
#ifdef DIFF_ASAN
const char *__asan_default_options(void);
const char *__asan_default_options(void) { return "allocator_may_return_null=1"; }
#endif

/* The result of malloc goes through a volatile object, so that the compiler cannot drop the malloc/free pair and
 * assume success. */
static void *volatile malloc_result;

static unsigned long long parse_u(const char *s) {
    char *e; errno = 0;
    unsigned long long v = strtoull(s, &e, 10);
    if (*s == '\0' || *s == '-' || *e != '\0' || errno) { fprintf(stderr, "bad number %s\n", s); exit(2); }
    return v;
}

static long long parse_i(const char *s) {
    char *e; errno = 0;
    long long v = strtoll(s, &e, 10);
    if (*s == '\0' || *e != '\0' || errno) { fprintf(stderr, "bad number %s\n", s); exit(2); }
    return v;
}

int main(void) {
    char *line = NULL; size_t cap = 0; ssize_t got;
    int bad = 0;
    while ((got = getline(&line, &cap, stdin)) >= 0) {
        char *save, *tok[8]; int nt = 0;
        for (char *t = strtok_r(line, " \t\r\n", &save); t && nt < 8; t = strtok_r(NULL, " \t\r\n", &save))
            tok[nt++] = t;
        if (nt == 0) continue;
        const char *fn = tok[0];
        if (strcmp(fn, "zlibVersion") == 0 && nt == 1) {
            printf("[%s]\n", zlibVersion());
        } else if (strcmp(fn, "zlibCompileFlags") == 0 && nt == 1) {
            printf("%lu\n", zlibCompileFlags());
        } else if (strcmp(fn, "zError") == 0 && nt == 2) {
            printf("[%s]\n", zError((int)parse_i(tok[1])));
        } else if (strcmp(fn, "zcalloc_free") == 0 && nt == 3) {
            unsigned items = (unsigned)parse_i(tok[1]), size = (unsigned)parse_i(tok[2]);
            unsigned n = items * size;
            unsigned char *p = zcalloc(NULL, items, size);
            if (p == NULL) { printf("null\n"); continue; }
            unsigned long sum = 0;
            for (unsigned i = 0; i < n; i++) p[i] = (unsigned char)(i * 31 + 7);
            for (unsigned i = 0; i < n; i++) sum += p[i];
            zcfree(NULL, p);
            printf("%u %lu\n", n, sum);
        } else if (strcmp(fn, "malloc") == 0 && nt == 2) {
            size_t n = (size_t)parse_u(tok[1]);
            malloc_result = malloc(n);
            void *p = malloc_result;
            if (p == NULL) { printf("null\n"); continue; }
            free(p);
            printf("ok\n");
        } else {
            fprintf(stderr, "unknown function or wrong arity: %s\n", fn);
            printf("BADINPUT\n");
            bad = 1;
        }
    }
    free(line);
    return bad;
}
