/* C side of the differential test for zutil.c: links the REAL zlib (patched copy).
 * Lines: zlibVersion | zlibCompileFlags | zError <int> | zcalloc_free <items> <size>
 * zcalloc_free allocates items*size bytes (unsigned product), fills them with a pattern, sums them, frees. */
#define _LARGEFILE64_SOURCE 1
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <errno.h>
#include "zutil.h"

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
        } else {
            fprintf(stderr, "unknown function or wrong arity: %s\n", fn);
            printf("BADINPUT\n");
            bad = 1;
        }
    }
    free(line);
    return bad;
}
