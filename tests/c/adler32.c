/* C side of the differential test for adler32.c: links the REAL zlib (patched copy).
 * Input and output formats: see tests/README.md and tests/lean/DiffTest/Common.lean. */
#define _LARGEFILE64_SOURCE 1
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <errno.h>
#include "zlib.h"

static unsigned long long parse_u(const char *s) {
    char *e; errno = 0;
    unsigned long long v = strtoull(s, &e, 10);
    if (*s == '\0' || *e != '\0' || errno || *s == '-') { fprintf(stderr, "bad unsigned %s\n", s); exit(2); }
    return v;
}
static long long parse_i(const char *s) {
    char *e; errno = 0;
    long long v = strtoll(s, &e, 10);
    if (*s == '\0' || *e != '\0' || errno) { fprintf(stderr, "bad signed %s\n", s); exit(2); }
    return v;
}
static int hexval(int c) {
    if (c >= '0' && c <= '9') return c - '0';
    if (c >= 'a' && c <= 'f') return c - 'a' + 10;
    if (c >= 'A' && c <= 'F') return c - 'A' + 10;
    return -1;
}
/* Buffer argument: null:<len> or hex:<digits>. The bytes are malloc'ed with the exact size
 * (at least one byte, so that the pointer of an empty buffer is not NULL), so a sanitizer
 * sees any read past the end. */
static unsigned char *parse_buf(const char *s, size_t *len) {
    if (strncmp(s, "null:", 5) == 0) { *len = (size_t)parse_u(s + 5); return NULL; }
    if (strncmp(s, "hex:", 4) != 0) { fprintf(stderr, "bad buffer\n"); exit(2); }
    s += 4;
    size_t n = strlen(s);
    if (n % 2) { fprintf(stderr, "odd hex\n"); exit(2); }
    *len = n / 2;
    unsigned char *b = malloc(*len ? *len : 1);
    for (size_t i = 0; i < *len; i++) {
        int h = hexval(s[2 * i]), l = hexval(s[2 * i + 1]);
        if (h < 0 || l < 0) { fprintf(stderr, "bad hex digit\n"); exit(2); }
        b[i] = (unsigned char)(h * 16 + l);
    }
    return b;
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
        if ((strcmp(fn, "adler32_z") == 0 || strcmp(fn, "adler32") == 0) && nt == 3) {
            uLong a = (uLong)parse_u(tok[1]);
            size_t len; unsigned char *b = parse_buf(tok[2], &len);
            uLong r;
            if (strcmp(fn, "adler32_z") == 0) r = adler32_z(a, b, (z_size_t)len);
            else {
                if (len > 0xffffffffUL) { fprintf(stderr, "len does not fit uInt\n"); exit(2); }
                r = adler32(a, b, (uInt)len);
            }
            printf("%lu\n", r);
            free(b);
        } else if ((strcmp(fn, "adler32_combine") == 0 || strcmp(fn, "adler32_combine64") == 0) && nt == 4) {
            uLong a1 = (uLong)parse_u(tok[1]), a2 = (uLong)parse_u(tok[2]);
            long long l = parse_i(tok[3]);
            uLong r = strcmp(fn, "adler32_combine") == 0 ? adler32_combine(a1, a2, (z_off_t)l)
                                                         : adler32_combine64(a1, a2, (z_off64_t)l);
            printf("%lu\n", r);
        } else {
            fprintf(stderr, "unknown function or wrong arity: %s\n", fn);
            printf("BADINPUT\n");
            bad = 1;
        }
    }
    free(line);
    return bad;
}
