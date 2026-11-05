/* C side of the differential test for crc32.c: links the REAL zlib (patched copy).
 * Input and output formats: see tests/README.md and tests/lean/Driver/Crc32.lean.
 * Buffer: null:<len> | hex:<digits> | off:<k>:<digits> (the bytes start k bytes into a malloc'ed block,
 * so the pointer alignment is k mod 8). */
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
/* Returns the pointer to give to crc32 and sets *base to the block to free. */
static unsigned char *parse_buf(const char *s, size_t *len, unsigned char **base) {
    size_t off = 0;
    *base = NULL;
    if (strncmp(s, "null:", 5) == 0) { *len = (size_t)parse_u(s + 5); return NULL; }
    if (strncmp(s, "off:", 4) == 0) {
        s += 4;
        char *e; off = strtoul(s, &e, 10);
        if (*e != ':') { fprintf(stderr, "bad off\n"); exit(2); }
        s = e + 1;
    } else if (strncmp(s, "hex:", 4) == 0) s += 4;
    else { fprintf(stderr, "bad buffer\n"); exit(2); }
    size_t n = strlen(s);
    if (n % 2) { fprintf(stderr, "odd hex\n"); exit(2); }
    *len = n / 2;
    unsigned char *b = malloc(off + *len ? off + *len : 1);
    *base = b;
    for (size_t i = 0; i < off; i++) b[i] = 0;
    for (size_t i = 0; i < *len; i++) {
        int h = hexval(s[2 * i]), l = hexval(s[2 * i + 1]);
        if (h < 0 || l < 0) { fprintf(stderr, "bad hex digit\n"); exit(2); }
        b[off + i] = (unsigned char)(h * 16 + l);
    }
    return b + off;
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
        if ((strcmp(fn, "crc32_z") == 0 || strcmp(fn, "crc32") == 0) && nt == 3) {
            uLong a = (uLong)parse_u(tok[1]);
            size_t len; unsigned char *base; unsigned char *b = parse_buf(tok[2], &len, &base);
            uLong r;
            if (strcmp(fn, "crc32_z") == 0) r = crc32_z(a, b, (z_size_t)len);
            else {
                if (len > 0xffffffffUL) { fprintf(stderr, "len does not fit uInt\n"); exit(2); }
                r = crc32(a, b, (uInt)len);
            }
            printf("%lu\n", r);
            free(base);
        } else if ((strcmp(fn, "crc32_combine") == 0 || strcmp(fn, "crc32_combine64") == 0) && nt == 4) {
            uLong a1 = (uLong)parse_u(tok[1]), a2 = (uLong)parse_u(tok[2]);
            long long l = parse_i(tok[3]);
            uLong r = strcmp(fn, "crc32_combine") == 0 ? crc32_combine(a1, a2, (z_off_t)l)
                                                       : crc32_combine64(a1, a2, (z_off64_t)l);
            printf("%lu\n", r);
        } else if ((strcmp(fn, "crc32_combine_gen") == 0 || strcmp(fn, "crc32_combine_gen64") == 0) && nt == 2) {
            long long l = parse_i(tok[1]);
            uLong r = strcmp(fn, "crc32_combine_gen") == 0 ? crc32_combine_gen((z_off_t)l)
                                                           : crc32_combine_gen64((z_off64_t)l);
            printf("%lu\n", r);
        } else if (strcmp(fn, "crc32_combine_op") == 0 && nt == 4) {
            printf("%lu\n", crc32_combine_op((uLong)parse_u(tok[1]), (uLong)parse_u(tok[2]), (uLong)parse_u(tok[3])));
        } else if (strcmp(fn, "get_crc_table") == 0 && nt == 1) {
            const z_crc_t *t = get_crc_table();
            for (int i = 0; i < 256; i++) printf(i ? " %lu" : "%lu", (unsigned long)t[i]);
            printf("\n");
        } else {
            fprintf(stderr, "unknown function or wrong arity: %s\n", fn);
            printf("BADINPUT\n");
            bad = 1;
        }
    }
    free(line);
    return bad;
}
