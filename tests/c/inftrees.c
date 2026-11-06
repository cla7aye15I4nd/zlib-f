/* C side of the differential test for inftrees.c: links the REAL zlib (patched copy).
 * Lines:
 *   inflate_table <type> <bits> <loff> <toff> <lens>   lens: one hex digit per symbol ("-" for none)
 *   inflate_fixed
 * inflate_table builds into codes[1444] (pre-filled with the marker {0xAA,0xBB,0xCCCC}) starting at codes+toff,
 * reading the lengths at lens+loff of a 320-entry array, with the work area work[288] (marker 0xABCD).
 * Output: return value, bits, table advance, FNV-1a of all 1444 entries, FNV-1a of the work area. */
#define _LARGEFILE64_SOURCE 1
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <errno.h>
#include "zutil.h"
#include "inftrees.h"
#include "inflate.h"

static unsigned long long fnv(unsigned long long h, unsigned b) {
    return (h ^ (b & 0xff)) * 1099511628211ULL;
}
static unsigned long long hash_codes(const code *c, int n) {
    unsigned long long h = 14695981039346656037ULL;
    for (int i = 0; i < n; i++) {
        h = fnv(h, c[i].op); h = fnv(h, c[i].bits); h = fnv(h, c[i].val & 0xff); h = fnv(h, c[i].val >> 8);
    }
    return h;
}
static unsigned long long parse_u(const char *s) {
    char *e; errno = 0;
    unsigned long long v = strtoull(s, &e, 10);
    if (*s == '\0' || *e != '\0' || errno || *s == '-') { fprintf(stderr, "bad unsigned %s\n", s); exit(2); }
    return v;
}
static int hexval(int c) {
    if (c >= '0' && c <= '9') return c - '0';
    if (c >= 'a' && c <= 'f') return c - 'a' + 10;
    return -1;
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
        if (strcmp(fn, "inflate_table") == 0 && nt == 6) {
            codetype type = (codetype)parse_u(tok[1]);
            unsigned bits = (unsigned)parse_u(tok[2]);
            unsigned loff = (unsigned)parse_u(tok[3]), toff = (unsigned)parse_u(tok[4]);
            const char *ls = strcmp(tok[5], "-") == 0 ? "" : tok[5];
            unsigned codes = (unsigned)strlen(ls);
            unsigned short *lensbuf = calloc(320, sizeof(unsigned short));
            unsigned short *work = malloc(288 * sizeof(unsigned short));
            code *tab = malloc(1444 * sizeof(code));
            if (loff + codes > 320 || toff > 1444) { fprintf(stderr, "out of range\n"); exit(2); }
            for (unsigned i = 0; i < codes; i++) {
                int v = hexval(ls[i]);
                if (v < 0) { fprintf(stderr, "bad digit\n"); exit(2); }
                lensbuf[loff + i] = (unsigned short)v;
            }
            for (int i = 0; i < 288; i++) work[i] = 0xABCD;
            for (int i = 0; i < 1444; i++) { tab[i].op = 0xAA; tab[i].bits = 0xBB; tab[i].val = 0xCCCC; }
            code *next = tab + toff;
            int ret = inflate_table(type, lensbuf + loff, codes, &next, &bits, work);
            unsigned long long hw = 14695981039346656037ULL;
            for (int i = 0; i < 288; i++) { hw = fnv(hw, work[i] & 0xff); hw = fnv(hw, work[i] >> 8); }
            printf("%d %u %ld %llu %llu\n", ret, bits, (long)(next - (tab + toff)), hash_codes(tab, 1444), hw);
            free(lensbuf); free(work); free(tab);
        } else if (strcmp(fn, "inflate_fixed") == 0 && nt == 1) {
            struct inflate_state *st = malloc(sizeof(struct inflate_state));
            memset(st, 0, sizeof(*st));
            inflate_fixed(st);
            printf("%llu %u %llu %u\n", hash_codes(st->lencode, 512), st->lenbits,
                   hash_codes(st->distcode, 32), st->distbits);
            free(st);
        } else {
            fprintf(stderr, "unknown function or wrong arity: %s\n", fn);
            printf("BADINPUT\n");
            bad = 1;
        }
    }
    free(line);
    return bad;
}
