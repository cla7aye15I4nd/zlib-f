/* C side of the differential test for inffast.c: links the REAL zlib (patched copy).
 * Line:  inflate_fast <tab> <wsize> <whave> <wnext> <hold> <bits> <avail_out> <window> <prior> <input>
 *   tab     fixed | dyn:<lit lens>:<dist lens>   (hex digit per symbol; the tables are built as inflate() does:
 *           lencode = codes, inflate_table(LENS, ..., 9), distcode = next, inflate_table(DISTS, ..., 6))
 *   window  hex of wsize bytes, or - (wsize 0: window is NULL)
 *   prior   hex of the bytes already written before next_out in the same buffer, or -
 *   input   hex, at least 6 bytes
 * state->mode = LEN, state->sane = 1 (the only value inflate() ever sets in this configuration).
 * Output: mode, msg (or -), next_in offset, avail_in, next_out offset, avail_out, hold, bits, the whole output
 * buffer in hex (prior bytes, new bytes, untouched marker 0xa5). TABFAIL if inflate_table rejects the lengths. */
#define _LARGEFILE64_SOURCE 1
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <errno.h>
#include "zutil.h"
#include "inftrees.h"
#include "inflate.h"
#include "inffast.h"

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
/* hex or "-": returns malloc'ed bytes (never NULL) and the length */
static unsigned char *parse_hex(const char *s, size_t *len) {
    if (strcmp(s, "-") == 0) s = "";
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
        char *save, *tok[16]; int nt = 0;
        for (char *t = strtok_r(line, " \t\r\n", &save); t && nt < 16; t = strtok_r(NULL, " \t\r\n", &save))
            tok[nt++] = t;
        if (nt == 0) continue;
        if (strcmp(tok[0], "inflate_fast") != 0 || nt != 11) {
            fprintf(stderr, "unknown function or wrong arity: %s\n", tok[0]);
            printf("BADINPUT\n"); bad = 1; continue;
        }
        const char *tab = tok[1];
        unsigned wsize = (unsigned)parse_u(tok[2]), whave = (unsigned)parse_u(tok[3]), wnext = (unsigned)parse_u(tok[4]);
        unsigned long hold = (unsigned long)parse_u(tok[5]);
        unsigned bits = (unsigned)parse_u(tok[6]), avail_out = (unsigned)parse_u(tok[7]);
        size_t wl, pl, il;
        unsigned char *wbytes = parse_hex(tok[8], &wl), *prior = parse_hex(tok[9], &pl), *input = parse_hex(tok[10], &il);
        if (wl != wsize) { fprintf(stderr, "window length\n"); exit(2); }

        struct inflate_state *st = malloc(sizeof(struct inflate_state));
        memset(st, 0, sizeof(*st));
        z_stream strm;
        memset(&strm, 0, sizeof(strm));
        strm.state = (struct internal_state *)st;
        st->strm = &strm;
        st->mode = LEN;
        st->wsize = wsize; st->whave = whave; st->wnext = wnext;
        st->window = wsize ? wbytes : NULL;
        st->hold = hold; st->bits = bits;
        st->sane = 1;
        int tabfail = 0;
        if (strcmp(tab, "fixed") == 0) {
            inflate_fixed(st);
        } else if (strncmp(tab, "dyn:", 4) == 0) {
            char *lit = strdup(tab + 4);
            char *dist = strchr(lit, ':');
            if (!dist) { fprintf(stderr, "bad tab\n"); exit(2); }
            *dist++ = 0;
            st->nlen = (unsigned)strlen(lit); st->ndist = (unsigned)strlen(dist);
            for (unsigned i = 0; i < st->nlen; i++) st->lens[i] = (unsigned short)hexval(lit[i]);
            for (unsigned i = 0; i < st->ndist; i++) st->lens[st->nlen + i] = (unsigned short)hexval(dist[i]);
            st->next = st->codes;
            st->lencode = (const code *)(st->next);
            st->lenbits = 9;
            int ret = inflate_table(LENS, st->lens, st->nlen, &(st->next), &(st->lenbits), st->work);
            if (ret) tabfail = 1;
            else {
                st->distcode = (const code *)(st->next);
                st->distbits = 6;
                ret = inflate_table(DISTS, st->lens + st->nlen, st->ndist, &(st->next), &(st->distbits), st->work);
                if (ret) tabfail = 1;
            }
            free(lit);
        } else { fprintf(stderr, "bad tab\n"); exit(2); }
        if (tabfail) printf("TABFAIL\n");
        else {
            unsigned char *outbuf = malloc(pl + avail_out);
            memcpy(outbuf, prior, pl);
            memset(outbuf + pl, 0xa5, avail_out);
            strm.next_in = input; strm.avail_in = (uInt)il;
            strm.next_out = outbuf + pl; strm.avail_out = avail_out;
            inflate_fast(&strm, (unsigned)(pl + avail_out));
            printf("%u %s %ld %u %ld %u %lu %u ", (unsigned)st->mode, strm.msg ? strm.msg : "-",
                   (long)(strm.next_in - input), strm.avail_in, (long)(strm.next_out - outbuf), strm.avail_out,
                   st->hold, st->bits);
            for (size_t i = 0; i < pl + avail_out; i++) printf("%02x", outbuf[i]);
            printf("\n");
            free(outbuf);
        }
        free(st); free(wbytes); free(prior); free(input);
    }
    free(line);
    return bad;
}
