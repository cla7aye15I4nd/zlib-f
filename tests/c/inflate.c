/* C side of the differential test for inflate.c (the whole inflate API): links the REAL zlib (patched copy).
 * Input and output formats: tests/README.md section "inflate". One case per line:
 *   inflate WB INCH OUTCH FLUSH OPTS hex:DICT hex:INPUT
 * WB    windowBits for inflateInit2 (signed)         INCH  input chunk size (0 = the whole input at once)
 * OUTCH output chunk size (>= 1)                     FLUSH the flush argument of every inflate() call
 * OPTS  bit 1: inflateGetHeader before the first call (buffers of 64 bytes for extra, name, comment)
 *       bit 2: inflateCopy after the second call, continue on the copy, inflateEnd the source
 *       bit 4: inflateGetDictionary at the end (32768-byte buffer)
 *       bit 8: inflatePrime(3, 5) before the first call
 *       bit 16: inflateSetDictionary before the first call (raw streams: the dictionary of a raw deflate stream)
 *       bit 32: inflateValidate(0) before the first call
 *       bit 64: after a data error, inflateSync on the unread rest of the current input chunk
 * DICT  the dictionary given to inflateSetDictionary when inflate() returns Z_NEED_DICT (empty = none)
 * The driver calls inflate() in a loop: a fresh input chunk when avail_in is 0, a fresh output buffer of OUTCH bytes on
 * every call. It stops at Z_STREAM_END, at an error other than Z_BUF_ERROR, at Z_BUF_ERROR with no input left, or
 * after 20000 calls. The output line holds every result and counter that can be observed. */
#define _LARGEFILE64_SOURCE 1
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <errno.h>
#include "zutil.h"
#include "inftrees.h"
#include "inflate.h"

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
static unsigned char *parse_hex(const char *s, size_t *len) {
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

/* a growing string */
typedef struct { char *p; size_t n, cap; } sb;
static void sb_add(sb *s, const char *t) {
    size_t k = strlen(t);
    if (s->n + k + 1 > s->cap) { s->cap = (s->n + k + 1) * 2; s->p = realloc(s->p, s->cap); }
    memcpy(s->p + s->n, t, k + 1); s->n += k;
}
static void sb_hex(sb *s, const unsigned char *b, size_t n) {
    char t[3];
    for (size_t i = 0; i < n; i++) { snprintf(t, sizeof t, "%02x", b[i]); sb_add(s, t); }
}
static void sb_fmt_i(sb *s, const char *fmt, long long v) { char t[64]; snprintf(t, sizeof t, fmt, v); sb_add(s, t); }

/* the NUL-terminated string at p (at most max bytes) as hex, "-" for NULL */
static void sb_cstr(sb *s, const unsigned char *p, size_t max) {
    if (p == NULL) { sb_add(s, "-"); return; }
    size_t k = 0;
    while (k < max && p[k] != 0) k++;
    if (k == 0) sb_add(s, "~"); else sb_hex(s, p, k);
}

static void run_case(char **tok) {
    int wb = (int)parse_i(tok[1]);
    size_t inch = (size_t)parse_u(tok[2]), outch = (size_t)parse_u(tok[3]);
    int flush = (int)parse_i(tok[4]);
    unsigned opts = (unsigned)parse_u(tok[5]);
    size_t dlen, ilen;
    unsigned char *dict = parse_hex(tok[6], &dlen);
    unsigned char *input = parse_hex(tok[7], &ilen);
    if (inch == 0) inch = ilen ? ilen : 1;
    sb out = {0}, line = {0}, tr = {0};
    z_stream s1; memset(&s1, 0, sizeof s1);
    z_stream s2; memset(&s2, 0, sizeof s2);
    z_streamp zs = &s1;
    int init = inflateInit2(&s1, wb);
    sb_fmt_i(&line, "init=%lld", init);
    unsigned char *extra = calloc(64, 1), *name = calloc(64, 1), *comm = calloc(64, 1);
    gz_header head; memset(&head, 0, sizeof head);
    head.extra = extra; head.extra_max = 64; head.name = name; head.name_max = 64; head.comment = comm; head.comm_max = 64;
    int hd = -99;
    unsigned char *dbuf = NULL;
    int final = 0;
    size_t pos = 0, calls = 0;
    int copied = 0;
    int faulted = 0;
    unsigned char *chunk = NULL;
    if (init == Z_OK) {
        if (opts & 32) sb_fmt_i(&line, " val=%lld", inflateValidate(zs, 0));
        if (opts & 8) sb_fmt_i(&line, " prime=%lld", inflatePrime(zs, 3, 5));
        if (opts & 1) hd = inflateGetHeader(zs, &head);
        if ((opts & 16) && dlen) sb_fmt_i(&line, " sd0=%lld", inflateSetDictionary(zs, dict, (uInt)dlen));
        for (;;) {
            if (zs->avail_in == 0 && pos < ilen) {
                size_t n = ilen - pos < inch ? ilen - pos : inch;
                free(chunk);
                chunk = malloc(n);
                memcpy(chunk, input + pos, n);
                zs->next_in = chunk; zs->avail_in = (uInt)n; pos += n;
            }
            unsigned char *ob = malloc(outch);
            zs->next_out = ob; zs->avail_out = (uInt)outch;
            int ret = inflate(zs, flush);
            size_t produced = outch - zs->avail_out;
            sb_add(&out, ""); sb_hex(&out, ob, produced);
            free(ob);
            calls++;
            if (calls <= 24) {
                char t[64]; snprintf(t, sizeof t, "%d:%u:%zu;", ret, zs->avail_in, produced); sb_add(&tr, t);
            }
            final = ret;
            if (ret == Z_NEED_DICT) {
                if (dlen) {
                    int r2 = inflateSetDictionary(zs, dict, (uInt)dlen);
                    if (calls <= 24) { char t[32]; snprintf(t, sizeof t, "d%d;", r2); sb_add(&tr, t); }
                    if (r2 != Z_OK) break;
                    continue;
                }
                break;
            }
            if (ret == Z_STREAM_END) break;
            if (ret < 0 && ret != Z_BUF_ERROR) break;
            if (ret == Z_BUF_ERROR && zs->avail_in == 0 && pos >= ilen) break;
            if ((opts & 2) && calls == 2 && !copied) {
                copied = 1;
                struct inflate_state *st = (struct inflate_state *)zs->state;
                /* the source compares state->lencode with state->codes (inflate.c L1383): undefined behaviour unless
                   lencode points into codes. The Lean translation faults there; report the same. */
                if (st->lencode != st->codes) { faulted = 1; break; }
                int rc = inflateCopy(&s2, zs);
                sb_fmt_i(&tr, "c%lld;", rc);
                inflateEnd(zs);
                zs = &s2;
            }
            if (calls >= 20000) break;
        }
        if (faulted) {
            printf("FAULT ub comparison of pointers into different objects\n");
            inflateEnd(zs);
            goto done;
        }
        if ((opts & 64) && final == Z_DATA_ERROR) {
            int r3 = inflateSync(zs);
            sb_fmt_i(&tr, "sync%lld;", r3);
            sb_fmt_i(&tr, "sin%lld;", (long long)zs->avail_in);
            sb_fmt_i(&tr, "mode%lld;", (long long)inflateSyncPoint(zs));
        }
        sb_fmt_i(&line, " rc=%lld", final);
        sb_fmt_i(&line, " calls=%lld", (long long)calls);
        sb_fmt_i(&line, " tin=%lld", (long long)zs->total_in);
        sb_fmt_i(&line, " tout=%lld", (long long)zs->total_out);
        sb_fmt_i(&line, " adler=%lld", (long long)zs->adler);
        sb_fmt_i(&line, " dt=%lld", (long long)zs->data_type);
        sb_add(&line, " msg="); sb_cstr(&line, (const unsigned char *)zs->msg, 64);
        sb_fmt_i(&line, " mark=%lld", (long long)inflateMark(zs));
        sb_fmt_i(&line, " sp=%lld", (long long)inflateSyncPoint(zs));
        sb_fmt_i(&line, " cu=%lld", (long long)inflateCodesUsed(zs));
        if (opts & 1) {
            sb_fmt_i(&line, " hd=%lld", hd);
            sb_fmt_i(&line, " h=%lld", head.done); sb_fmt_i(&line, ",%lld", head.text);
            sb_fmt_i(&line, ",%lld", (long long)head.time); sb_fmt_i(&line, ",%lld", head.xflags);
            sb_fmt_i(&line, ",%lld", head.os); sb_fmt_i(&line, ",%lld", head.hcrc);
            sb_fmt_i(&line, ",%lld,", (long long)head.extra_len);
            sb_hex(&line, extra, head.extra_len < 64 ? head.extra_len : 64);
            sb_add(&line, ","); sb_cstr(&line, name, 64);
            sb_add(&line, ","); sb_cstr(&line, comm, 64);
            sb_add(&line, head.extra == NULL ? ",xn" : ",xp");
            sb_add(&line, head.name == NULL ? "n" : "p");
            sb_add(&line, head.comment == NULL ? "n" : "p");
        }
        if (opts & 4) {
            dbuf = calloc(32768, 1);
            uInt dl = 12345;
            int gd = inflateGetDictionary(zs, dbuf, &dl);
            sb_fmt_i(&line, " gd=%lld", gd); sb_fmt_i(&line, ":%lld:", (long long)dl);
            sb_hex(&line, dbuf, dl <= 32768 ? dl : 0);
        }
        sb_add(&line, " tr="); sb_add(&line, tr.p ? tr.p : "");
        sb_add(&line, " out="); sb_add(&line, out.p ? out.p : "");
        printf("%s\n", line.p);
        inflateEnd(zs);
    } else {
        printf("%s\n", line.p);
    }
done:
    free(chunk); free(extra); free(name); free(comm); free(dbuf); free(dict); free(input);
    free(out.p); free(line.p); free(tr.p);
}

int main(void) {
    char *line = NULL; size_t cap = 0; ssize_t got;
    int bad = 0;
    while ((got = getline(&line, &cap, stdin)) >= 0) {
        char *save, *tok[16]; int nt = 0;
        for (char *t = strtok_r(line, " \t\r\n", &save); t && nt < 16; t = strtok_r(NULL, " \t\r\n", &save))
            tok[nt++] = t;
        if (nt == 0) continue;
        if (strcmp(tok[0], "inflate") == 0 && nt == 8) {
            run_case(tok);
        } else {
            fprintf(stderr, "unknown function or wrong arity: %s\n", tok[0]);
            printf("BADINPUT\n");
            bad = 1;
        }
    }
    free(line);
    return bad;
}
