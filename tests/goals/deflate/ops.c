/* Safety test of the deflate history domain: random sequences of every stream operation that
 * StreamReachable admits (ZlibF/Spec/Public/History.lean), on the real libz.a under ASan and
 * UBSan. The order rules are those of StreamArguments: deflatePrime and deflateSetHeader only
 * before the stream has started (DeflateNotStarted), and a gzip header that the caller keeps
 * at least as long as the part already written (DeflateHeaderProgress). Every other argument
 * is random, including deflateTune values, flushes, levels, strategies and buffer sizes.
 * A run passes when no sanitizer reports and every call returns.
 * Usage: ops SEED COUNT */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <zlib.h>
#include "deflate.h"

static uint64_t rs;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static unsigned rn(unsigned n) { return n ? (unsigned)(rnd() % n) : 0; }

static void fill(unsigned char *b, size_t n) {
    unsigned kind = rn(4);
    for (size_t i = 0; i < n; i++)
        b[i] = kind == 0 ? (unsigned char)rnd() : kind == 1 ? 0 : kind == 2 ? "abcab"[i % 5] : (unsigned char)(rn(3) + 'a');
}

static int not_started(z_stream *z) {
    deflate_state *s = (deflate_state *)z->state;
    return s->status == INIT_STATE || s->status == GZIP_STATE;
}

typedef struct { gz_header g; unsigned char *extra, *name, *comment; size_t nlen, clen; } hdr_t;

static void session(void) {
    z_stream *z = calloc(1, sizeof *z), *copy = NULL;
    int level = (int)rn(11) - 1, mem = rn(2) ? 1 + (int)rn(2) : 1 + (int)rn(9), strategy = (int)rn(5);
    int wb = 9 + (int)rn(7);
    switch (rn(3)) { case 0: wb = -wb; break; case 1: wb += 16; break; default: break; }
    if (deflateInit2(z, level, Z_DEFLATED, wb, mem, strategy) != Z_OK) { free(z); return; }
    size_t n = rn(3) ? rn(5000) : rn(200000);
    unsigned char *in = malloc(n + 1); fill(in, n);
    size_t ocap = 1 << 20; unsigned char *out = malloc(ocap);
    hdr_t H; memset(&H, 0, sizeof H);
    size_t taken = 0;
    for (int step = 0; step < 300; step++) {
        unsigned op = rn(100);
        deflate_state *s = (deflate_state *)z->state;
        if (op < 55) {                                   /* deflate */
            size_t give = rn(4) ? rn(3000) : rn(70000);
            if (taken + give > n) give = n - taken;
            z->next_in = in + taken; z->avail_in = (uInt)give;
            z->next_out = out; z->avail_out = rn(10) ? 1 + rn(rn(2) ? 64 : 20000) : 0;
            int flush = (int)rn(6);
            if (rn(4) == 0) flush = Z_FINISH;
            uInt a0 = z->avail_in;
            int rc = deflate(z, flush);
            taken += a0 - z->avail_in;
            if (rc == Z_STREAM_END && rn(3) == 0) { deflateReset(z); taken = 0; }
        } else if (op < 60) {                            /* deflateParams */
            z->next_in = in + taken; z->avail_in = 0;
            z->next_out = out; z->avail_out = 1 + rn(5000);
            deflateParams(z, (int)rn(11) - 1, (int)rn(5));
        } else if (op < 64) {                            /* deflateTune: any int, converted as in C */
            int v[4];
            for (int k = 0; k < 4; k++) v[k] = rn(4) == 0 ? (int)rnd() : (int)rn(300) - 10;
            deflateTune(z, v[0], v[1], v[2], v[3]);
        } else if (op < 68) {                            /* deflateSetDictionary */
            size_t dl = rn(4) ? rn(500) : rn(70000);
            unsigned char *d = malloc(dl + 1); fill(d, dl);
            deflateSetDictionary(z, d, (uInt)dl);
            free(d);
        } else if (op < 71) {                            /* deflateReset / deflateResetKeep */
            if (rn(2)) deflateReset(z); else deflateResetKeep(z);
            taken = 0;
        } else if (op < 75) {                            /* deflatePrime, only before the start */
            unsigned burst = rn(2) ? 1 : rn(300);
            for (unsigned k = 0; k < burst; k++)
                if (not_started(z)) deflatePrime(z, (int)rn(18) - 1, (int)rnd());
        } else if (op < 79) {                            /* deflateSetHeader, only before the start */
            if (not_started(z)) {
                free(H.extra); free(H.name); free(H.comment);
                memset(&H, 0, sizeof H);
                if (rn(2)) { size_t el = rn(2) ? rn(100) : rn(5000); H.extra = malloc(el + 1); fill(H.extra, el); H.g.extra = H.extra; H.g.extra_len = (uInt)el; }
                if (rn(2)) { H.nlen = rn(2) ? rn(50) : rn(3000); H.name = malloc(H.nlen + 1); memset(H.name, 'n', H.nlen); H.name[H.nlen] = 0; H.g.name = H.name; }
                if (rn(2)) { H.clen = rn(2) ? rn(50) : rn(3000); H.comment = malloc(H.clen + 1); memset(H.comment, 'c', H.clen); H.comment[H.clen] = 0; H.g.comment = H.comment; }
                H.g.hcrc = (int)rn(2); H.g.text = (int)rn(2); H.g.time = (uLong)rnd(); H.g.os = (int)rn(256);
                deflateSetHeader(z, rn(4) ? &H.g : Z_NULL);
            }
        } else if (op < 82) {                            /* caller edits of the header that keep progress */
            if (H.extra && s->gzhead == &H.g) {
                size_t lo = s->status == EXTRA_STATE ? s->gzindex : 0;
                if (H.g.extra_len > lo) H.g.extra_len = (uInt)(lo + rn((unsigned)(H.g.extra_len - lo + 1)));
            }
            if (rn(4) == 0 && s->status != NAME_STATE) H.g.name = Z_NULL;
        } else if (op < 86) {                            /* queries */
            unsigned p; int b; unsigned char dict[32768]; uInt dl;
            deflatePending(z, &p, &b); deflateBound(z, (uLong)rnd()); deflateBound_z(z, rn(100000));
            deflateGetDictionary(z, rn(2) ? dict : Z_NULL, &dl);
            unsigned long used; (void)used;
        } else if (op < 89) {                            /* deflateCopy, continue with the copy */
            copy = calloc(1, sizeof *copy);
            if (deflateCopy(copy, z) == Z_OK) { deflateEnd(z); free(z); z = copy; }
            else free(copy);
            copy = NULL;
        } else {                                         /* invalid calls refused cleanly */
            z->next_out = rn(2) ? Z_NULL : out; z->avail_out = rn(2) ? 0 : 10;
            z->next_in = Z_NULL; z->avail_in = rn(2) ? 0 : 3;
            deflate(z, (int)rn(9) - 1);
        }
    }
    deflateEnd(z); free(z);
    free(in); free(out); free(H.extra); free(H.name); free(H.comment);
}

int main(int argc, char **argv) {
    if (argc != 3) { fprintf(stderr, "usage: ops SEED COUNT\n"); return 2; }
    rs = strtoull(argv[1], NULL, 10) * 2654435761u + 88172645463325252ull;
    long count = strtol(argv[2], NULL, 10);
    for (long i = 0; i < count; i++) session();
    printf("sessions %ld\n", count);
    return 0;
}
