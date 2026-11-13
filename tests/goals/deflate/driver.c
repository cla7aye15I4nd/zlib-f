/* Statement test for the deflate goals: random sessions on the REAL libz.a (pinned zlib plus
 * patches). Each session is one actual history of the shape of DeflateDataTrace: init, preset
 * dictionaries, then deflate calls with random buffers and flushes. Every call is printed with the
 * state the goals talk about; check.py checks the clauses of Goal.deflate, Goal.deflate_sequence
 * and DeflateCompletes against these records, with its own decoder of the format specification.
 *
 * Usage: driver SEED COUNT [FOCUS]. Output lines (fields separated by one space):
 *   S level method wbits mem strategy rc          deflateInit2_ (a failed init ends the session)
 *   D rc hex                                      deflateSetDictionary
 *   B n bound bound_z                             deflateBound(strm, n) and deflateBound_z before data
 *   I hex                                         the whole input of the session
 *   C flush nullin nullout ain aout status pending bi_valid last_flush wrap lookahead strstart
 *     total_in total_out adler data_type msg
 *     -> rc ain' aout' status' pending' bi_valid' wrap' adler' data_type' msg' total_in' total_out' outhex
 *   E rc                                          deflateEnd
 * All randomness comes from SEED; no clock. Undefined behaviour of the C is never generated. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <zlib.h>
#include "deflate.h"

static uint64_t rs;
static int focus;   /* 1: the tight cases of deflateBound (small memLevel, incompressible data, FINISH only) */
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static unsigned rn(unsigned n) { return n ? (unsigned)(rnd() % n) : 0; }

static const char *WORDS[] = {"the ", "quick ", "brown ", "fox ", "zlib ", "deflate ", "window ", "huffman "};

static void data(unsigned char *b, size_t n, unsigned kind) {
    size_t i = 0;
    switch (kind % 7) {
    case 0: for (; i < n; i++) b[i] = (unsigned char)rnd(); break;
    case 1: memset(b, 0, n); break;
    case 2: while (i < n) { const char *w = WORDS[rn(8)]; for (size_t k = 0; w[k] && i < n; k++) b[i++] = (unsigned char)w[k]; } break;
    case 3: { unsigned char p[7]; for (int k = 0; k < 7; k++) p[k] = (unsigned char)rnd(); for (; i < n; i++) b[i] = p[i % 7]; } break;
    case 4: for (; i < n; i++) b[i] = (unsigned char)i; break;
    case 5: while (i < n) { unsigned char c = (unsigned char)rn(4); unsigned r = 1 + rn(300); for (unsigned k = 0; k < r && i < n; k++) b[i++] = c; } break;
    default:
        while (i < n) {
            if (rn(2)) { const char *w = WORDS[rn(8)]; for (size_t k = 0; w[k] && i < n; k++) b[i++] = (unsigned char)w[k]; }
            else { unsigned r = 1 + rn(12); for (unsigned k = 0; k < r && i < n; k++) b[i++] = (unsigned char)rnd(); }
        }
    }
}

static void hexout(const unsigned char *b, size_t n) {
    if (n == 0) { putchar('-'); return; }
    for (size_t i = 0; i < n; i++) printf("%02x", b[i]);
}

/* The two messages deflate can set: ERR_MSG(Z_STREAM_ERROR) and ERR_MSG(Z_BUF_ERROR). */
static const char *msgname(const char *m) {
    if (m == NULL) return "-";
    if (!strcmp(m, "stream error")) return "stream";
    if (!strcmp(m, "buffer error")) return "buffer";
    return "other";
}

static size_t pick_len(void) {
    switch (rn(6)) {
    case 0: return rn(40);
    case 1: return rn(600);
    case 2: return rn(5000);
    case 3: return 30000 + rn(40000);
    case 4: return rn(140000);
    default: return rn(3000);
    }
}

static const int FLUSHES[] = {Z_NO_FLUSH, Z_NO_FLUSH, Z_NO_FLUSH, Z_PARTIAL_FLUSH, Z_SYNC_FLUSH, Z_SYNC_FLUSH,
                              Z_FULL_FLUSH, Z_FULL_FLUSH, Z_BLOCK, Z_TREES};

static unsigned out_chunk(unsigned mode) {
    switch (mode) {
    case 0: return 1 + rn(3);
    case 1: return 1 + rn(20);
    case 2: return 1 + rn(400);
    case 3: return 1 + rn(70000);
    default: return rn(10) == 0 ? 0 : 1 + rn(5000);
    }
}

static void session(void) {
    z_stream *strm = calloc(1, sizeof *strm);
    int level = (int)rn(11) - 1, method = 8, mem = 1 + (int)rn(9), strategy = (int)rn(5);
    int wb = 8 + (int)rn(8);
    switch (rn(4)) { case 0: wb = -wb; break; case 1: wb += 16; break; default: break; }
    if (rn(40) == 0) wb = -8;                 /* refused */
    if (rn(60) == 0) mem = (int)rn(2) * 10;   /* refused */
    if (focus) { mem = 1 + (int)rn(3); if (rn(4) == 0) { mem = 8; wb = rn(2) ? 15 : -15; } if (rn(3) == 0) strategy = 4; }
    int rc = deflateInit2(strm, level, method, wb, mem, strategy);
    printf("S %d %d %d %d %d %d\n", level, method, wb, mem, strategy, rc);
    if (rc != Z_OK) { free(strm); return; }
    deflate_state *s = (deflate_state *)strm->state;
    size_t wsize = s->w_size;

    if (rn(3) == 0) {
        unsigned k = 1 + rn(3);
        for (unsigned j = 0; j < k; j++) {
            size_t dl;
            switch (rn(4)) { case 0: dl = 0; break; case 1: dl = rn(300); break; case 2: dl = wsize - 5 + rn(10); break; default: dl = rn(3 * wsize); }
            unsigned char *d = malloc(dl + 1);
            data(d, dl, rn(7));
            rc = deflateSetDictionary(strm, d, (uInt)dl);
            printf("D %d ", rc); hexout(d, dl); printf("\n");
            free(d);
        }
    }

    size_t n = pick_len();
    unsigned char *in = malloc(n + 1);
    data(in, n, focus ? (rn(2) ? 0 : 6) : rn(7));
    printf("B %zu %lu %zu\n", n, deflateBound(strm, (uLong)n), deflateBound_z(strm, n));
    printf("I "); hexout(in, n); printf("\n");

    unsigned mode = rn(4);             /* 0, 1: FINISH only; 2: mixed flushes; 3: one-shot */
    if (focus && mode == 2) mode = 3;
    unsigned omode = rn(5);
    size_t bound = deflateBound(strm, (uLong)n);
    size_t cap = 2 * bound + 4096;
    unsigned char *out = malloc(cap);
    size_t fed = 0, produced = 0, taken = 0;   /* offered, written, consumed */
    int done = 0, extra = 0;
    for (unsigned calls = 0; calls < 400000 && extra < 3; calls++) {
        int flush;
        size_t ain_target = fed;
        if (mode == 3) { ain_target = n; flush = Z_FINISH; }
        else if (mode < 2) { ain_target = fed + (mode == 0 ? n : rn(20000)); flush = Z_FINISH; }
        else {
            ain_target = fed + (rn(4) == 0 ? 0 : rn(9000));
            flush = FLUSHES[rn(10)];
            if (ain_target >= n && rn(2)) flush = Z_FINISH;
        }
        if (ain_target > n) ain_target = n;
        /* after the first FINISH the caller mostly stops offering input (zlib.h protocol) */
        if (s->status == FINISH_STATE && rn(8) != 0) fed = ain_target = taken;
        else if (ain_target < fed) ain_target = fed;
        unsigned aout = (mode == 3) ? (unsigned)(cap - produced) : out_chunk(omode);
        if (mode != 3 && rn(30) == 0) aout = (unsigned)(cap - produced < 70000 ? cap - produced : 70000);
        if (aout > cap - produced) aout = (unsigned)(cap - produced);
        int nullin = 0, nullout = 0;
        if (mode == 2 && rn(80) == 0) flush = rn(2) ? -1 : 6;
        if (mode == 2 && rn(80) == 0) nullout = 1;
        if (mode == 2 && rn(80) == 0) nullin = 1;
        if (done) { flush = rn(3) ? Z_FINISH : Z_NO_FLUSH; extra++; }
        fed = ain_target;
        printf("C %d %d %d", flush, nullin, nullout);
        strm->next_in = nullin ? Z_NULL : in + taken;
        strm->avail_in = nullin ? 5 : (uInt)(fed - taken);
        strm->next_out = nullout ? Z_NULL : out + produced;
        strm->avail_out = aout;
        printf(" %u %u %d %lu %d %d %d %u %u %lu %lu %lu %d %s", strm->avail_in, strm->avail_out, s->status,
               (unsigned long)s->pending, s->bi_valid, s->last_flush, s->wrap, s->lookahead, s->strstart,
               strm->total_in, strm->total_out, strm->adler, strm->data_type, msgname(strm->msg));
        uInt ain0 = strm->avail_in, aout0 = strm->avail_out;
        rc = deflate(strm, flush);
        size_t wrote = aout0 - strm->avail_out;
        printf(" -> %d %u %u %d %lu %d %d %lu %d %s %lu %lu ", rc, strm->avail_in, strm->avail_out, s->status,
               (unsigned long)s->pending, s->bi_valid, s->wrap, strm->adler, strm->data_type,
               msgname(strm->msg),
               strm->total_in, strm->total_out);
        hexout(out + produced, nullout ? 0 : wrote);
        printf("\n");
        if (!nullin) taken += ain0 - strm->avail_in;
        produced += nullout ? 0 : wrote;
        if (rc == Z_STREAM_END) done = 1;
        if (produced >= cap) break;
    }
    rc = deflateEnd(strm);
    printf("E %d\n", rc);
    free(in); free(out); free(strm);
}

int main(int argc, char **argv) {
    if (argc != 3 && argc != 4) { fprintf(stderr, "usage: driver SEED COUNT [FOCUS]\n"); return 2; }
    focus = argc == 4 && atoi(argv[3]);
    rs = strtoull(argv[1], NULL, 10) * 2654435761u + 88172645463325252ull;
    long count = strtol(argv[2], NULL, 10);
    for (long i = 0; i < count; i++) session();
    return 0;
}
