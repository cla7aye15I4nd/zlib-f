/* Adversarial-callback test of inflateBack (statement test for inflate_back_sequence_safety).
 * Links the real zlib (patched copy) built with sanitizers. For each case, from a seed:
 *   - an input stream: raw deflate of random data (any level, strategy, windowBits, flush pattern),
 *     optionally mutated (bit flips, truncation, garbage tail), or random bytes;
 *   - inflateBackInit_ with windowBits 8..15 and a window of exactly 1 << windowBits bytes;
 *   - one to three inflateBack calls on the same state, then inflateBackEnd.
 * The in call-back hands out pieces of random size, each in a fresh malloc'ed buffer of exactly that
 * size, freed at the next in call (the documented lifetime); it may stop early by returning 0.
 * The out call-back checks that it receives the window and at most 1 << windowBits bytes, reads every
 * byte, and fails at random. Sanitizers report any out-of-bounds access, use after free, undefined
 * behaviour or (Linux) leak; the library's own allocations are counted through zalloc/zfree. The program also checks the return codes the safety goal allows and, for an
 * unmodified stream decoded without a callback stop, with a window at least as large as the encoder's
 * (zlib.h's precondition; a smaller window may decode wrongly but stays memory-safe), that the output
 * equals the input. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "zlib.h"

static unsigned long long rng;
static long live_allocs;
static voidpf count_alloc(voidpf opaque, uInt items, uInt size) {
    (void)opaque; live_allocs++; return calloc(items, size);
}
static void count_free(voidpf opaque, voidpf p) { (void)opaque; if (p) live_allocs--; free(p); }
static unsigned long long next_rand(void) {
    rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; return rng;
}
static unsigned rnd(unsigned n) { return n ? (unsigned)(next_rand() % n) : 0; }

typedef struct {
    const unsigned char *src; size_t len, pos;
    unsigned char *piece; int stop_at; int calls; int policy;
} in_t;
typedef struct {
    unsigned char *window; unsigned wsize; int fail_policy; int calls;
    unsigned char *got; size_t glen, gcap; unsigned sum;
} out_t;

static unsigned in_cb(void *desc, z_const unsigned char **buf) {
    in_t *c = desc;
    free(c->piece); c->piece = NULL;
    c->calls++;
    if (c->stop_at >= 0 && c->calls > c->stop_at) return 0;
    if (c->pos >= c->len) return 0;
    size_t left = c->len - c->pos, n;
    switch (c->policy) {
    case 0: n = 1; break;
    case 1: n = 1 + rnd(7); break;
    case 2: n = 1 + rnd(4096); break;
    default: n = left; break;
    }
    if (n > left) n = left;
    c->piece = malloc(n);
    memcpy(c->piece, c->src + c->pos, n);
    c->pos += n;
    *buf = c->piece;
    return (unsigned)n;
}

static int out_cb(void *desc, unsigned char *buf, unsigned len) {
    out_t *o = desc;
    o->calls++;
    if (buf != o->window || len > o->wsize) { fprintf(stderr, "BAD out arguments\n"); abort(); }
    for (unsigned i = 0; i < len; i++) o->sum = o->sum * 31u + buf[i];
    if (o->glen + len > o->gcap) {
        o->gcap = (o->glen + len) * 2 + 1024;
        o->got = realloc(o->got, o->gcap);
    }
    memcpy(o->got + o->glen, buf, len);
    o->glen += len;
    switch (o->fail_policy) {
    case 1: return o->calls == 1;
    case 2: return rnd(8) == 0;
    case 3: return (int)(next_rand() | 1);   /* any nonzero value */
    default: return 0;
    }
}

static unsigned char *make_data(size_t *len) {
    size_t n = rnd(4) == 0 ? rnd(64) : rnd(200000);
    unsigned char *d = malloc(n ? n : 1);
    int kind = rnd(4);
    for (size_t i = 0; i < n; i++) {
        if (kind == 0) d[i] = (unsigned char)next_rand();
        else if (kind == 1) d[i] = (unsigned char)('a' + rnd(3));
        else if (kind == 2) d[i] = i >= 300 && rnd(4) ? d[i - 1 - rnd(300)] : (unsigned char)next_rand();
        else d[i] = (unsigned char)(i % 251);
    }
    *len = n;
    return d;
}

static unsigned char *compress_raw(const unsigned char *d, size_t n, int wbits, size_t *outlen) {
    z_stream s; memset(&s, 0, sizeof s);
    int level = (int)rnd(10), strategy = (int)rnd(5), mem = 1 + (int)rnd(9);
    if (deflateInit2(&s, level, Z_DEFLATED, -wbits, mem, strategy) != Z_OK) { fprintf(stderr, "deflateInit2\n"); abort(); }
    size_t cap = deflateBound(&s, n) + 1024 + n / 8;
    unsigned char *o = malloc(cap);
    s.next_out = o; s.avail_out = (uInt)cap;
    size_t pos = 0;
    while (pos < n) {
        size_t piece = 1 + rnd(65536); if (piece > n - pos) piece = n - pos;
        s.next_in = (z_const Bytef *)(d + pos); s.avail_in = (uInt)piece;
        int fl = rnd(10) == 0 ? (int)rnd(4) : Z_NO_FLUSH;     /* NO, PARTIAL, SYNC, FULL */
        if (deflate(&s, fl) == Z_STREAM_ERROR) { fprintf(stderr, "deflate\n"); abort(); }
        pos += piece - s.avail_in;
    }
    s.next_in = NULL; s.avail_in = 0;
    if (deflate(&s, Z_FINISH) != Z_STREAM_END) { fprintf(stderr, "deflate finish\n"); abort(); }
    *outlen = cap - s.avail_out;
    deflateEnd(&s);
    return o;
}

int main(int argc, char **argv) {
    unsigned long long first = argc > 1 ? strtoull(argv[1], NULL, 10) : 1;
    unsigned long long count = argc > 2 ? strtoull(argv[2], NULL, 10) : 1000;
    unsigned long long ends = 0, data_errors = 0, buf_errors = 0, roundtrips = 0;
    for (unsigned long long seed = first; seed < first + count; seed++) {
        rng = seed * 0x9E3779B97F4A7C15ull + 1;
        size_t dlen; unsigned char *data = make_data(&dlen);
        int ewbits = 9 + (int)rnd(7);
        size_t slen; unsigned char *stream;
        int mode = rnd(6);                      /* 0..3 valid, 4 mutated, 5 random bytes */
        if (mode == 5) { slen = rnd(5000); stream = malloc(slen ? slen : 1); for (size_t i = 0; i < slen; i++) stream[i] = (unsigned char)next_rand(); }
        else stream = compress_raw(data, dlen, ewbits, &slen);
        int mutated = 0;
        if (mode == 4 && slen) {
            mutated = 1;
            int k = 1 + rnd(8);
            for (int i = 0; i < k; i++) stream[rnd(slen)] ^= (unsigned char)(1u << rnd(8));
            if (rnd(2)) slen = rnd(slen + 1);
        }
        if (mode != 5 && rnd(8) == 0) {          /* garbage after the stream */
            stream = realloc(stream, slen + 64);
            for (int i = 0; i < 64; i++) stream[slen + i] = (unsigned char)next_rand();
            slen += 64;
        }
        int wbits = 8 + (int)rnd(8);
        unsigned wsize = 1u << wbits;
        unsigned char *window = malloc(wsize);
        z_stream strm; memset(&strm, 0, sizeof strm);
        strm.zalloc = count_alloc; strm.zfree = count_free;
        if (inflateBackInit(&strm, wbits, window) != Z_OK) { fprintf(stderr, "init\n"); abort(); }
        in_t in = { stream, slen, 0, NULL, rnd(6) == 0 ? (int)rnd(20) : -1, 0, (int)rnd(4) };
        out_t out = { window, wsize, rnd(3) == 0 ? 1 + (int)rnd(3) : 0, 0, NULL, 0, 0, 0 };
        int calls = 1 + rnd(3);
        unsigned char *pre = NULL;
        for (int c = 0; c < calls; c++) {
            strm.next_in = NULL; strm.avail_in = 0;
            if (rnd(3) == 0 && in.pos < in.len) {   /* preset input, its own exact buffer */
                size_t k = 1 + rnd(16); if (k > in.len - in.pos) k = in.len - in.pos;
                free(pre); pre = malloc(k); memcpy(pre, in.src + in.pos, k); in.pos += k;
                strm.next_in = pre; strm.avail_in = (uInt)k;
            }
            int ret = inflateBack(&strm, in_cb, &in, out_cb, &out);
            if (ret != Z_STREAM_END && ret != Z_DATA_ERROR && ret != Z_BUF_ERROR) {
                fprintf(stderr, "seed %llu: unexpected return %d\n", seed, ret); abort();
            }
            if (ret == Z_STREAM_END) ends++; else if (ret == Z_DATA_ERROR) data_errors++; else buf_errors++;
            if (c == 0 && ret == Z_STREAM_END && mode <= 3 && !mutated && out.fail_policy == 0 && ewbits <= wbits) {
                if (out.glen != dlen || memcmp(out.got, data, dlen) != 0) {
                    fprintf(stderr, "seed %llu: decoded output differs\n", seed); abort();
                }
                roundtrips++;
            }
        }
        if (inflateBackEnd(&strm) != Z_OK) { fprintf(stderr, "end\n"); abort(); }
        if (live_allocs != 0) { fprintf(stderr, "seed %llu: library leak %ld\n", seed, live_allocs); abort(); }
        free(in.piece); free(pre); free(out.got); free(window); free(stream); free(data);
    }
    printf("cases %llu: Z_STREAM_END %llu, Z_DATA_ERROR %llu, Z_BUF_ERROR %llu, round trips %llu\n",
        count, ends, data_errors, buf_errors, roundtrips);
    return 0;
}
