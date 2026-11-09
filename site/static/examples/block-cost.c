/* Reproduce the blockcost scene's complete, deliberately selected record streams.
 * Source: zlib 757f0527154291bcf6bfbd6396ecde6bedd2db95, ordinary packed build.
 * From the repository root (do not compile trees.c separately):
 * cc -O2 -I zlib site/static/examples/block-cost.c zlib/deflate.c \
 *    zlib/inflate.c zlib/inftrees.c zlib/inffast.c zlib/adler32.c \
 *    zlib/crc32.c zlib/zutil.c -o /tmp/block-cost
 * /tmp/block-cost
 * BLOCK_COST_TRACE=1 /tmp/block-cost  # also print each measured combination
 *
 * Including trees.c exposes its actual private constructors to this driver.
 * No encoder implementation is replaced. This selects records directly; it
 * does not predict which records a public deflate call would select.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "trees.c"

#define CHECK(condition) do { \
    if (!(condition)) { fprintf(stderr, "check failed at line %d\n", __LINE__); abort(); } \
} while (0)

static void start(z_stream *z, int fixed) {
    memset(z, 0, sizeof(*z));
    CHECK(deflateInit2(z, 6, Z_DEFLATED, -15, 8,
                      fixed ? Z_FIXED : Z_DEFAULT_STRATEGY) == Z_OK);
}

static unsigned records(deflate_state *s, int kind, unsigned char *raw) {
    unsigned n = 0;
    if (kind == 0) {
        raw[n++] = 'A'; raw[n++] = 'B';
        _tr_tally(s, 0, 'A'); _tr_tally(s, 0, 'B');
        _tr_tally(s, 2, 3); /* distance 2, length offset 3 => length 6 */
        while (n < 8) { raw[n] = raw[n - 2]; n++; }
    } else {
        unsigned count = kind == 1 ? 16 : 256;
        const char *pattern = "AAAAAAAABBBBCCDD";
        for (n = 0; n < count; n++) {
            raw[n] = kind == 3 ? (unsigned char)n : pattern[n % 16];
            _tr_tally(s, 0, raw[n]);
        }
    }
    return n;
}

/* Reach offset r with a real nonfinal fixed block: header 3 + n*9 + end 7.
 * Literal 144 has fixed width 9. Flush full bytes, retaining at most 7 bits.
 */
static unsigned prefix(deflate_state *s, unsigned r) {
    unsigned n = (r + 6) % 8;
    int old = s->strategy;
    s->strategy = Z_FIXED;
    for (unsigned i = 0; i < n; i++) _tr_tally(s, 0, 144);
    _tr_flush_block(s, NULL, n, 0);
    _tr_flush_bits(s);
    s->strategy = old;
    CHECK(s->bi_valid == (int)r);
    return n;
}

int main(void) {
    for (int kind = 0; kind < 4; kind++) {
        unsigned char raw[256];
        unsigned lf[L_CODES], df[D_CODES];
        z_stream z;
        start(&z, 0);
        deflate_state *s = z.state;
        unsigned len = records(s, kind, raw);
        /* Save observed frequencies before the Freq/Code union is reused. */
        for (int i = 0; i < L_CODES; i++) lf[i] = s->dyn_ltree[i].Freq;
        for (int i = 0; i < D_CODES; i++) df[i] = s->dyn_dtree[i].Freq;
        build_tree(s, &s->l_desc);
        build_tree(s, &s->d_desc);
        unsigned payload = 0;
        for (int i = 0; i < L_CODES; i++) payload += lf[i] * s->dyn_ltree[i].Len;
        for (int i = 0; i < D_CODES; i++) payload += df[i] * s->dyn_dtree[i].Len;
        /* These four streams require no numeric length/distance extra bits.
         * END_BLOCK was initialized with frequency 1 and is included above.
         */
        build_bl_tree(s);
        unsigned dynamic = s->opt_len, fixed = s->static_len;
        printf("case %d: raw=%u fixed_payload=%u dynamic_payload=%u "
               "description=%u dynamic_total=%u\n", kind, len, fixed,
               payload, dynamic - payload, dynamic);
        deflateEnd(&z);

        for (unsigned r = 0; r < 8; r++)
        for (int forced = 0; forced < 2; forced++)
        for (int available = 0; available < 2; available++) {
            start(&z, forced);
            s = z.state;
            unsigned np = prefix(s, r);
            unsigned offset = 10 + 9 * np;
            records(s, kind, raw);
            _tr_flush_block(s, available ? (char *)raw : NULL, len, 1);
            unsigned bit = offset + 1; /* BTYPE follows BFINAL. */
            unsigned btype = (s->pending_buf[bit / 8] >> (bit % 8)) & 3;
            if (bit % 8 == 7)
                btype = ((s->pending_buf[bit / 8] >> 7) |
                         (s->pending_buf[bit / 8 + 1] << 1)) & 3;
            unsigned fixedb = (fixed + 10) / 8;
            unsigned dynamicb = (dynamic + 10) / 8;
            unsigned chosen = forced || fixedb <= dynamicb ? fixedb : dynamicb;
            unsigned expected = available && len + 4 <= chosen ? 0 :
                                forced || fixedb <= dynamicb ? 1 : 2;
            CHECK(btype == expected);
            unsigned meaningful = expected == 0 ?
                3 + (8 - (r + 3) % 8) % 8 + 32 + 8 * len :
                3 + (expected == 1 ? fixed : dynamic);
            unsigned wire = expected == 0 ? meaningful :
                meaningful + (8 - (r + meaningful) % 8) % 8;
            CHECK(8 * s->pending == offset + wire);

            unsigned char out[300];
            z_stream iz = {0};
            CHECK(inflateInit2(&iz, -15) == Z_OK);
            iz.next_in = s->pending_buf; iz.avail_in = s->pending;
            iz.next_out = out; iz.avail_out = sizeof(out);
            CHECK(inflate(&iz, Z_FINISH) == Z_STREAM_END);
            CHECK(iz.total_out == np + len);
            CHECK(memcmp(out + np, raw, len) == 0);
            for (unsigned i = 0; i < np; i++) CHECK(out[i] == 144);
            inflateEnd(&iz);
            if (getenv("BLOCK_COST_TRACE"))
                printf("wire case=%d offset=%u fixed=%d raw=%d selected=%u "
                       "bits=%lu\n", kind, r, forced, available, btype,
                       (unsigned long)(8 * s->pending - offset));
            if (r == 0 && !forced && available) {
                /* Here the prefix is 64 bits; report only this final block. */
                printf("  selected=%u standalone_bytes=%lu\n", expected,
                       (unsigned long)s->pending - 8);
            }
            deflateEnd(&z);
        }
    }
    puts("128 combinations: branch, final size, and decoded output checked");
    return 0;
}
