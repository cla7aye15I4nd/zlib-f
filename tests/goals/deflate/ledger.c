/* Statement test of the deflate "ledger": at every call boundary of random histories of the real C
   (deflate with every flush, deflateParams, deflateSetDictionary, deflatePrime, deflateTune, raw,
   zlib and gzip wrappers, a gzip header set by deflateSetHeader), print what the ledger relates:
   the emitted bits (delivered output, pending bytes, held bits), the open block (recorded symbols,
   block_start, strstart, lookahead, match_available), the window, and on the caller side the
   accepted input and the dictionaries. ledger_check.py checks the claims. Evidence, not proof.

   Output is incremental to stay small: E (delivered ++ pending, a byte stream) and the symbol
   buffer are printed from the first byte not printed before; the harness checks that the bytes
   already printed did not change (line NM otherwise). The window is printed as its CRC-32.
   Usage: ledger [SESSIONS] [SEED] [FULL]: FULL=1 also prints the whole window (W line). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include "deflate.h"

static uint64_t rs;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static unsigned rn(unsigned n) { return n ? (unsigned)(rnd() % n) : 0; }

static unsigned crctab[256];
static void crcinit(void) {
    for (unsigned n = 0; n < 256; n++) {
        unsigned c = n;
        for (int k = 0; k < 8; k++) c = c & 1 ? 0xEDB88320u ^ (c >> 1) : c >> 1;
        crctab[n] = c;
    }
}
static unsigned crc(const unsigned char *p, size_t n) {
    unsigned c = 0xFFFFFFFFu;
    while (n--) c = crctab[(c ^ *p++) & 0xFF] ^ (c >> 8);
    return c ^ 0xFFFFFFFFu;
}
static void hex(const unsigned char *p, size_t n) {
    static const char d[] = "0123456789abcdef";
    if (!n) { putchar('-'); return; }
    for (size_t i = 0; i < n; i++) { putchar(d[p[i] >> 4]); putchar(d[p[i] & 15]); }
}

static unsigned char in[1 << 16], out[1 << 16], dict[4096];
static unsigned char deliv[1 << 21], ebuf[1 << 21], symsave[3 << 16];
static size_t elen, symlen;
static unsigned char extra[1024], name[1024], comment[1024];
static int full;

static void boundary(z_stream *z, char op, int flush, int rc, size_t given, size_t taken) {
    deflate_state *s = (deflate_state *)z->state;
    size_t tout = z->total_out;
    /* E = delivered ++ pending */
    size_t cur = tout + s->pending;
    size_t chk = cur < elen ? cur : elen;
    int nm = cur < elen;
    for (size_t i = 0; i < chk && !nm; i++) {
        unsigned char b = i < tout ? deliv[i] : s->pending_out[i - tout];
        if (b != ebuf[i]) { nm = 1; printf("NM %zu\n", i); }
    }
    if (cur < elen) printf("NM shrink %zu %zu\n", cur, elen);
    size_t from = elen;
    for (size_t i = elen; i < cur; i++) ebuf[i] = i < tout ? deliv[i] : s->pending_out[i - tout];
    if (cur > elen) elen = cur;
    /* symbols */
    size_t sn = s->sym_next, sf = 0;
    while (sf < sn && sf < symlen && s->sym_buf[sf] == symsave[sf]) sf++;
    sf -= sf % 3;
    memcpy(symsave + sf, s->sym_buf + sf, sn - sf);
    symlen = sn;
    size_t wl = (size_t)s->strstart + s->lookahead;
    long bc = -1;
    if (s->block_start >= 0 && s->block_start <= (long)s->strstart)
        bc = crc(s->window + s->block_start, s->strstart - s->block_start);
    printf("R %c %d %d %d %d %d %d %u %u %ld %d %u %d %u %zu %lu %zu %zu %zu %u %zu %ld %zu ",
           op, flush, rc, s->status, s->wrap, s->level, s->strategy, s->strstart, s->lookahead,
           s->block_start, s->match_available, s->insert, s->bi_valid,
           (unsigned)(s->bi_buf & ((1u << s->bi_valid) - 1)), tout, s->pending, sn, given, taken,
           crc(s->window, wl), wl, bc, sf);
    hex(s->sym_buf + sf, sn - sf);
    printf(" %u ", crc(s->sym_buf, sn));
    hex(ebuf + from, cur > from ? cur - from : 0);
    putchar('\n');
    if (full) { printf("W "); hex(s->window, wl); putchar('\n'); }
}

/* Deliver output of a call into deliv (by total_out) */
static void collect(z_stream *z, uLong tout0) {
    size_t n = z->total_out - tout0;
    memcpy(deliv + tout0, out, n);
}

int main(int argc, char **argv) {
    unsigned N = argc > 1 ? (unsigned)atoi(argv[1]) : 1000;
    unsigned base = argc > 2 ? (unsigned)atoi(argv[2]) : 0;
    full = argc > 3 ? atoi(argv[3]) : 0;
    crcinit();
    for (unsigned seed = base; seed < base + N; seed++) {
        rs = (uint64_t)seed * 2654435761u + 88172645463325252ull;
        for (int k = 0; k < 4; k++) rnd();
        int wb = 9 + rn(7), mem = 1 + rn(9), lvl = rn(10), strat = rn(5), wrap = rn(3);
        int wbits = wrap == 0 ? -wb : wrap == 1 ? wb : wb + 16;
        z_stream st; memset(&st, 0, sizeof st);
        if (deflateInit2(&st, lvl, Z_DEFLATED, wbits, mem, strat) != Z_OK) { printf("S %u fail\n", seed); continue; }
        deflate_state *s = (deflate_state *)st.state;
        printf("S %u %d %d %d %d %d %d %u\n", seed, wrap, wb, mem, lvl, strat, OS_CODE, s->w_size);
        elen = 0; symlen = 0;
        unsigned alpha = 1 + rn(8), kind = rn(4);
        for (size_t i = 0; i < sizeof in; i++)
            in[i] = kind == 0 ? (unsigned char)rnd() : kind == 1 ? (rn(5) == 0 ? (unsigned char)rnd() : 'a' + rn(alpha))
                  : kind == 2 ? "abcabd"[(i / (1 + i % 7)) % 6] : (rn(50) == 0 ? (unsigned char)rnd() : 'a' + rn(alpha));
        for (size_t i = 0; i < sizeof dict; i++) dict[i] = rn(3) ? 'a' + rn(alpha) : (unsigned char)rnd();
        gz_header g; memset(&g, 0, sizeof g);
        if (wrap == 2 && rn(2)) {
            if (rn(2)) { g.extra_len = rn(2) ? rn(40) : rn(1000); for (unsigned i = 0; i < g.extra_len; i++) extra[i] = rnd(); g.extra = extra; }
            if (rn(2)) { size_t l = rn(2) ? rn(30) : rn(1000); for (size_t i = 0; i < l; i++) name[i] = 1 + rn(255); name[l] = 0; g.name = name; }
            if (rn(2)) { size_t l = rn(2) ? rn(30) : rn(1000); for (size_t i = 0; i < l; i++) comment[i] = 1 + rn(255); comment[l] = 0; g.comment = comment; }
            g.hcrc = rn(2); g.text = rn(2); g.time = (uLong)rnd(); g.os = rn(512);
            int rc = deflateSetHeader(&st, &g);
            printf("H %d %d %lu %d %d ", rc, g.text, g.time & 0xffffffffUL, g.os, g.hcrc);
            if (g.extra) { putchar('x'); hex(extra, g.extra_len); } else putchar('-');
            putchar(' ');
            if (g.name) { putchar('x'); hex(name, strlen((char *)name)); } else putchar('-');
            putchar(' ');
            if (g.comment) { putchar('x'); hex(comment, strlen((char *)comment)); } else putchar('-');
            putchar('\n');
        }
        size_t pos = 0;
        int started = 0;
        boundary(&st, 'i', -1, 0, 0, 0);
        for (int step = 1; step < 50; step++) {
            unsigned op = rn(20);
            if (op < 12) {
                size_t n = rn(3) == 0 ? rn(3000) : rn(250);
                if (pos + n > sizeof in) n = sizeof in - pos;
                int fl = (int[]){0, 0, 0, 0, 1, 2, 3, 5, 4}[rn(9)];
                st.next_in = in + pos; st.avail_in = (uInt)n;
                st.next_out = out; st.avail_out = 1 + rn(rn(2) ? 40 : rn(2) ? 3000 : 30000);
                uLong t0 = st.total_out;
                int rc = deflate(&st, fl);
                collect(&st, t0);
                size_t took = n - st.avail_in;
                printf("I "); hex(in + pos, took); putchar('\n');
                pos += took; started = 1;
                boundary(&st, 'd', fl, rc, n, took);
                if (rc == Z_STREAM_END) break;
            } else if (op < 15) {
                st.next_out = out; st.avail_out = 1 + rn(rn(2) ? 40 : 3000);
                st.next_in = in + pos; st.avail_in = 0;
                uLong t0 = st.total_out;
                int l = rn(10), sg = rn(5);
                int rc = deflateParams(&st, l, sg);
                collect(&st, t0);
                printf("I -\n");
                boundary(&st, 'p', l * 10 + sg, rc, 0, 0);
            } else if (op < 17) {
                size_t dl = 1 + rn(rn(2) ? 4000 : 100);
                if (wrap == 1 && started && rn(4)) continue;
                int rc = deflateSetDictionary(&st, dict, (uInt)dl);
                printf("D %d ", rc); hex(dict, dl); putchar('\n');
                boundary(&st, 's', -1, rc, 0, 0);
            } else if (op < 19) {
                if (started) continue;
                int bits = rn(17), value = (int)rnd();
                int rc = deflatePrime(&st, bits, value);
                printf("P %d %d %u\n", rc, bits, (unsigned)value & ((1u << bits) - 1));
                boundary(&st, 'r', bits, rc, 0, 0);
            } else {
                int rc = deflateTune(&st, rn(300), rn(300), rn(300), rn(5000));
                boundary(&st, 't', -1, rc, 0, 0);
            }
        }
        printf("X\n");
        deflateEnd(&st);
    }
    return 0;
}
