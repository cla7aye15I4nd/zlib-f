/* State-dump driver for the statement test of the inflate format meaning.

   Random raw and zlib streams are made by the real deflate (every level and strategy, window
   widths 8 to 15, preset dictionaries, flushes that make many and empty blocks). They are
   inflated with random input and output splits and flush values. After every inflate call the
   internal decoder state (zlib's own inflate.h) is printed, so that check.py can compare it
   with the parse position that ZlibF/Proof/inflate.c.meaning.lean assigns to the consumed input.

   Output, per session:
     B <wbits> <wrap> <hex source> <hex dictionary>
     C <ret> <total_in> <total_out> <hex output of this call> <state fields...> L <lens> T <codes>
     E
   This is evidence about finitely many histories, not a proof. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "zutil.h"
#include "inftrees.h"
#include "inflate.h"

static unsigned long long rng = 88172645463325252ULL;
static unsigned rnd(void) {
    rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17;
    return (unsigned)(rng >> 11);
}
static unsigned upto(unsigned n) { return n ? rnd() % n : 0; }

static void hex(const unsigned char *p, size_t n) {
    if (n == 0) { putchar('-'); return; }
    for (size_t i = 0; i < n; i++) printf("%02x", p[i]);
}

static size_t make_data(unsigned char *buf, size_t cap) {
    size_t n = upto(4) == 0 ? upto(64) : upto(cap);
    unsigned kind = upto(4);
    for (size_t i = 0; i < n; i++) {
        if (kind == 0) buf[i] = (unsigned char)rnd();
        else if (kind == 1) buf[i] = (unsigned char)("abcab"[upto(5)]);
        else if (kind == 2 && i > 40 && upto(3)) buf[i] = buf[i - 1 - upto(40)];
        else if (i > 300 && upto(4)) buf[i] = buf[i - 1 - upto(i < 33000 ? i - 1 : 32767)];
        else buf[i] = (unsigned char)(upto(3) ? 'a' + upto(6) : rnd());
    }
    return n;
}

#define SRC_CAP 70000
static unsigned char data[SRC_CAP], comp[2 * SRC_CAP + 1024], out[SRC_CAP + 1024], dict[300];

/* One deflate stream. Returns its length; sets *wbits_out and *wrap_out, the dictionary. */
static size_t deflate_source(int *wbits_out, int *wrap_out, size_t *dlen, size_t *n_out) {
    z_stream d;
    memset(&d, 0, sizeof d);
    int wbits = 8 + (int)upto(8);
    int wrap = (int)upto(2); /* 0 raw, 1 zlib */
    int level = (int)upto(11) - 1;
    int strategy = (int)upto(5);
    int memlevel = 1 + (int)upto(9);
    if (wbits == 8) wbits = 9; /* deflate turns 8 into 9 for zlib; keep it simple and equal */
    if (deflateInit2(&d, level, Z_DEFLATED, wrap ? wbits : -wbits, memlevel, strategy) != Z_OK) abort();
    *dlen = upto(3) == 0 ? 1 + upto(sizeof dict) : 0;
    for (size_t i = 0; i < *dlen; i++) dict[i] = (unsigned char)(upto(2) ? 'a' + upto(6) : rnd());
    if (*dlen && deflateSetDictionary(&d, dict, (uInt)*dlen) != Z_OK) abort();
    size_t n = make_data(data, SRC_CAP);
    *n_out = n;
    d.next_out = comp;
    size_t pos = 0;
    while (1) {
        size_t step = upto(3) ? n - pos : upto(n - pos + 1);
        d.next_in = data + pos;
        d.avail_in = (uInt)step;
        pos += step;
        int fl = pos == n ? Z_FINISH : (int[]){Z_NO_FLUSH, Z_SYNC_FLUSH, Z_FULL_FLUSH, Z_PARTIAL_FLUSH, Z_BLOCK}[upto(5)];
        if (upto(8) == 0 && pos < n) deflateParams(&d, (int)upto(10), (int)upto(5));
        d.avail_out = (uInt)(sizeof comp - (size_t)(d.next_out - comp));
        int r = deflate(&d, fl);
        if (fl == Z_FINISH) { if (r != Z_STREAM_END) abort(); break; }
    }
    size_t clen = (size_t)(d.next_out - comp);
    deflateEnd(&d);
    *wbits_out = wbits;
    *wrap_out = wrap;
    return clen;
}

static void dump(z_stream *s, int ret, const unsigned char *o, size_t on) {
    struct inflate_state *st = (struct inflate_state *)s->state;
    printf("C %d %lu %lu ", ret, s->total_in, s->total_out);
    hex(o, on);
    printf(" %d %d %u %u %u %u %u %u %u %u %u %u %lx %u %u %u %u %u %d %lx %lu %d %d %lu",
           (int)st->mode, st->last, st->length, st->offset, st->extra, st->lenbits, st->distbits,
           st->ncode, st->nlen, st->ndist, st->have, (unsigned)st->wrap, st->hold, st->bits,
           st->wsize, st->whave, st->wnext, st->wbits, st->sane, st->check, st->total,
           st->lencode == st->codes ? 1 : 0, st->havedict, (unsigned long)(st->next - st->codes));
    printf(" W ");
    /* the window in chronological order */
    if (st->window && st->whave) {
        static unsigned char chron[1u << 15];
        memcpy(chron, st->window + st->wnext, st->whave - st->wnext);
        memcpy(chron + (st->whave - st->wnext), st->window, st->wnext);
        hex(chron, st->whave);
    } else putchar('-');
    printf(" L ");
    for (unsigned i = 0; i < 320; i++) printf("%x,", st->lens[i]);
    printf(" T ");
    if (st->mode == CODELENS && st->lencode == st->codes)
        for (unsigned i = 0; i < (1u << st->lenbits); i++)
            printf("%x.%x.%x,", st->lencode[i].op, st->lencode[i].bits, st->lencode[i].val);
    else putchar('-');
    putchar('\n');
}

int main(int argc, char **argv) {
    rng ^= argc > 1 ? strtoull(argv[1], 0, 10) * 0x9E3779B97F4A7C15ULL : 0;
    int sessions = argc > 2 ? atoi(argv[2]) : 100;
    for (int k = 0; k < sessions; k++) {
        int wbits, wrap;
        size_t dlen, n;
        size_t clen = deflate_source(&wbits, &wrap, &dlen, &n);
        int iw = wbits + (int)upto((unsigned)(16 - wbits));
        if (wrap && upto(4) == 0) iw = 0;
        printf("B %d %d ", wrap ? iw : -iw, wrap);
        hex(comp, clen);
        putchar(' ');
        hex(dict, dlen);
        putchar('\n');
        z_stream s;
        memset(&s, 0, sizeof s);
        if (inflateInit2(&s, wrap ? iw : -iw) != Z_OK) abort();
        if (!wrap && dlen) inflateSetDictionary(&s, dict, (uInt)dlen);
        size_t ip = 0, op = 0;
        int calls = 0;
        while (calls++ < 100000) {
            size_t ai = upto(4) == 0 ? clen - ip : upto(upto(2) ? 8 : 300);
            if (ai > clen - ip) ai = clen - ip;
            size_t ao = upto(4) == 0 ? sizeof out - op : upto(upto(2) ? 8 : 600);
            if (ao > sizeof out - op) ao = sizeof out - op;
            s.next_in = comp + ip; s.avail_in = (uInt)ai;
            s.next_out = out + op; s.avail_out = (uInt)ao;
            int fl = (int[]){Z_NO_FLUSH, Z_SYNC_FLUSH, Z_FINISH, Z_BLOCK, Z_TREES}[upto(5)];
            int r = inflate(&s, fl);
            size_t used = ai - s.avail_in, made = ao - s.avail_out;
            dump(&s, r, out + op, made);
            ip += used; op += made;
            if (r == Z_NEED_DICT) {
                inflateSetDictionary(&s, dict, (uInt)dlen);
                dump(&s, 99, out, 0);
            }
            if (r == Z_STREAM_END || r == Z_DATA_ERROR || r == Z_MEM_ERROR || r == Z_STREAM_ERROR) break;
            if (ip == clen && r == Z_BUF_ERROR && fl == Z_FINISH && s.avail_out) break;
        }
        inflateEnd(&s);
        printf("E\n");
    }
    return 0;
}
