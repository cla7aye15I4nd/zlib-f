/* State-level test of ParseMeaning (inflate format meaning), stream side. Derived from
 * tests/goals/inflate/driver.c: protocol sessions only, and after every inflate and
 * inflateSetDictionary call a line
 *   T mode bits hold wrap flags havedict wbits check total headnull last wsize sane
 * with the private inflate_state fields.
 *
 * Original description: Statement test for the inflate goals: random sessions on the REAL libz.a (pinned zlib plus
 * patches). Each session builds a source stream with the real deflate (raw, zlib with or without
 * a preset dictionary, gzip with a random gz_header), optionally damages it, appends junk, and
 * then decodes it with inflate under random input and output splits and flush values.
 *
 * A "protocol" session (X ... 1) uses only init, inflate and inflateSetDictionary: it has the
 * shape of InflateProtocolTrace, and check.py checks the format clauses of Goal.inflate_sequence
 * and InflateCompletes on it. A "free" session (X ... 0) also calls every other stream operation
 * (header capture, sync, resets, prime, validate, undermine, copy, queries); only the per-call
 * clauses of Goal.inflate are checked there, and the sanitizer build checks memory safety.
 *
 * Usage: driver SEED COUNT. Output lines (fields separated by one space):
 *   S wb rc                       inflateInit2_ (a failed init ends the session)
 *   X kind failing                1: protocol session, 0: free session; failing: allocations
 *                                 may fail
 *   G wrap valid gwbits hex       source: layer (raw zlib gzip), 0 if damaged, deflate window bits
 *   O hex                         the data the source was made from
 *   K hex                         the dictionary the source was made with (- if none)
 *   C probe flush nullin nullout ain aout mode havedict total_in total_out
 *     -> rc ain' aout' mode' total_in' total_out' same consumedhex outhex
 *   D rc hex                      inflateSetDictionary
 *   Q name rc                     any other operation (free sessions only)
 *   E rc                          inflateEnd
 * "same" is 1 when the z_stream and the inflate_state are bytewise unchanged by the call.
 * All randomness comes from SEED. Undefined behaviour of the C is never generated. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <zlib.h>
#include "zutil.h"
#include "inftrees.h"
#include "inflate.h"

static uint64_t rs;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static unsigned rn(unsigned n) { return n ? (unsigned)(rnd() % n) : 0; }

static const char *WORDS[] = {"the ", "quick ", "brown ", "fox ", "zlib ", "inflate ", "window ", "huffman "};

static void data(unsigned char *b, size_t n, unsigned kind) {
    size_t i = 0;
    switch (kind % 6) {
    case 0: for (; i < n; i++) b[i] = (unsigned char)rnd(); break;
    case 1: memset(b, 0, n); break;
    case 2: while (i < n) { const char *w = WORDS[rn(8)]; for (size_t k = 0; w[k] && i < n; k++) b[i++] = (unsigned char)w[k]; } break;
    case 3: { unsigned char p[7]; for (int k = 0; k < 7; k++) p[k] = (unsigned char)rnd(); for (; i < n; i++) b[i] = p[i % 7]; } break;
    case 4: for (; i < n; i++) b[i] = (unsigned char)i; break;
    default:
        while (i < n) {
            if (rn(2)) { const char *w = WORDS[rn(8)]; for (size_t k = 0; w[k] && i < n; k++) b[i++] = (unsigned char)w[k]; }
            else { unsigned r = 1 + rn(12); for (unsigned k = 0; k < r && i < n; k++) b[i++] = (unsigned char)rnd(); }
        }
    }
}

/* The allocator of a session: calloc, failing once in `failing` calls when failing is nonzero.
 * It stands for the default allocator with h.allocOk false. */
static unsigned failing;
static voidpf zalloc_test(voidpf opaque, uInt items, uInt size) {
    (void)opaque;
    if (failing && rn(failing) == 0) return Z_NULL;
    return calloc(items, size);
}
static void zfree_test(voidpf opaque, voidpf p) { (void)opaque; free(p); }

static void state_line(z_streamp strm) {
    struct inflate_state *st = (struct inflate_state *)strm->state;
    printf("T %d %u %llu %d %d %d %u %lu %lu %d %d %u %d\n", st->mode, st->bits,
           (unsigned long long)st->hold, st->wrap, st->flags, st->havedict, st->wbits,
           (unsigned long)st->check, (unsigned long)st->total, st->head == Z_NULL, st->last,
           st->wsize, st->sane);
}

static void hexout(const unsigned char *b, size_t n) {
    if (n == 0) { putchar('-'); return; }
    for (size_t i = 0; i < n; i++) printf("%02x", b[i]);
}

static size_t pick_len(void) {
    switch (rn(5)) {
    case 0: return rn(30);
    case 1: return rn(600);
    case 2: return rn(5000);
    case 3: return 20000 + rn(50000);
    default: return rn(2500);
    }
}

/* Compress with the real deflate. layer: 0 raw, 1 zlib, 2 gzip. Returns the length. */
static size_t make_source(int layer, int gwbits, const unsigned char *dict, size_t dl,
                          const unsigned char *in, size_t n, unsigned char **outp) {
    z_stream d;
    memset(&d, 0, sizeof d);
    int wb = layer == 0 ? -gwbits : layer == 2 ? gwbits + 16 : gwbits;
    int level = (int)rn(10), mem = 1 + (int)rn(9), strategy = (int)rn(5);
    if (deflateInit2(&d, level, Z_DEFLATED, wb, mem, strategy) != Z_OK) { *outp = NULL; return 0; }
    gz_header gh;
    unsigned char name[40], comment[40], extra[300];
    if (layer == 2 && rn(2)) {
        memset(&gh, 0, sizeof gh);
        gh.text = (int)rn(2); gh.time = (uLong)rnd() & 0xffffffffu; gh.os = (int)rn(256);
        if (rn(2)) { size_t k = rn(30); for (size_t j = 0; j < k; j++) name[j] = (unsigned char)(1 + rn(255)); name[k] = 0; gh.name = name; }
        if (rn(2)) { size_t k = rn(30); for (size_t j = 0; j < k; j++) comment[j] = (unsigned char)(1 + rn(255)); comment[k] = 0; gh.comment = comment; }
        if (rn(2)) { gh.extra_len = rn(300); data(extra, gh.extra_len, rn(6)); gh.extra = extra; }
        gh.hcrc = (int)rn(2);
        deflateSetHeader(&d, &gh);
    }
    if (dl && layer != 2) deflateSetDictionary(&d, dict, (uInt)dl);
    size_t cap = deflateBound(&d, (uLong)n) + 1024;
    unsigned char *out = malloc(cap);
    d.next_in = (unsigned char *)in; d.avail_in = (uInt)n;
    d.next_out = out; d.avail_out = (uInt)cap;
    int rc = deflate(&d, Z_FINISH);
    size_t len = cap - d.avail_out;
    deflateEnd(&d);
    if (rc != Z_STREAM_END) { free(out); *outp = NULL; return 0; }
    *outp = out;
    return len;
}

static const int FLUSHES[] = {Z_NO_FLUSH, Z_NO_FLUSH, Z_NO_FLUSH, Z_PARTIAL_FLUSH, Z_SYNC_FLUSH,
                              Z_FULL_FLUSH, Z_FINISH, Z_FINISH, Z_BLOCK, Z_TREES};

static unsigned out_chunk(unsigned mode) {
    switch (mode) {
    case 0: return 1 + rn(3);
    case 1: return 1 + rn(40);
    case 2: return 1 + rn(800);
    case 3: return 1 + rn(70000);
    default: return rn(8) == 0 ? 0 : 1 + rn(5000);
    }
}

static int pick_wb(void) {
    switch (rn(12)) {
    case 0: return -(8 + (int)rn(8));
    case 1: return 0;
    case 2: return 8 + (int)rn(8);
    case 3: return 16;
    case 4: return 24 + (int)rn(8);
    case 5: return 32;
    case 6: return 40 + (int)rn(8);
    case 7: { static const int bad[] = {-16, -7, 1, 7, 17, 23, 48, 64, -1}; return bad[rn(9)]; }
    case 8: return -15;
    case 9: return 15;
    case 10: return 31;
    default: return 47;
    }
}

static void session(void) {
    z_stream *strm = calloc(1, sizeof *strm);
    int wb = pick_wb();
    failing = rn(6) == 0 ? 1 + rn(4) : 0;
    strm->zalloc = zalloc_test; strm->zfree = zfree_test;
    int rc = inflateInit2(strm, wb);
    printf("S %d %d\n", wb, rc);
    if (rc != Z_OK) { free(strm); return; }
    int protocol = 1;
    printf("X %d %d\n", protocol, failing != 0);
    state_line(strm);

    /* The source layer follows the configuration; automatic detection picks zlib or gzip. */
    int layer = wb < 0 ? 0 : wb < 16 ? 1 : wb < 32 ? 2 : (rn(2) ? 1 : 2);
    if (rn(25) == 0) layer = (int)rn(3);   /* sometimes the wrong layer */
    int cfgbits = wb < 0 ? -wb : wb % 16;
    int gwbits = cfgbits ? cfgbits : 15;
    if (rn(4) == 0) gwbits = 9 + (int)rn(7);
    size_t n = pick_len();
    unsigned char *plain = malloc(n + 1);
    data(plain, n, rn(6));
    size_t dl = 0;
    unsigned char *dict = NULL;
    if (layer != 2 && rn(3) == 0) {
        dl = rn(3) ? 1 + rn(400) : 1 + rn(70000);
        dict = malloc(dl);
        data(dict, dl, rn(6));
    }
    unsigned char *src;
    size_t sl = make_source(layer, gwbits, dict, dl, plain, n, &src);
    if (src == NULL) { sl = 0; src = malloc(1); }
    int valid = 1;
    if (sl && rn(4) == 0) {
        valid = 0;
        switch (rn(3)) {
        case 0: src[rn((unsigned)sl)] ^= (unsigned char)(1u << rn(8)); break;
        case 1: sl = rn((unsigned)sl); break;
        default: { size_t i = rn((unsigned)sl); src[i] = (unsigned char)rnd(); }
        }
    }
    size_t junk = rn(3) ? 0 : rn(20);
    unsigned char *buf = malloc(sl + junk + 1);
    memcpy(buf, src, sl);
    data(buf + sl, junk, 0);
    printf("G %s %d %d ", layer == 0 ? "raw" : layer == 1 ? "zlib" : "gzip", valid, gwbits); hexout(src, sl); printf("\n");
    printf("O "); hexout(plain, n); printf("\n");
    printf("K "); hexout(dict, dl); printf("\n");

    size_t cap = n + 70000 + 16;
    unsigned char *out = malloc(cap);
    size_t taken = 0, produced = 0, total = sl + junk;
    unsigned omode = rn(5);
    gz_header head;
    unsigned char hname[64], hcomm[64], hextra[512];

    /* raw streams take their dictionary before the first byte */
    if (dl && wb < 0 && rn(4) != 0) {
        rc = inflateSetDictionary(strm, dict, (uInt)dl);
        printf("D %d ", rc); hexout(dict, dl); printf("\n");
        state_line(strm);
    }
    int ended = 0;
    for (unsigned calls = 0; calls < 200000 && ended < 3; calls++) {
        struct inflate_state *st = (struct inflate_state *)strm->state;
        unsigned op = rn(40);
        if (!protocol && op < 8) {
            switch (op) {
            case 0:
                memset(&head, 0, sizeof head);
                if (rn(2)) { head.name = hname; head.name_max = rn(65); }
                if (rn(2)) { head.comment = hcomm; head.comm_max = rn(65); }
                if (rn(2)) { head.extra = hextra; head.extra_max = rn(513); }
                printf("Q getheader %d\n", inflateGetHeader(strm, &head)); break;
            case 1: {
                strm->next_in = buf + taken; strm->avail_in = (uInt)rn((unsigned)(total - taken + 1));
                uInt a0 = strm->avail_in;
                rc = inflateSync(strm);
                taken += a0 - strm->avail_in;
                printf("Q sync %d\n", rc); break; }
            case 2: printf("Q reset %d\n", inflateReset(strm)); break;
            case 3: printf("Q reset2 %d\n", inflateReset2(strm, pick_wb())); break;
            case 4: { int b = (int)rn(20) - 2; printf("Q prime %d\n", inflatePrime(strm, b, (int)rnd())); break; }
            case 5: printf("Q validate %d\n", inflateValidate(strm, (int)rn(2))); break;
            case 6: {
                unsigned char dbuf[32768]; uInt dlen = 0;
                printf("Q getdict %d\n", inflateGetDictionary(strm, rn(2) ? dbuf : NULL, &dlen));
                printf("Q mark %ld\n", inflateMark(strm));
                printf("Q codesused %lu\n", inflateCodesUsed(strm));
                printf("Q syncpoint %d\n", inflateSyncPoint(strm)); break; }
            default: {
                z_stream *copy = calloc(1, sizeof *copy);
                copy->zalloc = zalloc_test; copy->zfree = zfree_test;
                rc = inflateCopy(copy, strm);
                printf("Q copy %d\n", rc);
                if (rc == Z_OK) { printf("Q endold %d\n", inflateEnd(strm)); free(strm); strm = copy; }
                else free(copy);
                if (rn(5) == 0) printf("Q undermine %d\n", inflateUndermine(strm, 1));
            }
            }
            continue;
        }
        int probe = protocol && rn(12) == 0;
        size_t ain = rn(4) == 0 ? 0 : rn((unsigned)(total - taken + 1));
        if (rn(3) == 0) ain = total - taken;
        int flush = FLUSHES[rn(10)];
        unsigned aout = out_chunk(omode);
        if (rn(10) == 0) aout = 70000;
        int nullin = 0, nullout = 0;
        if (rn(60) == 0) flush = rn(2) ? -1 : 7;
        if (rn(60) == 0) nullout = 1;
        if (rn(60) == 0) { nullin = 1; ain = 1 + rn(5); }
        if (probe) {
            ain = sl - taken < total - taken ? sl - taken : total - taken;
            if (taken > sl) ain = 0;
            aout = (unsigned)(cap - produced > 140000 ? 140000 : cap - produced);
            flush = rn(3) == 0 ? Z_NO_FLUSH : rn(2) ? Z_SYNC_FLUSH : Z_FINISH;
            nullin = nullout = 0;
        }
        if (aout > cap - produced) aout = (unsigned)(cap - produced);
        strm->next_in = nullin ? Z_NULL : buf + taken;
        strm->avail_in = (uInt)ain;
        strm->next_out = nullout ? Z_NULL : out + produced;
        strm->avail_out = aout;
        printf("C %d %d %d %d %u %u %d %d %lu %lu", probe, flush, nullin, nullout, strm->avail_in,
               strm->avail_out, st->mode, st->havedict, strm->total_in, strm->total_out);
        z_stream zb;
        struct inflate_state sb;
        memcpy(&zb, strm, sizeof zb);
        memcpy(&sb, st, sizeof sb);
        rc = inflate(strm, flush);
        st = (struct inflate_state *)strm->state;
        int same = !memcmp(&zb, strm, sizeof zb) && !memcmp(&sb, st, sizeof sb);
        size_t used = ain - strm->avail_in, wrote = aout - strm->avail_out;
        printf(" -> %d %u %u %d %lu %lu %d ", rc, strm->avail_in, strm->avail_out, st->mode,
               strm->total_in, strm->total_out, same);
        hexout(nullin ? NULL : buf + taken, nullin ? 0 : used); putchar(' ');
        hexout(out + produced, nullout ? 0 : wrote);
        printf("\n");
        state_line(strm);
        if (!nullin) taken += used;
        if (!nullout) produced += wrote;
        if (rc == Z_NEED_DICT && rn(6) != 0) {
            const unsigned char *dd = dict; size_t dn = dl; unsigned char wrong[8];
            if (rn(8) == 0 || dict == NULL) { data(wrong, 8, 0); dd = wrong; dn = rn(9); }
            rc = inflateSetDictionary(strm, dd, (uInt)dn);
            printf("D %d ", rc); hexout(dd, dn); printf("\n");
            state_line(strm);
        }
        if (protocol && wb < 0 && dl && rn(200) == 0) {
            rc = inflateSetDictionary(strm, dict, (uInt)dl);
            printf("D %d ", rc); hexout(dict, dl); printf("\n");
            state_line(strm);
        }
        if (rc == Z_STREAM_END || rc == Z_DATA_ERROR || rc == Z_MEM_ERROR) ended++;
        if (produced >= cap || (taken >= total && rn(4) == 0)) ended++;
    }
    printf("E %d\n", inflateEnd(strm));
    free(strm); free(plain); free(dict); free(src); free(buf); free(out);
}

int main(int argc, char **argv) {
    if (argc != 3) { fprintf(stderr, "usage: driver SEED COUNT\n"); return 2; }
    rs = strtoull(argv[1], NULL, 10) * 2654435761u + 88172645463325252ull;
    long count = strtol(argv[2], NULL, 10);
    for (long i = 0; i < count; i++) session();
    return 0;
}
