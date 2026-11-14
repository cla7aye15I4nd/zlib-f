/* Statement test for Goal.deflateCopy and Goal.deflateCopy_safety on the real C.
 * For many source histories and for every subset of the five allocations failing:
 *  - rc is Z_OK or Z_MEM_ERROR, never anything else;
 *  - Z_MEM_ERROR: dest->state == NULL, every block allocated by the copy is freed, other dest fields unchanged,
 *    and at least one allocation failed;
 *  - Z_OK: exactly 5 new live blocks; the source keeps working, and the copy produces the same output as the source;
 *  - the source record is unchanged;
 *  - an inconsistent source (zalloc or zfree NULL, or no state) is refused with Z_STREAM_ERROR and
 *    dest->state = NULL. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "zlib.h"

static unsigned failmask, ncalls;   /* allocation k (0-based) fails when bit k is set */
static long live;
static voidpf al(voidpf o, uInt n, uInt s) {
    (void)o;
    unsigned k = ncalls++;
    if (k < 32 && (failmask >> k) & 1) return NULL;
    live++;
    return calloc(n, s);
}
static void fr(voidpf o, voidpf p) { (void)o; if (p) { live--; free(p); } }

static unsigned char in[100000], o1[200000], o2[200000];
static long bad, oks, mems, combos, refusals;

static unsigned run(z_stream *z, unsigned char *out, unsigned n, int flush) {
    z->next_in = in + 50000; z->avail_in = n; z->next_out = out; z->avail_out = sizeof o1;
    int r = deflate(z, flush); (void)r;
    return (unsigned)(sizeof o1 - z->avail_out);
}

int main(void) {
    unsigned seed = 3;
    for (int i = 0; i < (int)sizeof in; i++) { seed = seed * 1103515245 + 12345; in[i] = (i % 1000 < 400) ? (unsigned char)(seed >> 24) : (unsigned char)("abcde"[i % 5]); }
    int pre[] = {0, 10, 3000, 40000, 90000};
    for (int level = 0; level <= 9; level += 1)
    for (int strategy = 0; strategy <= 4; strategy++)
    for (int wi = 0; wi < 3; wi++)
    for (int mi = 0; mi < 2; mi++)
    for (int pi = 0; pi < 5; pi++)
    for (int fl = 0; fl < 3; fl++)
    for (unsigned mask = 0; mask < 32; mask++) {
        int wbits = (int[]){15, 9, 31}[wi], memLevel = (int[]){1, 9}[mi];
        int flush = (int[]){Z_NO_FLUSH, Z_SYNC_FLUSH, Z_BLOCK}[fl];
        z_stream src; memset(&src, 0, sizeof src); src.zalloc = al; src.zfree = fr;
        failmask = 0; ncalls = 0;
        if (deflateInit2(&src, level, Z_DEFLATED, wbits, memLevel, strategy) != Z_OK) return 2;
        src.next_in = in; src.avail_in = pre[pi]; src.next_out = o1; src.avail_out = sizeof o1;
        deflate(&src, flush);
        long live0 = live;
        z_stream before = src;
        z_stream dst; memset(&dst, 0x5a, sizeof dst);
        z_stream dst0 = dst;
        failmask = mask; ncalls = 0;
        int rc = deflateCopy(&dst, &src);
        unsigned used = ncalls;
        failmask = 0;
        combos++;
        if (memcmp(&before, &src, sizeof src) != 0) { if (bad++ < 5) printf("source changed L%d m%u\n", level, mask); }
        if (rc == Z_MEM_ERROR) {
            mems++;
            z_stream exp = dst0; exp.state = NULL;
            int anyfail = (mask & ((1u << used) - 1)) != 0;
            if (live != live0 || memcmp(&exp, &dst, sizeof dst) != 0 || !anyfail)
                if (bad++ < 5) printf("MEM bad L%d m%u live %ld/%ld used %u\n", level, mask, live, live0, used);
        } else if (rc == Z_OK) {
            oks++;
            if (live != live0 + 5 || used != 5 || (mask & 31) != 0) if (bad++ < 5) printf("OK bad L%d m%u live %ld/%ld\n", level, mask, live, live0);
            unsigned a = run(&src, o1, 20000, Z_FINISH), b = run(&dst, o2, 20000, Z_FINISH);
            if (a != b || memcmp(o1, o2, a) != 0) if (bad++ < 5) printf("copy output differs L%d S%d\n", level, strategy);
            deflateEnd(&dst);
        } else { if (bad++ < 5) printf("rc %d\n", rc); }
        deflateEnd(&src);
        if (live != 0) { if (bad++ < 5) printf("leak %ld L%d m%u rc %d\n", live, level, mask, rc); live = 0; }
    }
    /* An inconsistent source (zalloc NULL, zfree NULL, or no state) is refused: Z_STREAM_ERROR,
     * dest->state = NULL, the other destination bytes unchanged, nothing allocated. */
    for (int k = 0; k < 3; k++) {
        z_stream src; memset(&src, 0, sizeof src); src.zalloc = al; src.zfree = fr;
        if (k == 2) { if (deflateInit(&src, 6) != Z_OK) return 2; src.zalloc = Z_NULL; }
        else if (k == 1) src.zfree = Z_NULL;
        z_stream dst; memset(&dst, 0x5a, sizeof dst);
        z_stream exp = dst; exp.state = NULL;
        long live0 = live;
        int rc = deflateCopy(&dst, &src);
        if (rc != Z_STREAM_ERROR || memcmp(&exp, &dst, sizeof dst) != 0 || live != live0)
            if (bad++ < 5) printf("refusal bad k%d rc %d\n", k, rc);
        if (k == 2) { src.zalloc = al; deflateEnd(&src); }
        refusals++;
    }
    printf("combos %ld ok %ld mem %ld refusals %ld bad %ld\n", combos, oks, mems, refusals, bad);
    return 0;
}
