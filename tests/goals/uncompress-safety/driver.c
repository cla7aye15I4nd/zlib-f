/* Statement test for the uncompress* safety goals (Goal.uncompress*_safe).
 * For random valid, truncated and corrupted zlib streams, random capacities and
 * injected allocation failures, call uncompress2 and uncompress with exact-size
 * heap buffers (so AddressSanitizer catches any access outside them) and check:
 *   - the return code is Z_OK, Z_BUF_ERROR, Z_DATA_ERROR or Z_MEM_ERROR;
 *   - the stored output length is at most the capacity, the stored consumed
 *     length at most the source length;
 *   - Z_MEM_ERROR only when an allocation failed;
 *   - every allocation is freed on return (live allocation count back to 0);
 *   - bytes past the stored output length are not written (dest is checked
 *     against a canary fill).
 * Build with -fsanitize=address,undefined and link with -Wl,--wrap=malloc,--wrap=free. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "zlib.h"

static long live, fail_at = -1, count;
void *__real_malloc(size_t);
void __real_free(void *);
void *__wrap_malloc(size_t n) {
    if (count++ == fail_at) return NULL;
    void *p = __real_malloc(n);
    if (p) live++;
    return p;
}
void __wrap_free(void *p) { if (p) live--; __real_free(p); }

static unsigned long rng = 1;
static unsigned rnd(void) { rng = rng * 6364136223846793005UL + 1442695040888963407UL; return (unsigned)(rng >> 33); }

static int bad = 0;
static long seen[4], memFailed;
static void fail(const char *what, int rc, unsigned long cap, unsigned long n) {
    fprintf(stderr, "violation: %s (rc %d, cap %lu, n %lu)\n", what, rc, cap, n);
    bad = 1;
}

static void one(const unsigned char *src, unsigned long n, unsigned long cap, long failAt, int counted) {
    unsigned char *s = __real_malloc(n ? n : 1), *d = __real_malloc(cap ? cap : 1);
    memcpy(s, src, n);
    memset(d, 0xA5, cap ? cap : 1);
    uLongf dl = cap; uLong sl = n;
    count = 0; fail_at = failAt; live = 0;
    int rc = counted ? uncompress2(cap ? d : NULL, &dl, n ? s : NULL, &sl)
                     : uncompress(cap ? d : NULL, &dl, n ? s : NULL, n);
    long failed = (failAt >= 0 && count > failAt);
    fail_at = -1;
    if (rc != Z_OK && rc != Z_BUF_ERROR && rc != Z_DATA_ERROR && rc != Z_MEM_ERROR) fail("rc", rc, cap, n);
    if (dl > cap) fail("output length", rc, cap, n);
    if (counted && sl > n) fail("consumed length", rc, cap, n);
    if (rc == Z_MEM_ERROR && !failed) fail("mem without failure", rc, cap, n);
    if (live != 0) fail("leak", rc, cap, n);
    seen[rc == Z_OK ? 0 : rc == Z_BUF_ERROR ? 1 : rc == Z_DATA_ERROR ? 2 : 3]++;
    if (failed) memFailed++;
    for (unsigned long i = dl; i < cap; i++)
        if (d[i] != 0xA5) { fail("write past output", rc, cap, n); break; }
    __real_free(s); __real_free(d);
}

int main(int argc, char **argv) {
    rng = argc > 1 ? strtoul(argv[1], 0, 10) : 1;
    long runs = argc > 2 ? strtol(argv[2], 0, 10) : 2000;
    static unsigned char plain[4096], comp[8192];
    for (long k = 0; k < runs; k++) {
        unsigned long pn = rnd() % 3000;
        for (unsigned long i = 0; i < pn; i++) plain[i] = (rnd() % 4) ? 'a' + rnd() % 3 : rnd();
        uLongf cn = sizeof comp;
        if (compress2(comp, &cn, plain, pn, rnd() % 10) != Z_OK) return 2;
        unsigned long n = cn;
        switch (rnd() % 4) {
        case 0: break;                                   /* valid */
        case 1: n = rnd() % (cn + 1); break;              /* truncated */
        case 2: comp[rnd() % cn] ^= 1u << (rnd() % 8); break; /* corrupted */
        case 3: n = cn + rnd() % 16; for (unsigned long i = cn; i < n; i++) comp[i] = rnd(); break; /* trailing */
        }
        unsigned long cap = (rnd() % 3) ? pn + (rnd() % 8) - 4 : rnd() % 64;
        if ((long)cap < 0) cap = 0;
        long failAt = (rnd() % 5 == 0) ? (long)(rnd() % 3) : -1;
        one(comp, n, cap, failAt, rnd() % 2);
    }
    printf("%ld runs (ok %ld, buf %ld, data %ld, mem %ld; allocation failures %ld), %s\n", runs,
        seen[0], seen[1], seen[2], seen[3], memFailed, bad ? "VIOLATIONS" : "no violation");
    return bad;
}
