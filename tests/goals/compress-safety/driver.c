/* Statement test for the compressor safety goals (Goal.compress*_safety, CompressorSafety).
 * For random sources, random levels (including invalid ones), random capacities (including
 * tiny ones) and injected allocation failures, call compress2 and compress with exact-size heap
 * buffers (so AddressSanitizer catches any access outside them) and check:
 *   - the call returns (a hang is a failure of the run);
 *   - the stored length is at most the capacity;
 *   - Z_MEM_ERROR only when an allocation failed;
 *   - every allocation is freed on return (live allocation count back to 0);
 *   - bytes past the stored length are not written (dest is checked against a canary fill).
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
static long seen[5], memFailed;
static void fail(const char *what, int rc, unsigned long cap, unsigned long n, int level) {
    fprintf(stderr, "violation: %s (rc %d, cap %lu, n %lu, level %d)\n", what, rc, cap, n, level);
    bad = 1;
}

static void one(const unsigned char *src, unsigned long n, unsigned long cap, int level, long failAt, int counted) {
    unsigned char *s = __real_malloc(n ? n : 1), *d = __real_malloc(cap ? cap : 1);
    memcpy(s, src, n);
    memset(d, 0xA5, cap ? cap : 1);
    uLongf dl = cap;
    count = 0; fail_at = failAt; live = 0;
    int rc = counted ? compress2(cap ? d : NULL, &dl, n ? s : NULL, n, level)
                     : compress(cap ? d : NULL, &dl, n ? s : NULL, n);
    long failed = (failAt >= 0 && count > failAt);
    fail_at = -1;
    if (dl > cap) fail("stored length", rc, cap, n, level);
    if (rc == Z_MEM_ERROR && !failed) fail("mem without failure", rc, cap, n, level);
    if (live != 0) fail("leak", rc, cap, n, level);
    seen[rc == Z_OK ? 0 : rc == Z_BUF_ERROR ? 1 : rc == Z_STREAM_ERROR ? 2 : rc == Z_MEM_ERROR ? 3 : 4]++;
    if (failed) memFailed++;
    for (unsigned long i = dl; i < cap; i++)
        if (d[i] != 0xA5) { fail("write past stored length", rc, cap, n, level); break; }
    __real_free(s); __real_free(d);
}

int main(int argc, char **argv) {
    rng = argc > 1 ? strtoul(argv[1], 0, 10) : 1;
    long runs = argc > 2 ? strtol(argv[2], 0, 10) : 2000;
    static unsigned char plain[70000];
    for (long k = 0; k < runs; k++) {
        unsigned long n = (rnd() % 8 == 0) ? rnd() % 70000 : rnd() % 3000;
        for (unsigned long i = 0; i < n; i++) plain[i] = (rnd() % 4) ? 'a' + rnd() % 3 : rnd();
        unsigned long bound = compressBound(n);
        unsigned long cap;
        switch (rnd() % 4) {
        case 0: cap = bound; break;
        case 1: cap = rnd() % 16; break;
        case 2: cap = rnd() % (bound + 1); break;
        default: cap = n / 2 + rnd() % (n / 2 + 8); break;
        }
        int level = (int)(rnd() % 13) - 2;               /* -2 .. 10: -2 and 10 are invalid */
        long failAt = (rnd() % 5 == 0) ? (long)(rnd() % 6) : -1;
        one(plain, n, cap, level, failAt, rnd() % 2);
    }
    printf("%ld runs (ok %ld, buf %ld, stream %ld, mem %ld, other %ld; allocation failures %ld), %s\n", runs,
        seen[0], seen[1], seen[2], seen[3], seen[4], memFailed, bad ? "VIOLATIONS" : "no violation");
    return bad;
}
