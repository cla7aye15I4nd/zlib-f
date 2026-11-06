/* Differential-test driver: compress2_z / compress2 / compress_z / compress
 * (and one uncompress2_z case) under controlled malloc failure.
 *
 * Every malloc and free of the whole program is wrapped (linker --wrap). The
 * failure oracle and the attempt counter are armed ONLY around the call into
 * zlib; all printing and buffer setup happen outside the armed interval, so
 * libc/stdio allocations are never counted and never failed.
 *
 * Allocated pointers are tracked in a fixed-size table (no dynamic allocation
 * in the tracking code); the number of live zlib allocations at return is
 * printed in each row as live=.
 *
 * The destination buffer is filled with the nonzero sentinel 0xA5 before every
 * call and its full contents are printed after, so an argument rejection that
 * preserves the initial capacity is not mistaken for bytes written.
 *
 * Rows are canonical and strict-compared by compare.py against the Lean
 * driver. The NULL-destLen calls of the uLongf wrappers compress2/compress
 * are C undefined behaviour (*destLen is read before any NULL test) and are
 * NOT executed here; the C witness for those runs separately under
 * AddressSanitizer (ubwitness.c). This file is evidence, not proof.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "zlib.h"

extern void *__real_malloc(size_t);
extern void __real_free(void *);

#define NTRACK 64
static void *track[NTRACK]; /* live zlib allocations */
static int ntrack = 0;
static long armed = -1;     /* -1: never fail; k>=0: fail exactly attempt k */
static long attempts = 0;   /* malloc attempts inside the armed interval */
static int incall = 0;      /* 1 only between arm() and disarm() */

static void arm(long fail_at) {
    if (ntrack != 0) abort();
    armed = fail_at;
    attempts = 0;
    ntrack = 0;
    incall = 1;
}

static long disarm(void) {
    incall = 0;
    return attempts;
}

void *__wrap_malloc(size_t n) {
    if (!incall)
        return __real_malloc(n);
    long idx = attempts++;
    if (armed >= 0 && idx == armed)
        return NULL; /* counted attempt, failed */
    void *p = __real_malloc(n);
    if (p != NULL) {
        if (ntrack == NTRACK) abort();
        track[ntrack++] = p;
    }
    return p;
}

void __wrap_free(void *p) {
    if (incall && p != NULL) {
        for (int i = 0; i < ntrack; i++) {
            if (track[i] == p) {
                track[i] = track[ntrack - 1];
                ntrack--;
                break;
            }
        }
    }
    __real_free(p);
}

#define CAP 64
#define UCAP 256
static unsigned char destbuf[CAP];
static unsigned char ucbuf[UCAP];
static const unsigned char sent = 0xA5;

static void hexout(const unsigned char *b, size_t n) {
    for (size_t i = 0; i < n; i++)
        printf("%02x", b[i]);
}

enum fn_id { F_C2Z, F_C2, F_CZ, F_COMPRESS };

static const char *fn_name(int fn) {
    switch (fn) {
    case F_C2Z: return "compress2_z";
    case F_C2: return "compress2";
    case F_CZ: return "compress_z";
    default: return "compress";
    }
}

static int takes_level(int fn) { return fn == F_C2Z || fn == F_C2; }

/* One comparison row. fail < 0 means "no failure". */
static void row(const char *casename, int fn, long fail, int destnull,
                unsigned long long cap, const unsigned char *src,
                size_t srclen, int srcnull, int level, int nulllen) {
    z_size_t zdl = (z_size_t)cap;
    uLongf udl = (uLongf)cap;
    int rc = -99;
    long allocs;
    int live;
    unsigned char *d = destnull ? NULL : destbuf;
    const unsigned char *s = srcnull ? NULL : src;

    memset(destbuf, sent, CAP);
    arm(fail);
    switch (fn) {
    case F_C2Z:
        rc = nulllen ? compress2_z(d, NULL, s, srclen, level)
                     : compress2_z(d, &zdl, s, srclen, level);
        break;
    case F_C2:
        rc = compress2(d, &udl, s, srclen, level);
        break;
    case F_CZ:
        rc = nulllen ? compress_z(d, NULL, s, srclen)
                     : compress_z(d, &zdl, s, srclen);
        break;
    default:
        rc = compress(d, &udl, s, srclen);
        break;
    }
    allocs = disarm();
    live = ntrack;
    printf("ROW case=%s fn=%s fail=", casename, fn_name(fn));
    if (fail < 0)
        printf("none");
    else
        printf("%ld", fail);
    printf(" rc=%d destLen=", rc);
    if (nulllen)
        printf("none");
    else
        printf("%llu", (unsigned long long)((fn == F_C2Z || fn == F_CZ) ? zdl : udl));
    printf(" out=");
    hexout(destbuf, CAP);
    printf(" live=%d allocs=%ld\n", live, allocs);
    fflush(stdout);
}

static const long sweep[] = {-1, 0, 1, 2, 3, 4, 5, 6};
#define NSWEEP 8

int main(void) {
    static const unsigned char one[1] = {'a'};
    static const unsigned char five[5] = {0x78, 0x9c, 0x73, 0x04, 0x00};

    for (int fn = F_C2Z; fn <= F_COMPRESS; fn++) {
        int level = fn == F_C2Z || fn == F_C2 ? 6 : Z_DEFAULT_COMPRESSION;
        for (int i = 0; i < NSWEEP; i++) /* normal calls */
            row("normal", fn, sweep[i], 0, 64, one, 1, 0, level, 0);
        for (int i = 0; i < NSWEEP; i++) /* empty input */
            row("empty", fn, sweep[i], 0, 64, one, 0, 0, level, 0);
        row("nullsrc", fn, -1, 0, 64, one, 1, 1, level, 0);
        row("nulldest_pos", fn, -1, 1, 64, one, 1, 0, level, 0);
        for (int i = 0; i < NSWEEP; i++) /* zero-capacity null destination */
            row("nulldest_zero", fn, sweep[i], 1, 0, one, 1, 0, level, 0);
        if (takes_level(fn)) /* invalid level for the level-taking entries */
            row("badlevel", fn, -1, 0, 64, one, 1, 0, 99, 0);
        if (fn == F_C2Z || fn == F_CZ) /* NULL destLen: defined for _z entries */
            row("nulllen", fn, -1, 0, 64, one, 1, 0, level, 1);
        else /* compress2/compress read *destLen first: C UB, not executed */
            printf("# UB skipped: case=nulllen fn=%s\n", fn_name(fn));
    }

    /* Specification-review evidence: uncompress2_z on the 5-byte prefix
     * [78 9c 73 04 00] of zlib('A'), capacity 256, malloc failure at
     * attempt index 1 (state allocation succeeds, window allocation fails). */
    {
        z_size_t dl = 256, sl = 5;
        int rc;
        long allocs;
        memset(ucbuf, sent, UCAP);
        arm(1);
        rc = uncompress2_z(ucbuf, &dl, five, &sl);
        allocs = disarm();
        printf("UNCROW case=prefix5 fail=1 rc=%d destLen=%llu sourceLen=%llu out=",
               rc, (unsigned long long)dl, (unsigned long long)sl);
        hexout(ucbuf, UCAP);
        printf(" live=%d allocs=%ld\n", ntrack, allocs);
    }
    return 0;
}
