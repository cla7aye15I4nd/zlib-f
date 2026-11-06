/* C side of the inflatePrime boundary regression (tests/regression/inflate-prime).
 * Links the REAL patched zlib. Every case creates a stream with inflateInit2_(-15),
 * calls the real inflatePrime, reads hold/bits out of the real struct inflate_state,
 * prints one line per call, and ends the stream. Output must match the Lean driver
 * byte for byte (run.sh compares with cmp). Exit status 0, or 1 if a state read fails. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <limits.h>
#include "zutil.h"
#include "inftrees.h"
#include "inflate.h"

_Static_assert(sizeof(int) == 4 && sizeof(unsigned) == 4 &&
               sizeof(unsigned long) == 8 && sizeof(z_stream) == 112,
               "default LP64 target required");

static struct inflate_state *st(z_streamp s) {
    return (struct inflate_state *)s->state;   /* same cast inflate.c uses internally */
}

/* One fresh-stream case: init, prime(bits, value), print, end. */
static void fresh(int bits, int value) {
    z_stream s;
    memset(&s, 0, sizeof(s));
    s.zalloc = zcalloc;
    s.zfree = zcfree;
    s.opaque = Z_NULL;
    int rc = inflateInit2_(&s, -15, ZLIB_VERSION, (int)sizeof(z_stream));
    if (rc != Z_OK) { fprintf(stderr, "inflatePrime test init failed: %d\n", rc); exit(2); }
    printf("fresh b=%d v=%d rc=%d hold=%lu bits=%u\n",
           bits, value, rc, (unsigned long)st(&s)->hold, st(&s)->bits);
    rc = inflatePrime(&s, bits, value);
    printf("prime b=%d v=%d rc=%d hold=%lu bits=%u\n",
           bits, value, rc, (unsigned long)st(&s)->hold, st(&s)->bits);
    if (inflateEnd(&s) != Z_OK) { fprintf(stderr, "inflatePrime test end failed\n"); exit(1); }
}

/* The append sequence on one stream. */
static void seq(void) {
    static const int bs[] = {16, 16, 1, 0, -1};
    static const int vs[] = {-1, -1, 0, 5, 7};
    z_stream s;
    memset(&s, 0, sizeof(s));
    s.zalloc = zcalloc;
    s.zfree = zcfree;
    s.opaque = Z_NULL;
    int rc = inflateInit2_(&s, -15, ZLIB_VERSION, (int)sizeof(z_stream));
    if (rc != Z_OK) { fprintf(stderr, "inflatePrime test init failed: %d\n", rc); exit(2); }
    printf("seq init rc=%d hold=%lu bits=%u\n", rc, (unsigned long)st(&s)->hold, st(&s)->bits);
    for (int i = 0; i < 5; i++) {
        rc = inflatePrime(&s, bs[i], vs[i]);
        printf("seq step=%d call=prime(%d,%d) rc=%d hold=%lu bits=%u\n",
               i, bs[i], vs[i], rc, (unsigned long)st(&s)->hold, st(&s)->bits);
    }
    if (inflateEnd(&s) != Z_OK) { fprintf(stderr, "inflatePrime test end failed\n"); exit(1); }
}

int main(void) {
    static const int bitv[] = {-2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17};
    static const int valv[] = {INT_MIN, -65537, -2, -1, 0, 1, 65535, 65536, INT_MAX};
    for (unsigned b = 0; b < sizeof(bitv) / sizeof(bitv[0]); b++)
        for (unsigned v = 0; v < sizeof(valv) / sizeof(valv[0]); v++)
            fresh(bitv[b], valv[v]);
    seq();
    return 0;
}
