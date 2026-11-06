/* A raw fixed block: literal A, length 3, distance 2, end-of-block.
 * There is only one history byte. The first call has exactly one output byte.
 * Compare actual consumption and deferred error detection with distance.lean. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "zutil.h"
#include "inftrees.h"
#include "inflate.h"

_Static_assert(sizeof(int) == 4 && sizeof(unsigned long) == 8 && sizeof(z_stream) == 112,
               "default LP64 target required");

static void hex(const unsigned char *p, size_t n) {
    for (size_t i = 0; i < n; ++i) printf("%02x", p[i]);
}

static void observe(const char *tag, int rc, z_stream *z, unsigned char *src,
                    size_t nsrc, unsigned char *dst, size_t ndst) {
    struct inflate_state *s = (struct inflate_state *)z->state;
    size_t used = (size_t)(z->next_in - src), produced = (size_t)(z->next_out - dst);
    if (used > nsrc || produced > ndst) exit(2);
    printf("%s rc=%d used=%zu produced=%zu avail_in=%u avail_out=%u total_in=%lu total_out=%lu hold=%lu bits=%u mode=%u length=%u offset=%u whave=%u msgnull=%d prefix=",
           tag, rc, used, produced, z->avail_in, z->avail_out, z->total_in, z->total_out,
           s->hold, s->bits, (unsigned)s->mode, s->length, s->offset, s->whave, z->msg == NULL);
    hex(src, used); printf(" output="); hex(dst, produced);
    printf(" buffer="); hex(dst, ndst); printf("\n");
}

int main(void) {
    unsigned char src[] = {0x73, 0x04, 0x42, 0x00}, dst[16];
    memset(dst, 0xa5, sizeof(dst));
    z_stream z = {0};
    int rc = inflateInit2(&z, -15);
    if (rc != Z_OK) { fprintf(stderr, "distance test init failed: %d\n", rc); return 2; }
    z.next_in = src; z.avail_in = sizeof(src);
    z.next_out = dst; z.avail_out = 1;
    rc = inflate(&z, Z_NO_FLUSH);
    observe("first", rc, &z, src, sizeof(src), dst, sizeof(dst));
    z.avail_out = 8;
    rc = inflate(&z, Z_NO_FLUSH);
    observe("second", rc, &z, src, sizeof(src), dst, sizeof(dst));
    int ended = inflateEnd(&z);
    printf("end rc=%d state_null=%d\n", ended, z.state == NULL);
    return ended != Z_OK || z.state != NULL;
}
