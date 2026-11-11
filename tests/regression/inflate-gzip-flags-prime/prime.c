#include <stdio.h>
#include <string.h>
#include "zlib.h"
#include "zutil.h"
#include "inftrees.h"
#include "inflate.h"
/* After the gzip magic, inflate is in FLAGS with no bits held. Two
   inflatePrime calls supply 32 bits; FLAGS stores (int)hold. */
static int run(unsigned lo, unsigned hi) {
    unsigned char in[] = {0x1f, 0x8b};
    unsigned char rest[] = {0, 0, 0, 0, 0, 3, /* MTIME XFL OS */
                            1, 0, 0, 0xff, 0xff, 0, 0, 0, 0, 0, 0, 0, 0};
    unsigned char out[16];
    z_stream s; memset(&s, 0, sizeof s);
    inflateInit2(&s, 31);
    s.next_in = in; s.avail_in = 2; s.next_out = out; s.avail_out = sizeof out;
    int r1 = inflate(&s, Z_NO_FLUSH);
    struct inflate_state *st = (struct inflate_state *)s.state;
    printf("after magic: ret %d mode %d bits %u\n", r1, st->mode, st->bits);
    inflatePrime(&s, 16, (int)lo);
    inflatePrime(&s, 16, (int)hi);
    s.next_in = rest; s.avail_in = sizeof rest;
    int r2 = inflate(&s, Z_NO_FLUSH);
    printf("hold %08x%04x: ret %d mode %d flags %d (0x%x)\n", hi, lo, r2, st->mode, st->flags, st->flags);
    inflateEnd(&s);
    return 0;
}
int main(void) {
    run(0x0008, 0x0001);   /* flags 65544 */
    run(0x0008, 0x8000);   /* flags negative */
    return 0;
}
