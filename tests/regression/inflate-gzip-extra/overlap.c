/* inflate with a gz_header whose extra buffer overlaps the unread input.
   EXTRA copies the extra field with zmemcpy(head->extra + len, next, n);
   the source and destination overlap, which memcpy does not allow. */
#include <stdio.h>
#include <string.h>
#include "zlib.h"

int main(void) {
    unsigned char in[64];
    unsigned char out[64];
    /* gzip header: ID1 ID2 CM FLG(FEXTRA) MTIME(4) XFL OS XLEN(2) extra(8) */
    unsigned char hdr[] = {0x1f, 0x8b, 8, 4, 0, 0, 0, 0, 0, 3, 8, 0,
                           'a', 'b', 'c', 'd', 'e', 'f', 'g', 'h'};
    /* empty stored final block, CRC32 0, ISIZE 0 */
    unsigned char tail[] = {1, 0, 0, 0xff, 0xff, 0, 0, 0, 0, 0, 0, 0, 0};
    size_t n = 0;
    memcpy(in, hdr, sizeof hdr); n += sizeof hdr;
    memcpy(in + n, tail, sizeof tail); n += sizeof tail;

    z_stream strm;
    memset(&strm, 0, sizeof strm);
    if (inflateInit2(&strm, 31) != Z_OK) return 1;
    gz_header head;
    memset(&head, 0, sizeof head);
    head.extra = in + 14;          /* overlaps the extra field at in + 12 .. in + 20 */
    head.extra_max = 8;
    if (inflateGetHeader(&strm, &head) != Z_OK) return 1;
    strm.next_in = in;
    strm.avail_in = (uInt)n;
    strm.next_out = out;
    strm.avail_out = sizeof out;
    int ret = inflate(&strm, Z_FINISH);
    printf("inflate returned %d, done %d\n", ret, head.done);
    inflateEnd(&strm);
    return 0;
}
