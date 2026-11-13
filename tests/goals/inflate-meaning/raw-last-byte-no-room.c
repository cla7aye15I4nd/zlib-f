/* A raw deflate stream whose last byte holds the end of the last literal code
 * and the whole end-of-block code: a fixed block with six literals of 9-bit
 * codes (bytes 144..255) takes 3 + 6 * 9 + 7 = 64 bits, so the sixth literal
 * ends at bit 57 and the end-of-block code fills bits 57..63. With room for
 * five bytes, inflate pulls the last byte to decode the sixth literal, then
 * stops in LIT for want of room: all input consumed, Z_OK, not finished.
 * So "a call that reads the last byte of a valid stream returns Z_STREAM_END
 * or Z_MEM_ERROR" (ConsumesWithinStream) fails for raw data without room. A
 * zlib or gzip stream ends with a trailer that only CHECK reads, after the
 * last block. Build against the patched copy made by tests/build-zlib.sh. */
#include <stdio.h>
#include <string.h>
#include "zlib.h"

static unsigned char data[6] = {200, 201, 202, 203, 204, 205}, comp[64], out[16];

int main(void) {
    z_stream d;
    memset(&d, 0, sizeof d);
    if (deflateInit2(&d, 9, Z_DEFLATED, -15, 8, Z_FIXED) != Z_OK) return 2;
    d.next_in = data; d.avail_in = sizeof data; d.next_out = comp; d.avail_out = sizeof comp;
    if (deflate(&d, Z_FINISH) != Z_STREAM_END) return 2;
    unsigned n = (unsigned)d.total_out;
    deflateEnd(&d);
    printf("stream %u bytes:", n);
    for (unsigned i = 0; i < n; i++) printf(" %02x", comp[i]);
    printf("\n");
    z_stream s;
    memset(&s, 0, sizeof s);
    if (inflateInit2(&s, -15) != Z_OK) return 2;
    s.next_in = comp; s.avail_in = n; s.next_out = out; s.avail_out = 5;
    int rc = inflate(&s, Z_NO_FLUSH);
    printf("room 5: rc %d, used %u of %u, written %u\n", rc, n - s.avail_in, n, 5 - s.avail_out);
    int consumed_all = s.avail_in == 0;
    s.avail_out = sizeof out - 5;
    int rc2 = inflate(&s, Z_NO_FLUSH);
    printf("then: rc %d, written %lu\n", rc2, s.total_out);
    inflateEnd(&s);
    return !(n == 8 && rc == Z_OK && consumed_all && rc2 == Z_STREAM_END && s.total_out == 6);
}
