/* A caller lowers head->extra_len while inflate is inside the gzip extra
   field. EXTRA computes len = extra_len - length (unsigned, wraps) and
   checks len + copy > extra_max in 32-bit arithmetic, which wraps too:
   zmemcpy then writes one byte past extra_max. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "zlib.h"

int main(void) {
    /* gzip header with FEXTRA, XLEN = 4, extra "WXYZ", then an empty stored final block */
    unsigned char in[] = {0x1f, 0x8b, 8, 4, 0, 0, 0, 0, 0, 3, 4, 0,
                          'W', 'X', 'Y', 'Z',
                          1, 0, 0, 0xff, 0xff, 0, 0, 0, 0, 0, 0, 0, 0};
    unsigned char out[16];
    unsigned max = 0xffffffffu;               /* extra_max = 2^32 - 1 */
    unsigned char *extra = malloc(max);       /* exactly extra_max bytes */
    if (!extra) { puts("no memory"); return 1; }
    z_stream strm;
    memset(&strm, 0, sizeof strm);
    if (inflateInit2(&strm, 31) != Z_OK) return 1;
    gz_header head;
    memset(&head, 0, sizeof head);
    head.extra = extra;
    head.extra_max = max;
    inflateGetHeader(&strm, &head);
    strm.next_out = out; strm.avail_out = sizeof out;
    /* first call: the 12 header bytes up to XLEN; inflate leaves in EXTRA with length 4 */
    strm.next_in = in; strm.avail_in = 12;
    int ret = inflate(&strm, Z_NO_FLUSH);
    printf("first call %d, extra_len %u\n", ret, head.extra_len);
    head.extra_len = 0;                        /* the caller changes its record */
    /* second call: the 4 extra bytes; len = 0 - 4 wraps to 2^32 - 4 < extra_max,
       len + copy wraps to 0, so n = copy = 4: bytes [2^32-4, 2^32) of a 2^32-1 byte buffer */
    strm.avail_in = sizeof in - 12;
    ret = inflate(&strm, Z_NO_FLUSH);
    printf("second call %d\n", ret);
    inflateEnd(&strm);
    free(extra);
    return 0;
}
