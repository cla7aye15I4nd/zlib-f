/* After a call that read a whole zlib stream and returned Z_STREAM_END, a
 * further call with next_out == NULL consumes nothing and returns
 * Z_STREAM_ERROR. Its consumed input is still the whole stream, so
 * "a call whose consumed input is the whole stream returns Z_STREAM_END or
 * Z_MEM_ERROR" (ConsumesWithinStream, clause 2) is false; such a call returns
 * neither Z_OK nor Z_BUF_ERROR. Build against tests/build-zlib.sh. */
#include <stdio.h>
#include <string.h>
#include "zlib.h"

int main(void) {
    unsigned char src[] = "hello hello hello", comp[64], out[64];
    uLongf n = sizeof comp;
    if (compress(comp, &n, src, sizeof src) != Z_OK) return 2;
    z_stream s;
    memset(&s, 0, sizeof s);
    if (inflateInit(&s) != Z_OK) return 2;
    s.next_in = comp; s.avail_in = (uInt)n; s.next_out = out; s.avail_out = sizeof out;
    int rc1 = inflate(&s, Z_NO_FLUSH);
    s.next_out = Z_NULL; s.avail_out = 0;
    int rc2 = inflate(&s, Z_NO_FLUSH);
    printf("first rc %d (avail_in %u), second rc %d (avail_in %u)\n", rc1, s.avail_in, rc2, s.avail_in);
    inflateEnd(&s);
    return !(rc1 == Z_STREAM_END && s.avail_in == 0 && rc2 == Z_STREAM_ERROR);
}
