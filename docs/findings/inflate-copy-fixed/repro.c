#include <stdio.h>
#include <string.h>
#include "zlib.h"

/* A zlib-wrapped final fixed block representing 2048 copies of 'A'. */
static unsigned char encoded[] = {
    120, 1, 115, 116, 28, 5, 163, 96, 20, 140, 130, 81,
    48, 10, 70, 193, 72, 3, 0, 133, 239, 8, 31
};

int main(void) {
    z_stream stream, copied;
    unsigned char out[1];
    int rc;

    memset(&stream, 0, sizeof(stream));
    memset(&copied, 0, sizeof(copied));
    rc = inflateInit(&stream);
    if (rc != Z_OK)
        return 10;
    stream.next_in = encoded;
    stream.avail_in = (uInt)sizeof(encoded);
    stream.next_out = out;
    stream.avail_out = (uInt)sizeof(out);
    rc = inflate(&stream, Z_NO_FLUSH);
    fprintf(stderr, "inflate=%d produced=%lu fixed_block=%u\n",
            rc, stream.total_out, ((unsigned)encoded[2] >> 1) & 3u);
    if (rc != Z_OK || stream.total_out != 1 || out[0] != 'A')
        return 11;

    rc = inflateCopy(&copied, &stream);
    fprintf(stderr, "inflateCopy=%d\n", rc);
    if (rc == Z_OK)
        inflateEnd(&copied);
    inflateEnd(&stream);
    return rc == Z_OK ? 0 : 12;
}
