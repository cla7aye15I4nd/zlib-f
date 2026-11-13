/* deflatePrime after deflate has recorded symbols: pending grows over sym_buf. */
#include <stdio.h>
#include <string.h>
#include <zlib.h>
int main(void) {
    static unsigned char in[300], out[100000];
    for (int i = 0; i < 300; i++) in[i] = "abc"[i % 3];
    z_stream z; memset(&z, 0, sizeof z);
    int rc = deflateInit2(&z, 1, Z_DEFLATED, -15, 1, Z_DEFAULT_STRATEGY);
    z.next_in = in; z.avail_in = sizeof in; z.next_out = out; z.avail_out = sizeof out;
    rc = deflate(&z, Z_NO_FLUSH);
    printf("deflate NO_FLUSH rc=%d avail_in=%u out=%lu\n", rc, z.avail_in, z.total_out);
    int k = 0;
    for (; k < 200; k++) { rc = deflatePrime(&z, 16, 0xffff); if (rc != Z_OK) break; }
    printf("deflatePrime ok %d times, last rc=%d\n", k, rc);
    rc = deflate(&z, Z_FINISH);
    printf("deflate FINISH rc=%d out=%lu\n", rc, z.total_out);
    deflateEnd(&z);
    return 0;
}
