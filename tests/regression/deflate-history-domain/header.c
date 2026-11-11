/* A gzip header with a 2000-byte extra field and memLevel 1 (a 512-byte pending
   buffer): the first deflate call stops inside the extra field (EXTRA_STATE, 500 bytes written).
   Then mode 1: deflateSetHeader(strm, NULL); mode 2: the caller shrinks extra_len to 10.
   The next deflate call dereferences NULL (mode 1) or reads past the extra buffer (mode 2). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <zlib.h>
int main(int argc, char **argv) {
    int mode = atoi(argv[1]);
    static unsigned char out[100000];
    unsigned char *extra = malloc(2000); memset(extra, 'x', 2000);
    gz_header g; memset(&g, 0, sizeof g); g.extra = extra; g.extra_len = 2000;
    z_stream z; memset(&z, 0, sizeof z);
    deflateInit2(&z, 6, Z_DEFLATED, 31, 1, Z_DEFAULT_STRATEGY);
    deflateSetHeader(&z, &g);
    z.next_in = (unsigned char *)"hello"; z.avail_in = 5; z.next_out = out; z.avail_out = 10;
    int rc = deflate(&z, Z_NO_FLUSH);
    printf("first call rc=%d avail_out=%u\n", rc, z.avail_out);
    if (mode == 1) deflateSetHeader(&z, Z_NULL); else g.extra_len = 10;
    z.avail_out = sizeof out - 10;
    fflush(stdout);
    rc = deflate(&z, Z_FINISH);
    printf("second call rc=%d\n", rc);
    deflateEnd(&z); free(extra);
    return 0;
}
