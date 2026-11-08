/* A complete raw DEFLATE stream, decoded through a reusable five-byte buffer.
 * Build with: cc inflate-chunks.c -lz -o inflate-chunks
 */
#include <stdio.h>
#include <stdlib.h>
#include <zlib.h>

int main(void) {
    unsigned char compressed[] = {0x73, 0x74, 0x82, 0x40, 0x00};
    unsigned char output[5];
    z_stream stream = {0};
    unsigned call = 0;

    /* Raw DEFLATE: these five bytes have no zlib or gzip wrapper. */
    if (inflateInit2(&stream, -MAX_WBITS) != Z_OK)
        return EXIT_FAILURE;
    stream.next_in = compressed;
    stream.avail_in = sizeof compressed;

    for (;;) {
        unsigned input_before = stream.avail_in;
        /* BEGIN call */
        stream.next_out = output;             /* writable destination */
        stream.avail_out = sizeof output;     /* five bytes of room */

        int result = inflate(&stream, Z_NO_FLUSH);
        unsigned produced = sizeof output - stream.avail_out;
        /* END call */

        printf("call %u: input=%u, output=%u, bytes=", ++call,
               input_before - stream.avail_in, produced);
        fwrite(output, 1, produced, stdout);
        printf(", result=%s\n", result == Z_STREAM_END ? "Z_STREAM_END" :
               result == Z_OK ? "Z_OK" : "error");

        if (result == Z_STREAM_END)
            break;
        /* All input was supplied up front in this example. An error or no
         * progress therefore cannot be fixed by retrying the same call. */
        if (result != Z_OK ||
            (input_before == stream.avail_in && produced == 0)) {
            inflateEnd(&stream);
            return EXIT_FAILURE;
        }
        /* The next iteration reuses output, but keeps the SAME stream. */
    }

    return inflateEnd(&stream) == Z_OK ? EXIT_SUCCESS : EXIT_FAILURE;
}
