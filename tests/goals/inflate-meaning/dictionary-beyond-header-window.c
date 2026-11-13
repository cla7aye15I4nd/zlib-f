/* A zlib stream whose header announces a 256-byte window (CINFO = 0) and asks
 * for a 1000-byte preset dictionary, with a match at distance 500 into the
 * dictionary. inflate configured with windowBits 15 keeps the whole dictionary
 * and accepts the stream (Z_STREAM_END, the 20 matched bytes). The RFC 1950
 * format (Zlib.Decodes) keeps only the last window-size bytes of the
 * dictionary, so the stream has no valid decoding: inflate with windowBits 8
 * (window 256) rejects it with "invalid distance too far back".
 * So after an admitted history with this dictionary the delivered output has
 * no evidence in Api.Layer.Decodes, and TraceEvidence needs a premise that
 * excludes a zlib dictionary used with a window larger than the header's.
 * Build against the patched copy made by tests/build-zlib.sh. */
#include <stdio.h>
#include <string.h>
#include "zlib.h"

static unsigned char dict[1000], data[20], comp[256], out[64];

static int decode(int wbits, unsigned long n, const char **msg, unsigned long *got) {
    z_stream s;
    memset(&s, 0, sizeof s);
    if (inflateInit2(&s, wbits) != Z_OK) return -100;
    s.next_in = comp; s.avail_in = (uInt)n; s.next_out = out; s.avail_out = sizeof out;
    int rc = inflate(&s, Z_NO_FLUSH);
    if (rc == Z_NEED_DICT) {
        if (inflateSetDictionary(&s, dict, sizeof dict) != Z_OK) return -101;
        rc = inflate(&s, Z_NO_FLUSH);
    }
    *msg = s.msg ? s.msg : "";
    *got = sizeof out - s.avail_out;
    inflateEnd(&s);
    return rc;
}

int main(void) {
    unsigned x = 12345;
    for (int i = 0; i < 1000; i++) { x = x * 1103515245u + 12345u; dict[i] = (unsigned char)(x >> 16); }
    memcpy(data, dict + 500, sizeof data);           /* distance 500 from the end of the dictionary */
    z_stream d;
    memset(&d, 0, sizeof d);
    if (deflateInit2(&d, 9, Z_DEFLATED, 15, 8, Z_DEFAULT_STRATEGY) != Z_OK) return 2;
    if (deflateSetDictionary(&d, dict, sizeof dict) != Z_OK) return 2;
    d.next_in = data; d.avail_in = sizeof data; d.next_out = comp; d.avail_out = sizeof comp;
    if (deflate(&d, Z_FINISH) != Z_STREAM_END) return 2;
    unsigned long n = d.total_out;
    deflateEnd(&d);
    /* Announce a 256-byte window: CMF = 0x08, keep FDICT and FLEVEL, fix FCHECK. */
    unsigned flg = comp[1] & 0xe0;
    comp[0] = 0x08;
    comp[1] = (unsigned char)(flg + (31 - (0x08 * 256 + flg) % 31) % 31);
    if ((comp[0] * 256 + comp[1]) % 31 != 0 || !(comp[1] & 0x20)) return 2;
    const char *msg15, *msg8;
    unsigned long got15, got8;
    int rc15 = decode(15, n, &msg15, &got15);
    int rc8 = decode(8, n, &msg8, &got8);
    printf("stream %lu bytes:", n);
    for (unsigned long i = 0; i < n; i++) printf(" %02x", comp[i]);
    printf("\n");
    printf("windowBits 15: rc %d, %lu bytes, equal %d, msg \"%s\"\n", rc15, got15,
           got15 == sizeof data && memcmp(out, data, sizeof data) == 0, msg15);
    printf("windowBits 8: rc %d, msg \"%s\"\n", rc8, msg8);
    return !(rc15 == Z_STREAM_END && got15 == sizeof data && rc8 == Z_DATA_ERROR);
}
