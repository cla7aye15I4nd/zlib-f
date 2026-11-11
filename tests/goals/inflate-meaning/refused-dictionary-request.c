/* A zlib stream with a preset dictionary: the first call returns Z_NEED_DICT
 * and the decoder waits in DICT. A further call with next_out == NULL is
 * refused with Z_STREAM_ERROR and changes nothing: the decoder still waits for
 * the dictionary, and the next accepted call returns Z_NEED_DICT again. The
 * protocol token after the refused call is false (its return code is not
 * Z_NEED_DICT), so "the token is set exactly when the decoder waits for a
 * dictionary" (the request clause of ParseMeaning, as an equivalence) is
 * false; the clause holds as an implication from the token to the wait.
 * Build against tests/build-zlib.sh. */
#include <stdio.h>
#include <string.h>
#include "zlib.h"

int main(void) {
    unsigned char dict[] = "hello", src[] = "hello hello hello", comp[64], out[64];
    z_stream d;
    memset(&d, 0, sizeof d);
    if (deflateInit(&d, Z_DEFAULT_COMPRESSION) != Z_OK) return 2;
    if (deflateSetDictionary(&d, dict, sizeof dict - 1) != Z_OK) return 2;
    d.next_in = src; d.avail_in = sizeof src; d.next_out = comp; d.avail_out = sizeof comp;
    if (deflate(&d, Z_FINISH) != Z_STREAM_END) return 2;
    uInt n = sizeof comp - d.avail_out;
    deflateEnd(&d);
    z_stream s;
    memset(&s, 0, sizeof s);
    if (inflateInit(&s) != Z_OK) return 2;
    s.next_in = comp; s.avail_in = n; s.next_out = out; s.avail_out = sizeof out;
    int rc1 = inflate(&s, Z_NO_FLUSH);
    s.next_out = Z_NULL; s.avail_out = 0;
    int rc2 = inflate(&s, Z_NO_FLUSH);
    s.next_out = out; s.avail_out = sizeof out;
    int rc3 = inflate(&s, Z_NO_FLUSH);
    printf("rc %d, refused rc %d, then rc %d\n", rc1, rc2, rc3);
    inflateEnd(&s);
    return !(rc1 == Z_NEED_DICT && rc2 == Z_STREAM_ERROR && rc3 == Z_NEED_DICT);
}
