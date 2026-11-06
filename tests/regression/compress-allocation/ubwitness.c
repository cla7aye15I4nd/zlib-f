/* Isolated C witness for the undefined behaviour of the uLongf wrappers:
 * compress2 and compress read *destLen before any NULL test, so a NULL
 * destLen is C undefined behaviour (a read through a null pointer).
 *
 * Run only under AddressSanitizer/UBSan. Not part of the defined-behaviour
 * comparison matrix. Usage: ubwitness [compress2|compress]
 */
#include <stdio.h>
#include <string.h>
#include "zlib.h"

int main(int argc, char **argv) {
    unsigned char src[1] = {'a'};
    unsigned char dst[64];
    int which = argc > 1 && strcmp(argv[1], "compress") == 0;
    memset(dst, 0xA5, sizeof dst);
    fprintf(stderr, "calling %s with destLen == NULL\n",
            which ? "compress" : "compress2");
    if (which)
        return compress(dst, NULL, src, 1);
    return compress2(dst, NULL, src, 1, 6);
}
