/* R-4: a large gzread decompresses directly into the caller's buffer, and gz_decomp()
   leaves state->x.next pointing into that buffer (with x.have set to 0). The caller then
   frees its buffer, as it may. A later gzdirect (after the end of the gzip member) or
   gzseek (not in COPY mode) evaluates "state->x.next += n" with n == 0: pointer
   arithmetic on a pointer to an object whose lifetime has ended. The probe of
   ../gz-reset-next-uninitialised/probe.h shows each such evaluation, and whether the
   value points into the freed buffer. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include "zlib.h"

#define LEN 100000

static uintptr_t lo, hi;
static int events = 0;

unsigned zprobe_next(const unsigned char *next, unsigned n, const char *file, int line) {
    const char *base = strrchr(file, '/');
    if (n == 0) {
        uintptr_t v = (uintptr_t)next;
        events++;
        printf("x.next + 0 at %s:%d, x.next = %s\n", base ? base + 1 : file, line,
               lo && v >= lo && v <= hi ? "inside the freed caller buffer" : "elsewhere");
    }
    return n;
}

/* open the file, read all of it with one large gzread into a malloc'd buffer, free it */
static gzFile read_all_then_free(void) {
    gzFile f = gzopen("dangling.gz", "rb");
    unsigned char *buf = malloc(LEN);
    int n;
    if (f == NULL || buf == NULL)
        exit(2);
    n = gzread(f, buf, LEN);
    printf("gzread %d = %d\n", LEN, n);
    lo = (uintptr_t)buf;
    hi = (uintptr_t)buf + LEN;
    free(buf);
    return f;
}

int main(void) {
    static unsigned char data[LEN];
    gzFile f;
    int i;

    for (i = 0; i < LEN; i++)
        data[i] = (unsigned char)("abcdefgh\n"[i % 9]);
    f = gzopen("dangling.gz", "wb");
    if (f == NULL || gzwrite(f, data, LEN) != LEN || gzclose(f) != Z_OK)
        return 2;

    printf("-- large gzread, free the buffer, gzdirect\n");
    f = read_all_then_free();
    printf("gzdirect = %d\n", gzdirect(f));
    gzclose(f);

    printf("-- large gzread, free the buffer, gzseek(f, 1, SEEK_CUR)\n");
    f = read_all_then_free();
    printf("gzseek = %ld\n", (long)gzseek(f, 1, SEEK_CUR));
    gzclose(f);

    printf("evaluations of x.next with n == 0: %d\n", events);
    return 0;
}
