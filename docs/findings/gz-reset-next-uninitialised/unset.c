/* R-3: gz_reset() never writes state->x.next, and the gz_state record comes from
   malloc(). On a fresh reader of a gzip file, gzseek (not in COPY mode) and gzdirect
   evaluate "state->x.next += n" with n == 0 before any assignment of x.next: the value
   used is the indeterminate content of the allocation. The probe of probe.h shows each
   such evaluation. Under AddressSanitizer, fresh allocations are filled with 0xbe, so the
   value printed is 0xbebebebebebebebe. */
#include <stdio.h>
#include <string.h>
#include "zlib.h"

static int events = 0;

unsigned zprobe_next(const unsigned char *next, unsigned n, const char *file, int line) {
    const char *base = strrchr(file, '/');
    if (n == 0) {
        events++;
        printf("x.next + 0 at %s:%d, x.next = %p\n", base ? base + 1 : file, line,
               (const void *)next);
    }
    return n;
}

int main(void) {
    char buf[16];
    gzFile f;
    int n;

    f = gzopen("unset.gz", "wb");
    if (f == NULL || gzputs(f, "hello, hello!\n") < 0 || gzclose(f) != Z_OK)
        return 2;

    printf("-- gzopen, gzseek(f, 3, SEEK_SET)\n");
    f = gzopen("unset.gz", "rb");
    if (f == NULL)
        return 2;
    printf("gzseek = %ld\n", (long)gzseek(f, 3, SEEK_SET));
    n = gzread(f, buf, 5);
    printf("gzread 5 = %d \"%.*s\"\n", n, n > 0 ? n : 0, buf);
    gzclose(f);

    printf("-- gzopen, gzdirect\n");
    f = gzopen("unset.gz", "rb");
    if (f == NULL)
        return 2;
    printf("gzdirect = %d\n", gzdirect(f));
    gzclose(f);

    printf("evaluations of x.next with n == 0: %d\n", events);
    return 0;
}
