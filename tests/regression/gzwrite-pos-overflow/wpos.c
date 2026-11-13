/* gzwrite: signed overflow of x.pos on a transparent writer.
   gzdopen(/dev/null, "wT"); gzbuffer 2^29; gzseek to INT64_MAX - 10; gzwrite 100 bytes.
   gzwrite first writes the INT64_MAX - 10 zeros of the pending seek (2^34 writes of
   2^29 bytes to /dev/null), then copies the 100 bytes. Without the fix, the copy adds
   100 to x.pos (gzwrite.c, state->x.pos += copy). With the argument "putc", one byte
   is written with gzputc at INT64_MAX instead (seek to INT64_MAX). */
#include <stdio.h>
#include <stdint.h>
#include <string.h>
#include <fcntl.h>
#include <unistd.h>
#include "zlib.h"

int null_fd = -1;

int main(int argc, char **argv) {
    int putc_mode = argc > 1 && strcmp(argv[1], "putc") == 0;
    char buf[100];
    const char *msg;
    int r, err;
    gzFile f;

    setvbuf(stdout, NULL, _IONBF, 0);
    null_fd = open("/dev/null", O_WRONLY);
    if (null_fd < 0) {
        perror("open");
        return 2;
    }
    f = gzdopen(null_fd, "wT");
    if (f == NULL)
        return 2;
    printf("gzbuffer 2^29 = %d\n", gzbuffer(f, 1u << 29));
    if (putc_mode) {
        printf("gzseek INT64_MAX = %lld\n", (long long)gzseek(f, INT64_MAX, SEEK_SET));
        r = gzputc(f, 'a');
        printf("gzputc = %d", r);
    }
    else {
        printf("gzseek INT64_MAX - 10 = %lld\n",
               (long long)gzseek(f, INT64_MAX - 10, SEEK_SET));
        memset(buf, 'a', sizeof buf);
        r = gzwrite(f, buf, sizeof buf);
        printf("gzwrite 100 = %d", r);
    }
    msg = gzerror(f, &err);
    printf(", err = %d (%s), gztell = %lld\n", err, msg, (long long)gztell(f));
    fflush(stdout);
    gzclose(f);
    return 0;
}
