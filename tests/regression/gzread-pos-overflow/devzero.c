/* gzread: signed overflow of x.pos after a transparent seek on an endless device.
   gzdopen(/dev/zero, "r"); gzread 1 byte (not gzip: transparent copy); gzseek to
   INT64_MAX; gzread 16 bytes. On Linux, lseek on /dev/zero returns 0 and does not
   fail, so gzseek accepts the target and sets x.pos to INT64_MAX. Without the fix,
   gz_read then adds 16 to x.pos (gzread.c, state->x.pos += n). With the argument
   "near", the seek goes to INT64_MAX - 4 instead, and the bytes are taken with
   gzread, the gzgetc() macro and gzgets: the buffered output must never carry
   the position past INT64_MAX. */
#include <string.h>
#include <stdio.h>
#include <stdint.h>
#include <fcntl.h>
#include <unistd.h>
#include "zlib.h"

int main(int argc, char **argv) {
    const char *dev = "/dev/zero";
    int near = argc > 1 && strcmp(argv[1], "near") == 0;
    int i;
    char buf[16];
    int fd, n, err;
    const char *msg;
    gzFile f;

    setvbuf(stdout, NULL, _IONBF, 0);
    fd = open(dev, O_RDONLY);
    if (fd < 0) {
        perror("open");
        return 2;
    }
    printf("lseek(fd, INT64_MAX - 1, SEEK_CUR) = %lld\n",
           (long long)lseek(fd, INT64_MAX - 1, SEEK_CUR));
    lseek(fd, 0, SEEK_SET);
    f = gzdopen(fd, "r");
    if (f == NULL)
        return 2;
    n = gzread(f, buf, 1);
    printf("gzread 1 = %d, gzdirect = %d\n", n, gzdirect(f));
    if (near) {
        printf("gzseek INT64_MAX - 4 = %lld\n",
               (long long)gzseek(f, INT64_MAX - 4, SEEK_SET));
        n = gzread(f, buf, 1);
        printf("gzread 1 = %d, gztell = %lld\n", n, (long long)gztell(f));
        for (i = 0; i < 4; i++) {
            n = gzgetc(f);
            printf("gzgetc = %d, gztell = %lld\n", n, (long long)gztell(f));
        }
        printf("gzgets = %s\n", gzgets(f, buf, sizeof buf) == NULL ? "NULL" : "text");
        msg = gzerror(f, &err);
        printf("err = %d (%s), gztell = %lld\n", err, msg, (long long)gztell(f));
        gzclose(f);
        return 0;
    }
    printf("gzseek INT64_MAX = %lld\n", (long long)gzseek(f, INT64_MAX, SEEK_SET));
    n = gzread(f, buf, sizeof buf);
    msg = gzerror(f, &err);
    printf("gzread 16 = %d, err = %d (%s), gztell = %lld\n", n, err, msg,
           (long long)gztell(f));
    n = gzgetc(f);
    printf("gzgetc = %d, gztell = %lld\n", n, (long long)gztell(f));
    gzclose(f);
    return 0;
}
