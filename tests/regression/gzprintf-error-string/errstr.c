/* gzprintf with the handle's own error message as a %s argument, after a stalled write.
   gzvprintf calls gz_error(state, Z_OK, NULL), which frees state->msg, and then vsnprintf
   reads the argument. */
#include <stdio.h>
#include <string.h>
#include <fcntl.h>
#include <unistd.h>
#include "zlib.h"

int main(void) {
    int p[2];
    if (pipe(p)) return 2;
    fcntl(p[1], F_SETFL, O_NONBLOCK);
    static char fill[65536];
    memset(fill, 'a', sizeof fill);
    while (write(p[1], fill, sizeof fill) > 0) ;      /* the pipe is full: write() fails with EAGAIN */
    gzFile f = gzdopen(p[1], "wT");
    static char big[100000];
    memset(big, 'b', sizeof big);
    int n = gzwrite(f, big, sizeof big);              /* stalls: again = 1, err = Z_ERRNO, msg set */
    int e;
    const char *m = gzerror(f, &e);                   /* the handle's own message */
    printf("gzwrite -> %d, err %d, msg \"%s\"\n", n, e, m);
    int r = gzprintf(f, "%s", m);
    printf("gzprintf -> %d\n", r);
    return 0;
}
