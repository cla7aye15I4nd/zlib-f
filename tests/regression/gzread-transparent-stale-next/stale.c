/* A transparent (COPY) read whose read() returns some bytes and then fails: gzread copies from a
   stale state->x.next.

   gzbuffer(f, 16) makes the output buffer 32 bytes. 48 gzgetc calls on a 128-byte raw file
   consume the first two 32-byte loads exactly: x.have is 0 and x.next is out + 32, one past the
   buffer. Then read() is replaced by one that returns one byte and then fails with EIO. In
   gz_fetch's COPY case, gz_load stores x.have = 1 and returns -1, so gz_fetch returns before it
   sets x.next = out. gz_read sees x.have != 0 and copies one byte from out + 32: a heap read past
   the output buffer. With the fix (x.next = out before gz_load), gzread returns 1 and keeps the
   Z_ERRNO error.

   The replacement read() is defined in this program, so the static libz.a calls it; until
   `inject` is set it forwards to the next read(). The state fields come from gzguts.h. */
#define _GNU_SOURCE
#include <dlfcn.h>
#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include "zlib.h"
#include "gzguts.h"

static int inject;

ssize_t read(int fd, void *buf, size_t count) {
  static ssize_t (*next)(int, void *, size_t);
  static int fired;
  if (next == NULL) next = (ssize_t (*)(int, void *, size_t))dlsym(RTLD_NEXT, "read");
  if (inject) {
    if (fired++) { errno = EIO; return -1; }
    return next(fd, buf, count > 1 ? 1 : count);
  }
  return next(fd, buf, count);
}

int main(int argc, char **argv) {
  unsigned char buf[64];
  if (argc != 2) { fprintf(stderr, "usage: stale FILE\n"); return 2; }
  setvbuf(stdout, NULL, _IONBF, 0);
  gzFile f = gzopen(argv[1], "rb");
  gz_statep s = (gz_statep)f;
  if (f == NULL) return 2;
  if (gzbuffer(f, 16) != 0) return 3;
  for (int i = 0; i < 48; i++)
    if (gzgetc(f) < 0) { printf("early EOF at %d\n", i); return 4; }
  printf("before: how=%d have=%u next-offset=%ld size=%u\n", s->how, s->x.have,
         (long)(s->x.next - s->out), s->size);
  if (s->how != COPY || s->x.have != 0 || s->x.next != s->out + 2 * s->size) return 5;
  inject = 1;
  int n = gzread(f, buf, 1);
  printf("after: n=%d have=%u next-offset=%ld err=%d\n", n, s->x.have,
         (long)(s->x.next - s->out), s->err);
  gzclose(f);
  return 0;
}
