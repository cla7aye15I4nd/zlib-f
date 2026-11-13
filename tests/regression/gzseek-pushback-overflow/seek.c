/* gzungetc right after gzopen, then gzseek: signed overflow in gzseek64.

   gzungetc at position zero is allowed and sets state->x.pos to -1. Two calls follow, each on a
   fresh handle:
   - `cur`: gzseek(f, 1, SEEK_CUR). pos is -1, and the range check evaluates GZ_OFF_MAX - (-1).
   - `set`: gzseek(f, LONG_MAX, SEEK_SET). The range check passes (pos is 0), and the
     displacement pos - state->x.pos is LONG_MAX + 1.
   The file is given on the command line (transparent or gzip). z_off_t is 64 bits (LP64), so
   gzseek reaches gzseek64 with the same value. */
#include <limits.h>
#include <stdio.h>
#include <string.h>
#include "zlib.h"

int main(int argc, char **argv) {
  if (argc != 3) { fprintf(stderr, "usage: seek FILE cur|set\n"); return 2; }
  gzFile f = gzopen(argv[1], "rb");
  if (f == NULL) return 2;
  setvbuf(stdout, NULL, _IONBF, 0);
  printf("ungetc=%d\n", gzungetc('Q', f));
  if (strcmp(argv[2], "cur") == 0)
    printf("seek cur 1 = %ld\n", (long)gzseek(f, 1L, SEEK_CUR));
  else
    printf("seek set LONG_MAX = %ld\n", (long)gzseek(f, LONG_MAX, SEEK_SET));
  gzclose(f);
  return 0;
}
