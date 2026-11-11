/* Inflate with the input range and the output range in one heap block.
 * The two ranges are disjoint at the call, as zlib.h asks of no more. Both
 * orders are run: input before output, and output before input. Each must
 * decode the same bytes as with separate blocks, with no sanitizer report.
 * The stream has many matches, and both buffers are large, so inflate_fast
 * does the work (avail_in >= 6 and avail_out >= 258 at entry). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "zlib.h"

#define N 200000

static int run(unsigned char *block, size_t in_off, const unsigned char *z, size_t zn,
               size_t out_off, const unsigned char *want) {
  memcpy(block + in_off, z, zn);
  z_stream s;
  memset(&s, 0, sizeof s);
  if (inflateInit(&s) != Z_OK) return 1;
  s.next_in = block + in_off;
  s.avail_in = (uInt)zn;
  s.next_out = block + out_off;
  s.avail_out = N;
  int r = inflate(&s, Z_FINISH);
  int bad = r != Z_STREAM_END || s.total_out != N || memcmp(block + out_off, want, N) != 0;
  inflateEnd(&s);
  return bad;
}

int main(void) {
  unsigned char *plain = malloc(N);
  unsigned int x = 1;
  for (size_t i = 0; i < N; i++) {          /* repeated words with variation */
    x = x * 1103515245u + 12345u;
    plain[i] = (unsigned char)("abcdefgh"[(x >> 16) % 8] + (i % 97 == 0));
  }
  uLong zn = compressBound(N);
  unsigned char *z = malloc(zn);
  if (compress2(z, &zn, plain, N, 6) != Z_OK) return 2;
  unsigned char *block = malloc(zn + N);
  int bad = 0;
  bad |= run(block, 0, z, zn, zn, plain);   /* input, then output */
  bad |= run(block, N, z, zn, 0, plain);    /* output, then input */
  printf("%s: %lu compressed bytes, %d bytes out, one block\n", bad ? "MISMATCH" : "ok",
         (unsigned long)zn, N);
  free(block); free(z); free(plain);
  return bad;
}
