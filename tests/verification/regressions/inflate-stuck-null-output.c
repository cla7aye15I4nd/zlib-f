/* Regression for the statement correction of InflateStuckNoOutput (ZlibF/Proof/gz.read-decomp.lean, d509a81c).
 * The old conclusion "rc = Z_DATA_ERROR or rc = Z_MEM_ERROR" for an inflate call from mode BAD or MEM is false:
 * inflate's entry check (inflateStateCheck, next_out == Z_NULL, next_in == Z_NULL with avail_in != 0) comes
 * before the mode dispatch, so a stream in BAD with next_out == NULL gets Z_STREAM_ERROR (-2), with avail_in and
 * avail_out unchanged. The corrected statement allows Z_STREAM_ERROR.
 * Build against zlib/ with patches/*.patch applied, from a patched copy of zlib/ (ASan and UBSan report nothing):
 *   cc -fsanitize=address,undefined -I. -o inflate-stuck-null-output inflate-stuck-null-output.c adler32.c \
 *     crc32.c inffast.c inflate.c inftrees.c zutil.c
 * Expected output:
 *   bad: rc -3
 *   stuck, next_out set: rc -3 avail_in 5->5 avail_out 9->9
 *   stuck, next_out NULL: rc -2 avail_in 5->5 avail_out 9->9
 */
#include <stdio.h>
#include <string.h>
#include "zlib.h"
int main(void) {
  unsigned char in[8] = {0x78, 0x00, 0, 0, 0, 0, 0, 0}, out[16];
  z_stream z;
  memset(&z, 0, sizeof z);
  if (inflateInit(&z) != Z_OK) return 1;
  /* 0x78 0x00 fails the zlib header check (0x7800 % 31 != 0): the stream goes to BAD */
  z.next_in = in; z.avail_in = 2; z.next_out = out; z.avail_out = sizeof out;
  printf("bad: rc %d\n", inflate(&z, Z_NO_FLUSH));
  /* from BAD: with an output buffer the call returns Z_DATA_ERROR and moves nothing */
  z.next_in = in; z.avail_in = 5; z.next_out = out; z.avail_out = 9;
  int rc = inflate(&z, Z_NO_FLUSH);
  printf("stuck, next_out set: rc %d avail_in 5->%u avail_out 9->%u\n", rc, z.avail_in, z.avail_out);
  /* from BAD with next_out == NULL: the entry check returns Z_STREAM_ERROR, again moving nothing */
  z.next_in = in; z.avail_in = 5; z.next_out = Z_NULL; z.avail_out = 9;
  rc = inflate(&z, Z_NO_FLUSH);
  printf("stuck, next_out NULL: rc %d avail_in 5->%u avail_out 9->%u\n", rc, z.avail_in, z.avail_out);
  inflateEnd(&z);
  return 0;
}
