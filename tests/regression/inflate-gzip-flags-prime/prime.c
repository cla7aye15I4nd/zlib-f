/* inflatePrime while inflate waits in FLAGS: the gzip flags word is wider than 16 bits.
   Prints the state after each step and exits 0 when the C writes flags >= 65536. */
#include <stdio.h>
#include <string.h>
#include "zlib.h"
#include "zutil.h"
#include "inftrees.h"
#include "inflate.h"

int main(void) {
  z_stream s;
  memset(&s, 0, sizeof s);
  if (inflateInit2(&s, 31) != Z_OK) return 2;
  struct inflate_state *st = (struct inflate_state *)s.state;
  unsigned char magic[2] = {0x1f, 0x8b}, out[16];
  s.next_in = magic; s.avail_in = 2; s.next_out = out; s.avail_out = sizeof out;
  int ret = inflate(&s, Z_NO_FLUSH);
  printf("magic: ret=%d mode=%d bits=%u\n", ret, (int)st->mode, st->bits);
  if (ret != Z_OK || st->mode != FLAGS || st->bits != 0) return 2;
  /* 32 bits: method byte 8, flag byte 0, then 0x0001 above bit 16. */
  int p1 = inflatePrime(&s, 16, 0x0008), p2 = inflatePrime(&s, 16, 0x0001);
  printf("prime: %d %d bits=%u hold=0x%lx\n", p1, p2, st->bits, st->hold);
  if (p1 != Z_OK || p2 != Z_OK) return 2;
  unsigned char more[4] = {0, 0, 0, 0};
  s.next_in = more; s.avail_in = 4;
  ret = inflate(&s, Z_NO_FLUSH);
  printf("flags: ret=%d mode=%d flags=%d\n", ret, (int)st->mode, st->flags);
  inflateEnd(&s);
  return ret != Z_OK ? 2 : 0;
}
