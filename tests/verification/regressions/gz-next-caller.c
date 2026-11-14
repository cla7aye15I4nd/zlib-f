/* Regression for the statement correction of GzCommon.next (ZlibF/Proof/gz.inv-model.lean).
 * The old clause "x.next is NULL, or inside an owned buffer" is false between calls: the direct path of gz_read
 * (gz_decomp into the caller's buffer) leaves x.next = next_out - have inside the caller's buffer, with x.have = 0,
 * and patch 0005 only guards `x.next += n` with n != 0. A gzread of 40000 bytes with the default want 8192 inflates
 * directly into buf; the last trip starts at buf + 16384 or later.
 * Build against zlib/ with patches/*.patch applied, from a patched copy of zlib/ (ASan and UBSan report nothing):
 *   cc -fsanitize=address,undefined -DHAVE_UNISTD_H -I. -o gz-next-caller gz-next-caller.c adler32.c crc32.c \
 *     deflate.c inffast.c inflate.c inftrees.c trees.c zutil.c gzlib.c gzread.c gzwrite.c gzclose.c
 * The gzip file f.gz is 40033 bytes. Expected output:
 *   read 40000 next_in_buf=1 offset=16384 have=0
 */
#include <stdio.h>
#include "zlib.h"
#include "gzguts.h"
int main(void){
  /* 40000 bytes of pseudo-random data: the gzip file is about as long as its content */
  static unsigned char data[40000], buf[40000];
  unsigned long x = 12345;
  for (int k = 0; k < 40000; k++) { x = x * 1103515245UL + 12345UL; data[k] = (unsigned char)(x >> 16); }
  gzFile w = gzopen("f.gz", "wb"); gzwrite(w, data, 40000); gzclose(w);
  gzFile r = gzopen("f.gz", "rb");
  int n = gzread(r, buf, 40000);
  gz_statep s = (gz_statep)r;
  int inside = s->x.next >= buf && s->x.next < buf + 40000;
  printf("read %d next_in_buf=%d offset=%ld have=%u\n", n, inside, inside ? (long)(s->x.next - buf) : -1L,
         s->x.have);
  gzclose(r);
  return 0;
}
