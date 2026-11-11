/* The gzip header name lies in the output buffer. At entry it is a valid C string (NUL at
   index 505). The first flush of the name loop writes the header and the first name bytes to
   next_out, which shifts the name 10 bytes forward over its own NUL; the loop then reads on
   past the end of the 1024-byte buffer. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "zlib.h"

int main(void) {
  z_stream s;
  memset(&s, 0, sizeof s);
  if (deflateInit2(&s, 6, Z_DEFLATED, 31, 1, Z_DEFAULT_STRATEGY) != Z_OK) return 2;
  unsigned char *buf = malloc(1024);
  memset(buf, 'a', 1024);
  buf[505] = 0;
  gz_header head;
  memset(&head, 0, sizeof head);
  head.name = buf;
  if (deflateSetHeader(&s, &head) != Z_OK) return 2;
  s.next_in = (unsigned char *)"x";
  s.avail_in = 0;
  s.next_out = buf;
  s.avail_out = 1024;
  int rc = deflate(&s, Z_NO_FLUSH);
  printf("rc=%d avail_out=%u\n", rc, s.avail_out);
  deflateEnd(&s);
  free(buf);
  return 0;
}
