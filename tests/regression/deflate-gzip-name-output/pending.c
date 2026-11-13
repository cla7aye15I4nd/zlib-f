/* The gzip header name lies in the stream's own pending_buf. At the call it is a valid C
   string (NUL at name[4]). The header bytes written into pending_buf overwrite that NUL, and
   the name loop reads on past the end of pending_buf. */
#include <stdio.h>
#include <string.h>
#include "zlib.h"
#include "deflate.h"

int main(void) {
  z_stream s;
  memset(&s, 0, sizeof s);
  if (deflateInit2(&s, 9, Z_DEFLATED, 31, 1, Z_DEFAULT_STRATEGY) != Z_OK) return 2;
  deflate_state *st = (deflate_state *)s.state;
  memset(st->pending_buf, 'a', st->pending_buf_size);
  Bytef *name = st->pending_buf + 5;
  name[4] = 0;
  gz_header head;
  memset(&head, 0, sizeof head);
  head.name = name;
  head.os = 3;
  head.time = 0x01010101;
  if (deflateSetHeader(&s, &head) != Z_OK) return 2;
  static unsigned char out[4096];
  s.next_in = out;
  s.avail_in = 0;
  s.next_out = out;
  s.avail_out = sizeof out;
  int rc = deflate(&s, Z_NO_FLUSH);
  printf("rc=%d avail_out=%u\n", rc, s.avail_out);
  deflateEnd(&s);
  return 0;
}
