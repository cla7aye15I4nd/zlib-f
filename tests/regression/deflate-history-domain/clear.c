/* The caller clears head->extra while deflate is inside the extra field (EXTRA_STATE with
   gzindex > 0). The next call skips the extra stage without resetting gzindex, and the name
   loop starts reading at name[gzindex], past the end of the short name. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "zlib.h"

int main(void) {
  z_stream s;
  memset(&s, 0, sizeof s);
  if (deflateInit2(&s, 6, Z_DEFLATED, 31, 1, Z_DEFAULT_STRATEGY) != Z_OK) return 2;
  static unsigned char extra[2000];
  memset(extra, 'e', sizeof extra);
  char *name = malloc(4);
  strcpy(name, "abc");
  gz_header head;
  memset(&head, 0, sizeof head);
  head.extra = extra;
  head.extra_len = 1500;
  head.name = (Bytef *)name;
  if (deflateSetHeader(&s, &head) != Z_OK) return 2;
  static unsigned char out[4096];
  s.next_in = out; s.avail_in = 0;
  s.next_out = out; s.avail_out = 100;          /* first flush leaves bytes pending */
  int rc = deflate(&s, Z_FINISH);
  printf("first rc=%d\n", rc);
  head.extra = Z_NULL;                          /* caller edit between calls */
  s.next_out = out; s.avail_out = sizeof out;
  rc = deflate(&s, Z_FINISH);
  printf("second rc=%d\n", rc);
  deflateEnd(&s);
  free(name);
  return 0;
}
