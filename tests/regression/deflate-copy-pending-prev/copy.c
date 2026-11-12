/* deflateResetKeep, deflateCopy, then a Z_RLE flush on the copy: longest_match follows an
   uninitialised prev slot.

   deflateResetKeep keeps the window and the hash and drops the lookahead. A following
   deflate(Z_BLOCK) sets insert = 2, so strstart - 2 and strstart - 1 wait for insertion, but they
   were inserted before the reset and are chain heads. deflateCopy copies prev only below
   strstart - insert, so their prev slots in the copy are fresh memory. On the copy, a Z_RLE flush
   with no input ends deflate_rle with insert = 0: fill_window will never re-insert the two
   positions. Back at the default strategy, an input that starts with the three bytes at
   strstart - 2 makes deflate_slow insert strstart with that key and call longest_match on the old
   head strstart - 2, which reads its uninitialised prev slot as the next candidate.

   The allocator fills fresh memory with the 16-bit value 1030, so the candidate lies just past the
   1024-byte window (windowBits 9) and AddressSanitizer reports the read. With any other content
   the candidate is whatever the slot holds. With the argument `plain` the default allocator is used:
   the slot is then uninitialised malloc memory, which MemorySanitizer or valgrind report. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "deflate.h"

static voidpf fill_alloc(voidpf opaque, uInt items, uInt size) {
  size_t bytes = (size_t)items * size;
  unsigned short *p = malloc(bytes + 2);
  (void)opaque;
  if (p == NULL) return NULL;
  for (size_t i = 0; i < bytes / 2; i++) p[i] = 1030;
  if (bytes & 1) ((unsigned char *)p)[bytes - 1] = 0;
  return p;
}
static void plain_free(voidpf opaque, voidpf p) { (void)opaque; free(p); }

int main(int argc, char **argv) {
  static unsigned char in[4000], out[16000], again[600];
  unsigned x = 1;
  for (int i = 0; i < 4000; i++) { x = x * 1103515245u + 12345u; in[i] = 'a' + ((x >> 16) % 4); }
  z_stream a;
  memset(&a, 0, sizeof a);
  if (!(argc > 1 && strcmp(argv[1], "plain") == 0)) { a.zalloc = fill_alloc; a.zfree = plain_free; }
  if (deflateInit2(&a, 6, Z_DEFLATED, 9, 8, Z_DEFAULT_STRATEGY) != Z_OK) return 2;
  deflate_state *s = (deflate_state *)a.state;
  a.next_in = in; a.avail_in = 600; a.next_out = out; a.avail_out = sizeof out;
  deflate(&a, Z_NO_FLUSH);
  deflateResetKeep(&a);
  a.next_in = in; a.avail_in = 0; a.next_out = out; a.avail_out = sizeof out;
  deflate(&a, Z_BLOCK);
  unsigned ss = s->strstart;
  printf("source: strstart %u insert %u\n", ss, s->insert);
  z_stream c;
  if (deflateCopy(&c, &a) != Z_OK) return 3;
  c.next_in = in; c.avail_in = 0; c.next_out = out; c.avail_out = sizeof out;
  deflateParams(&c, 6, Z_RLE);
  deflate(&c, Z_SYNC_FLUSH);
  deflateParams(&c, 6, Z_DEFAULT_STRATEGY);
  again[0] = s->window[ss - 2]; again[1] = s->window[ss - 1]; again[2] = s->window[ss];
  for (int i = 3; i < (int)sizeof again; i++) again[i] = (unsigned char)('0' + (i % 10));
  c.next_in = again; c.avail_in = sizeof again;
  int rc = deflate(&c, Z_FINISH);
  printf("copy: deflate returned %d\n", rc);
  deflateEnd(&c);
  deflateEnd(&a);
  return 0;
}
