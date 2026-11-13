/* gz_comp's deflate loop on the real C, with no new input:
 *   do { if (avail_out == 0) reset to size; have = avail_out; deflate(strm, flush); have -= avail_out; } while (have);
 * For every level, strategy, memLevel 1 and 8, inputs of 0, 3 and 5000 bytes (consumed first with Z_NO_FLUSH),
 * every flush value 0..5 and output sizes 1..8 and 64, count deflate calls up to CAP.
 * Expected (the facts behind DeflateQuiet and gzbuffer's clamp to 8):
 *   - size >= 8: every loop ends;
 *   - sizes 1..7: some loops cycle (a flush marker fills the output, last_flush = -1, the marker is emitted again);
 *     the smallest known case, level 0, memLevel 1, no input, Z_PARTIAL_FLUSH, size 1, must cycle.
 * Exit 0 when both hold. Evidence about the C, not proof. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "zlib.h"
#define CAP 200000L
static unsigned char outbuf[1 << 16];
static long loop(z_streamp s, int flush, unsigned size) {
  unsigned have; long calls = 0;
  s->next_out = outbuf; s->avail_out = size;
  do {
    if (s->avail_out == 0) { s->next_out = outbuf; s->avail_out = size; }
    have = s->avail_out;
    if (deflate(s, flush) == Z_STREAM_ERROR) return -1;
    have -= s->avail_out;
    if (++calls > CAP) return CAP + 1;
  } while (have);
  return calls;
}
int main(void) {
  static unsigned char in[5000];
  unsigned sizes[] = {1, 2, 3, 4, 5, 6, 7, 8, 64};
  size_t lens[] = {0, 3, 5000};
  long runs = 0, cyclesSmall = 0, cyclesLarge = 0, maxLarge = 0, errors = 0;
  srand(1);
  for (int level = 0; level <= 9; level++)
  for (int strat = 0; strat <= 4; strat++)
  for (int mem = 1; mem <= 8; mem += 7)
  for (int li = 0; li < 3; li++)
  for (int flush = 0; flush <= 5; flush++)
  for (int si = 0; si < 9; si++) {
    z_stream s; memset(&s, 0, sizeof s);
    if (deflateInit2(&s, level, Z_DEFLATED, 31, mem, strat) != Z_OK) { fprintf(stderr, "init failed\n"); return 2; }
    for (size_t i = 0; i < lens[li]; i++) in[i] = (unsigned char)rand();
    s.next_in = in; s.avail_in = (uInt)lens[li];
    while (s.avail_in) { s.next_out = outbuf; s.avail_out = sizeof outbuf; deflate(&s, Z_NO_FLUSH); }
    long c = loop(&s, flush, sizes[si]);
    runs++;
    if (c < 0) errors++;
    else if (sizes[si] >= 8) {
      if (c > CAP) { cyclesLarge++; printf("CYCLE at size %u: level %d strategy %d memLevel %d input %zu flush %d\n",
                                         sizes[si], level, strat, mem, lens[li], flush); }
      else if (c > maxLarge) maxLarge = c;
    } else if (c > CAP) cyclesSmall++;
    deflateEnd(&s);
  }
  z_stream s; memset(&s, 0, sizeof s);
  deflateInit2(&s, 0, Z_DEFLATED, 31, 1, Z_DEFAULT_STRATEGY);
  long known = loop(&s, Z_PARTIAL_FLUSH, 1);
  deflateEnd(&s);
  printf("runs %ld, stream errors %ld, cycles at sizes 1..7: %ld, cycles at sizes >= 8: %ld, longest loop at >= 8: %ld calls, "
         "known small case cycles: %s\n", runs, errors, cyclesSmall, cyclesLarge, maxLarge, known > CAP ? "yes" : "NO");
  return (cyclesLarge == 0 && errors == 0 && known > CAP) ? 0 : 1;
}
