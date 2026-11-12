#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "deflate.h"
/* deflateResetKeep keeps the window and the hash and drops the lookahead. Raw deflate: data A
   with Z_NO_FLUSH (leaves lookahead), deflateResetKeep, data B with Z_FINISH. The second stream
   may refer to the kept window window[0 .. strstart), so it is decoded with those bytes as the
   dictionary. Prints the histories whose decoding differs from B. Built with the pinned zlib:
     cc -I zlib repro.c zlib/{adler32,crc32,deflate,inflate,inftrees,inffast,trees,zutil}.c
   With CLEAR_HASH(s) added to deflateResetKeep after `s->lookahead = 0;` no history differs
   (200000 tried). */
static unsigned char win[1<<17], A[1<<16], B[1<<16], out[1<<18], back[1<<17];
int main(int argc, char **argv) {
  int bad = 0, tried = 0;
  for (unsigned seed = 0; seed < 200000 && bad < 3; seed++) {
    srand(seed);
    int lvl = 1 + rand() % 9, wb = 9 + rand() % 7, mem = 1 + rand() % 9;
    int alpha = 2 + rand() % 4;
    int na = 300 + rand() % 3000, nb = 50 + rand() % 2000;
    for (int i = 0; i < na; i++) A[i] = 'a' + rand() % alpha;
    for (int i = 0; i < nb; i++) B[i] = 'a' + rand() % alpha;
    z_stream s; memset(&s, 0, sizeof s);
    if (deflateInit2(&s, lvl, Z_DEFLATED, -wb, mem, Z_DEFAULT_STRATEGY) != Z_OK) return 1;
    s.next_in = A; s.avail_in = na; s.next_out = out; s.avail_out = sizeof out;
    deflate(&s, Z_NO_FLUSH);
    if (s.avail_in != 0) { deflateEnd(&s); continue; }
    unsigned kept = ((deflate_state *)s.state)->strstart;
    memcpy(win, ((deflate_state *)s.state)->window, kept);
    unsigned slid = ((deflate_state *)s.state)->slid;
    if (deflateResetKeep(&s) != Z_OK) return 2;
    s.next_in = B; s.avail_in = nb; s.next_out = out; s.avail_out = sizeof out;
    if (deflate(&s, Z_FINISH) != Z_STREAM_END) { deflateEnd(&s); continue; }
    unsigned long olen = s.total_out; deflateEnd(&s);
    tried++;
    z_stream t; memset(&t, 0, sizeof t); inflateInit2(&t, -wb);
    (void)slid;
    inflateSetDictionary(&t, win, kept);
    t.next_in = out; t.avail_in = olen; t.next_out = back; t.avail_out = sizeof back;
    int rc = inflate(&t, Z_FINISH);
    unsigned long got = t.total_out; inflateEnd(&t);
    if (rc != Z_STREAM_END || got != (unsigned long)nb || memcmp(back, B, nb)) {
      bad++;
      int at = -1; for (int i = 0; i < nb && i < (int)got; i++) if (back[i] != B[i]) { at = i; break; }
      printf("MISMATCH seed %u level %d wb %d mem %d alpha %d na %d nb %d rc %d got %lu first diff %d\n",
             seed, lvl, wb, mem, alpha, na, nb, rc, got, at);
    }
  }
  printf("tried %d bad %d\n", tried, bad);
  return bad != 0;
}
