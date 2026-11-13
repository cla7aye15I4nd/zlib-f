/* Search for a violation of the overlay bound F9 (docs/proof/trees.md) in dynamic blocks.
 *
 * Usage: search <memLevel> <windowBits> <steps> <seed>
 *
 * A state from deflateInit2 records an arbitrary block of valid symbols (literals 0..255,
 * matches of length 3..258 at distance 1..2^windowBits-262) with the real _tr_tally macros and
 * flushes it with the real _tr_flush_block. The instrumented trees.c (see run.sh) records the
 * smallest gap, in bytes, between the pending output and the next unread symbol, before the
 * first symbol and after every symbol of compress_block. Simulated annealing over the symbol
 * blocks minimizes that gap. A negative gap would be an overwritten symbol. Exit 1 then.
 * This is evidence about the blocks visited, not a proof. */
#include "deflate.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
extern long g_margin;
typedef struct { int dist; int lc; } sym;
static z_stream strm; static int memlevel, wbits, maxdist;
long evaluate(sym *a, int n) {
  deflate_state *s;
  deflateReset(&strm);
  s = (deflate_state *)strm.state;
  strm.data_type = Z_BINARY;
  for (int i = 0; i < n; i++) {
    int fl;
    if (a[i].dist == 0) { _tr_tally_lit(s, (uch)a[i].lc, fl); }
    else { _tr_tally_dist(s, (unsigned)a[i].dist, (unsigned)a[i].lc, fl); }
    (void)fl;
  }
  g_margin = 1L << 40;
  s->pending = 0; s->bi_valid = 0; s->bi_buf = 0;
  _tr_flush_block(s, NULL, 0, 0);
  return g_margin;
}
static unsigned long long rs = 88172645463325252ULL;
static unsigned long long rnd(void){ rs ^= rs<<13; rs ^= rs>>7; rs ^= rs<<17; return rs; }
static sym rsym(void) {
  sym x;
  int t = rnd()%4;
  if (t == 0) { x.dist = 0; x.lc = rnd()%256; }
  else { x.lc = rnd()%256; 
    int r = rnd()%3; 
    if (r==0) x.dist = 1 + rnd()%maxdist; else if (r==1) x.dist = maxdist - rnd()%(maxdist/2); else x.dist = 1 + rnd()%64; }
  return x;
}
int main(int argc, char **argv) {
  memlevel = argc > 1 ? atoi(argv[1]) : 1;
  wbits = argc > 2 ? atoi(argv[2]) : 15;
  long iters = argc > 3 ? atol(argv[3]) : 200000;
  rs ^= (unsigned long long)(argc > 4 ? atol(argv[4]) : time(0));
  memset(&strm, 0, sizeof strm);
  if (deflateInit2(&strm, 6, 8, wbits, memlevel, 0) != Z_OK) return 1;
  deflate_state *s = (deflate_state *)strm.state;
  int B = s->lit_bufsize; int nmax = B - 1;
  maxdist = (1 << wbits) - 262;
  sym *cur = malloc(sizeof(sym) * nmax), *nx = malloc(sizeof(sym) * nmax), *best = malloc(sizeof(sym)*nmax);
  int n = nmax, bn;
  for (int i = 0; i < n; i++) cur[i] = rsym();
  long cm = evaluate(cur, n), bm = cm; memcpy(best, cur, sizeof(sym)*n); bn = n;
  double T = 8.0;
  for (long it = 0; it < iters; it++) {
    int m = n; memcpy(nx, cur, sizeof(sym)*n);
    int k = 1 + rnd()%3;
    for (int j = 0; j < k; j++) {
      int op = rnd()%5; int p = rnd()%m;
      if (op <= 1) nx[p] = rsym();
      else if (op == 2) { int q = rnd()%m; sym t = nx[p]; nx[p] = nx[q]; nx[q] = t; }
      else if (op == 3) { int q = rnd()%m; nx[p] = nx[q]; }
      else if (op == 4 && rnd()%4 == 0) { if (rnd()%2 && m > 2) m--; else if (m < nmax) { nx[m] = rsym(); m++; } }
      else { if (rnd()%2) { nx[p].lc = rnd()%256; } else if (nx[p].dist) nx[p].dist = 1 + rnd()%maxdist; }
    }
    long nm = evaluate(nx, m);
    if (nm <= cm || (double)(rnd()%1000000)/1e6 < __builtin_exp((cm - nm)/T)) { memcpy(cur, nx, sizeof(sym)*m); n = m; cm = nm; }
    if (cm < bm) { bm = cm; memcpy(best, cur, sizeof(sym)*n); bn = n; }
    T *= 0.99997; if (T < 0.3) T = 0.3;
    if (it % 50000 == 0) { fprintf(stderr, "it %ld cur %ld best %ld\n", it, cm, bm); }
  }
  printf("memLevel %d wbits %d best margin %ld bytes (B=%d)\n", memlevel, wbits, bm, B);
  char fn[64]; sprintf(fn, "best-%d.txt", memlevel); FILE *f = fopen(fn, "w"); for (int i = 0; i < bn; i++) fprintf(f, "%d %d\n", best[i].dist, best[i].lc); fclose(f);
  return bm < 0 ? 1 : 0;
}
