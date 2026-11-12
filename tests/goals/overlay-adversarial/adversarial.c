/* Targeted adversarial blocks for the dynamic-block overlay room (fact F9) at small memLevel.
 *
 * Usage: adversarial search <memLevel> <rounds> <seed>    construct and improve histograms
 *        adversarial check  <memLevel> <file>              replay a saved block (one "dist lc" per line)
 *
 * The worst order of a fixed symbol multiset puts the symbols in decreasing dynamic cost, so the
 * tightest prefix room is 8*lit_bufsize - 25 - H - E (H: header bits after the 3-bit tag,
 * E: total excess sum(max(0, d_i - 24))). The search therefore works on histograms (literal,
 * length-code and distance-code counts), pairs long length codes with long distance codes, and
 * orders the block greedily by decreasing cost. Seeds are built analytically: many distinct
 * literals spread to maximise the zero-run cost of the header, a few far matches with rare codes
 * (large excess), and copies of one cheap match whose gain pays for the header so that the
 * dynamic branch is still chosen. Every candidate goes through the real _tr_tally and
 * _tr_flush_block in the instrumented trees.c (see run.sh), which records the smallest gap in
 * bytes between pending output and the next unread symbol. A negative gap is an overwritten
 * symbol: the program prints the block and exits 1. */
#include "deflate.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>

extern long g_margin, g_entry;
extern unsigned long g_opt, g_stat;
extern void (*g_hook)(deflate_state *);

static const int xl[29] = {0,0,0,0,0,0,0,0,1,1,1,1,2,2,2,2,3,3,3,3,4,4,4,4,5,5,5,5,0};
static const int xd[30] = {0,0,0,0,1,1,2,2,3,3,4,4,5,5,6,6,7,7,8,8,9,9,10,10,11,11,12,12,13,13};
static const int baselen[29] = {3,4,5,6,7,8,9,10,11,13,15,17,19,23,27,31,35,43,51,59,67,83,99,115,131,163,195,227,258};
static const int basedist[30] = {1,2,3,4,5,7,9,13,17,25,33,49,65,97,129,193,257,385,513,769,1025,1537,2049,3073,4097,6145,8193,12289,16385,24577};

typedef struct { int dist; int lc; int cost; } sym;
typedef struct { int lit[256], len[29], dst[30]; } hist;

static z_stream strm;
static int L, H, E, D, dyn, nsym;
static long gap;
static int Llen[286], Dlen[30];

static void hook(deflate_state *s) {
  dyn = 1;
  H = (int)(8L * s->pending + s->bi_valid - g_entry - 3);
  for (int c = 0; c < 286; c++) Llen[c] = s->dyn_ltree[c].Len;
  for (int c = 0; c < 30; c++) Dlen[c] = s->dyn_dtree[c].Len;
}

static int cost(const sym *x) {
  if (x->dist == 0) return Llen[x->lc];
  int c = _length_code[x->lc], dc = d_code(x->dist - 1);
  return Llen[c + 257] + xl[c] + Dlen[dc] + xd[dc];
}

static void flush(const sym *a, int n) {
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
  g_margin = 1L << 40; dyn = 0;
  s->pending = 0; s->bi_valid = 0; s->bi_buf = 0;
  _tr_flush_block(s, NULL, 0, 0);
  gap = g_margin;
}

static int cmpcost(const void *p, const void *q) { return ((const sym *)q)->cost - ((const sym *)p)->cost; }

/* Build the block of a histogram: matches pair length and distance codes by decreasing extra
 * bits; the length (distance) inside a code is its largest value. Returns the symbol count. */
static int build(const hist *h, sym *a) {
  int n = 0, lens[256], dsts[256], nl = 0, nd = 0;
  for (int e = 5; e >= 0; e--) for (int c = 28; c >= 0; c--) if (xl[c] == e) for (int k = 0; k < h->len[c]; k++) lens[nl++] = c;
  for (int e = 13; e >= 0; e--) for (int c = 29; c >= 0; c--) if (xd[c] == e) for (int k = 0; k < h->dst[c]; k++) dsts[nd++] = c;
  if (nl != nd) return -1;
  for (int i = 0; i < nl; i++) {
    int c = lens[i], dc = dsts[i];
    int len = c == 28 ? 258 : baselen[c] + (1 << xl[c]) - 1; if (len > 257 && c != 28) len = 257;
    int dist = basedist[dc] + (1 << xd[dc]) - 1; if (dist > 32768) dist = 32768;
    a[n].dist = dist; a[n].lc = len - 3; n++;
  }
  for (int v = 0; v < 256; v++) for (int k = 0; k < h->lit[v]; k++) { a[n].dist = 0; a[n].lc = v; n++; }
  return n;
}

/* Score: worst-order room in bits (8L - 25 - H - E); a non-dynamic block scores by how far the
 * dynamic byte cost is from winning. Also flushes the worst order and keeps the real gap. */
static double score(const hist *h, sym *a, int *np) {
  int n = build(h, a);
  if (n < 1 || n > L - 1) return 1e9;
  flush(a, n);
  if (!dyn) return 1e6 + (double)(((g_opt + 10) >> 3) - ((g_stat + 10) >> 3) + 1);
  E = 0; D = 0;
  for (int i = 0; i < n; i++) { a[i].cost = cost(&a[i]); D += a[i].cost; if (a[i].cost > 24) E += a[i].cost - 24; }
  qsort(a, n, sizeof *a, cmpcost);
  flush(a, n);
  if (gap < 0) {
    printf("OVERWRITE gap %ld bytes, memLevel %d, %d symbols\n", gap, L == 128 ? 1 : 2, n);
    for (int i = 0; i < n; i++) printf("%d %d\n", a[i].dist, a[i].lc);
    exit(1);
  }
  *np = n;
  return 8.0 * L - 25 - H - E;
}

static unsigned long long rs = 88172645463325252ULL;
static unsigned long long rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int total(const hist *h) { int n = 0; for (int v = 0; v < 256; v++) n += h->lit[v]; for (int c = 0; c < 29; c++) n += h->len[c]; return n; }

/* Analytic seed: r distinct literals spaced sp apart from base, m copies of one cheap match
 * (length code lc0, distance code dc0), and k far matches on rare codes. */
static void seed(hist *h, int r, int sp, int base, int m, int lc0, int dc0, int k) {
  memset(h, 0, sizeof *h);
  for (int i = 0; i < r; i++) h->lit[(base + i * sp) % 256]++;
  h->len[lc0] += m; h->dst[dc0] += m;
  for (int i = 0; i < k; i++) { h->len[24 + i % 4]++; h->dst[29 - i % 8]++; }
}

static void mutate(hist *h) {
  int op = rnd() % 7;
  if (op == 0) { int v = rnd() % 256; if (h->lit[v]) h->lit[v]--; else h->lit[v]++; }
  else if (op == 1) { int v = rnd() % 256, w = rnd() % 256; if (h->lit[v]) { h->lit[v]--; h->lit[w]++; } }
  else if (op == 2) { h->len[rnd() % 29]++; h->dst[rnd() % 30]++; }
  else if (op == 3) { int c = rnd() % 29, d = rnd() % 30; if (h->len[c] && h->dst[d]) { h->len[c]--; h->dst[d]--; } }
  else if (op == 4) { int c = rnd() % 29, c2 = rnd() % 29; if (h->len[c]) { h->len[c]--; h->len[c2]++; } }
  else if (op == 5) { int d = rnd() % 30, d2 = rnd() % 30; if (h->dst[d]) { h->dst[d]--; h->dst[d2]++; } }
  else { int v = rnd() % 256, w = rnd() % 256; int t = h->lit[v]; h->lit[v] = h->lit[w]; h->lit[w] = t; }
}

static int init(int memlevel) {
  memset(&strm, 0, sizeof strm);
  if (deflateInit2(&strm, 6, Z_DEFLATED, 15, memlevel, Z_DEFAULT_STRATEGY) != Z_OK) return 0;
  L = ((deflate_state *)strm.state)->lit_bufsize;
  g_hook = hook;
  return 1;
}

int main(int argc, char **argv) {
  if (argc < 4) { fprintf(stderr, "usage: adversarial search <memLevel> <rounds> <seed> | check <memLevel> <file>\n"); return 2; }
  if (!init(atoi(argv[2]))) return 2;
  sym *a = malloc(sizeof(sym) * 1024), *best = malloc(sizeof(sym) * 1024);
  int n = 0, bn = 0;
  if (!strcmp(argv[1], "check")) {
    FILE *f = fopen(argv[3], "r"); if (!f) return 2;
    while (n < 1024 && fscanf(f, "%d %d", &a[n].dist, &a[n].lc) == 2) n++;
    fclose(f);
    flush(a, n);
    printf("memLevel %s: %d symbols, dynamic %d, header %d bits, smallest gap %ld bytes\n", argv[2], n, dyn, H, gap);
    return gap < 0;
  }
  long rounds = atol(argv[3]);
  rs ^= (unsigned long long)atol(argv[4 < argc ? 4 : 3]) * 0x9E3779B97F4A7C15ULL;
  for (int i = 0; i < 20; i++) rnd();
  /* Grid of analytic seeds; keep the best. */
  hist h, cur, bh; double bs = 1e18;
  for (int r = 0; r <= L - 1; r += (L - 1) / 16 + 1)
    for (int sp = 1; sp <= 13; sp += 2)
      for (int k = 0; k <= 24; k += 4)
        for (int m = 0; m + r + k <= L - 1; m += (L - 1) / 8 + 1) {
          seed(&h, r, sp, 144, m, 28, 0, k);
          double s = score(&h, a, &n);
          if (s < bs) { bs = s; bh = h; }
        }
  /* Local improvement in histogram space with a slowly cooling acceptance. */
  cur = bh; double cs = bs, T = 20;
  for (long it = 0; it < rounds; it++) {
    h = cur; int k = 1 + rnd() % 3;
    for (int j = 0; j < k; j++) mutate(&h);
    if (total(&h) > L - 1) continue;
    double s = score(&h, a, &n);
    if (s <= cs || (double)(rnd() % 1000000) / 1e6 < exp((cs - s) / T)) { cur = h; cs = s; }
    if (s < bs) { bs = s; bh = h; }
    T *= 0.99995; if (T < 0.5) T = 0.5;
  }
  score(&bh, best, &bn);
  printf("memLevel %s: best worst-order room %.0f bits (header %d, excess %d), smallest gap %ld bytes, %d symbols\n",
         argv[2], bs, H, E, gap, bn);
  for (int i = 0; i < bn; i++) fprintf(stderr, "%d %d\n", best[i].dist, best[i].lc);
  return 0;
}
