/* Statement test of the memLevel 2 overlay certificate (lit_bufsize 256), on the real C.
 *
 * Usage: check search <rounds> <seed>      adversarial search for the tightest block
 *        check replay <file>               one block, "dist lc" per line
 *
 * For every block that _tr_flush_block builds trees for (dynamic or not), a hook placed after
 * build_bl_tree (see run.sh) checks each fact the Lean proof uses, on the actual code lengths:
 *   F1  every used code has 1 <= len <= 15 and f*F(len+1) + F(len) <= lit_bufsize + 2;
 *   F2  a code with a nonzero length and no occurrence has index <= 2 (zlib's forced leaves);
 *   F3  Kraft: sum 2^(15-len) <= 2^15 in each tree;
 *   F4  scan: the header trees cost under the reference bit-length code K0 (scan_tree's own
 *       counts) is at most sum over nonzero entries of max(K0[len], 3) plus the zero blocks
 *       g(1)=2, g(2)=4, g(3..10)=6, g(11..138)=14, plus 40 in the literal tree for blocks > 138;
 *   F5  the bound: 71 + (header trees under K0) + E <= BOUND, with E the block excess
 *       sum max(0, cost - 24) under the actual lengths. BOUND is the certificate's (cert.py).
 * It also reports the largest observed repair excess  sum f_k (blLen_k - K0_k)  (batch 1's Delta).
 * A violated fact prints the block and exits 1. */
#include "deflate.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>

#ifndef BOUND
#define BOUND 1893
#endif

extern void (*g_hook2)(deflate_state *);

static const int xl[29] = {0,0,0,0,0,0,0,0,1,1,1,1,2,2,2,2,3,3,3,3,4,4,4,4,5,5,5,5,0};
static const int xd[30] = {0,0,0,0,1,1,2,2,3,3,4,4,5,5,6,6,7,7,8,8,9,9,10,10,11,11,12,12,13,13};
static const int baselen[29] = {3,4,5,6,7,8,9,10,11,13,15,17,19,23,27,31,35,43,51,59,67,83,99,115,131,163,195,227,258};
static const int basedist[30] = {1,2,3,4,5,7,9,13,17,25,33,49,65,97,129,193,257,385,513,769,1025,1537,2049,3073,4097,6145,8193,12289,16385,24577};
static const int K0[19] = {2,7,7,5,5,4,4,4,4,3,4,4,7,7,7,7,7,3,7};
static const int blx[19] = {0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,3,7};
/* memLevel 1: the reference code kappa1 (symbols 10..15 unused) and the region charges, scaled by 2 */
static const int K1[19] = {2,8,8,6,5,4,3,4,4,3,7,7,7,7,7,7,7,3,3};
static int pe1(int x) { return K1[x] > 3 ? K1[x] : 3; }
static long charge1(int region, int x) { /* region 0 literal (0..256), 1 length, 2 distance */
  if (x == 0) return region == 0 ? 1 : 4;
  return 2L * pe1(x) + (region == 0 ? 9 : 0);
}
static const int blOrder[19] = {16,17,18,0,8,7,9,6,10,5,11,4,12,3,13,2,14,1,15};
static int fixedLen(int v) { return v < 144 ? 8 : v < 256 ? 9 : v < 280 ? 7 : 8; }
static long maxDelta1 = -1000000, minSlack1 = 1L << 40, dynBlocks1;
/* exact sides of the proved inequalities (see README): smallest slack seen */
static long minCert2 = 1L << 40, minAsm2 = 1L << 40, minReal2 = 1L << 40;
static long minCert1 = 1L << 40, minReal1 = 1L << 40;
#ifndef DELTA2
#define DELTA2 160
#endif
#ifndef DELTA1
#define DELTA1 115
#endif
static const int ENTRY2[16] = {2,7,7,5,5,4,4,4,4,3,4,4,7,7,7,7};
/* the certificate's excess: per occurrence, length codes x + e - 9, distance codes x + e - 15 */
static long occExcess(const int *ll, const int *dl, const int *fl, const int *fd) {
  long e = 0;
  for (int v = 257; v < 286; v++) { long t = ll[v] + xl[v - 257] - 9; if (t > 0) e += fl[v] * t; }
  for (int v = 0; v < 30; v++) { long t = dl[v] + xd[v] - 15; if (t > 0) e += fd[v] * t; }
  return e;
}

typedef struct { int dist; int lc; } sym;
typedef struct { int lit[256], len[29], dst[30]; } hist;

static z_stream strm;
static int L, built, nsym;
static sym *cur;
static long fib[40];
static long slack, maxDelta = -1000000, blocks;

static void fail(const char *what) {
  printf("VIOLATED %s\n", what);
  for (int i = 0; i < nsym; i++) printf("%d %d\n", cur[i].dist, cur[i].lc);
  exit(1);
}

/* scan_tree's counts for lengths len[0..maxc] (guard 0xffff after maxc). */
static void scan(const int *len, int maxc, long *f) {
  int prev = -1, next = len[0], count = 0, mx = 7, mn = 4;
  if (next == 0) { mx = 138; mn = 3; }
  for (int n = 0; n <= maxc; n++) {
    int c = next; next = n + 1 <= maxc ? len[n + 1] : 0xffff;
    if (++count < mx && c == next) continue;
    else if (count < mn) f[c] += count;
    else if (c != 0) { if (c != prev) f[c]++; f[16]++; }
    else if (count <= 10) f[17]++;
    else f[18]++;
    count = 0; prev = c;
    if (next == 0) { mx = 138; mn = 3; } else if (c == next) { mx = 6; mn = 3; } else { mx = 7; mn = 4; }
  }
}

static long g(int m) { return m == 1 ? 2 : m == 2 ? 4 : m <= 10 ? 6 : 14; }

/* F4's right side for one tree. */
static long entries_bound(const int *len, int maxc, int lit) {
  long b = 0;
  for (int v = 0; v <= maxc; v++) if (len[v]) b += K0[len[v]] > 3 ? K0[len[v]] : 3;
  for (int v = 0; v <= maxc;) {
    if (len[v]) { v++; continue; }
    int m = 0; while (v <= maxc && !len[v]) { m++; v++; }
    if (m > 138) { if (!lit) fail("F4 long block in the distance tree"); b += 40; }
    b += g(m > 138 ? 11 : m);
  }
  return b;
}

/* memLevel 1: the facts of the L = 128 certificate (overlay_cert128.py) on the actual block. */
static void check128(deflate_state *s, const int *ll, const int *dl, const int *fl, const int *fd,
                     int ml, int md, const long *f, long E) {
  long C2 = 0, hk1 = 0, delta1 = 0, H, fx = 0, fs = 0, fdsum = 0;
  int forcedL = 0, forcedD = 0, nzL = 0, nzD = 0;
  for (int v = 0; v < 286; v++) {
    C2 += charge1(v <= 256 ? 0 : 1, ll[v]);
    if (ll[v]) nzL++;
    if (ll[v] && !fl[v]) forcedL = 1;
    if (ll[v] > 9) fail("M1 length above 9 (literal tree)");
    fx += (long)fl[v] * ll[v]; fs += (long)fl[v] * fixedLen(v);
  }
  for (int v = 0; v < 30; v++) {
    C2 += charge1(2, dl[v]);
    if (dl[v]) nzD++;
    if (dl[v] && !fd[v]) forcedD = 1;
    if (dl[v] > 9) fail("M1 length above 9 (distance tree)");
    fx += (long)fd[v] * dl[v]; fdsum += fd[v];
  }
  int mb = 3;
  for (int k = 18; k >= 3; k--) if (s->bl_tree[blOrder[k]].Len != 0) { mb = k; break; }
  H = 14 + 3L * (mb + 1);
  for (int k = 0; k < 19; k++) {
    hk1 += f[k] * (K1[k] + blx[k]);
    delta1 += f[k] * ((long)s->bl_tree[k].Len - K1[k]);
    H += f[k] * (s->bl_tree[k].Len + blx[k]);
  }
  if (2 * hk1 > C2) fail("M2 region scan");
  if (H > 71 + delta1 + hk1) fail("M3 header row");
  if (forcedL && nzL != 2) fail("M4 two leaves (literal tree)");
  if (forcedD && nzD != 2) fail("M4 two leaves (distance tree)");
  int dynamic = ((s->static_len + 10) >> 3) > ((s->opt_len + 10) >> 3) && s->strategy != Z_FIXED;
  if (!dynamic) { /* steer the search towards the dynamic branch */
    long gap = (long)((s->opt_len + 10) >> 3) - (long)((s->static_len + 10) >> 3) + 1;
    slack = 1000000 + (gap > 0 ? gap : 0);
    return;
  }
  dynBlocks1++;
  if (H + fx + 1 > fs + 5 * fdsum) fail("M5 choice row");
  if (delta1 > maxDelta1) maxDelta1 = delta1;
  { /* the largest header both rows allow at Delta = DELTA1, and the certificate's excess */
    long hrow = 71 + DELTA1 + C2 / 2, crow = fs + 5 * fdsum - fx - 1;
    long hstar = hrow < crow ? hrow : crow;
    long cert = 999 - (hstar + occExcess(ll, dl, fl, fd));
    if (cert < 0) fail("M7 certificate side");
    if (cert < minCert1) minCert1 = cert;
    long real = 1024 - 25 - (H + E);
    if (real < minReal1) minReal1 = real;
  }
  slack = 999 - (H + E);
  if (slack < 0) fail("M6 overlay budget");
  if (slack < minSlack1) minSlack1 = slack;
}

static void hook2(deflate_state *s) {
  int ll[287], dl[31], fl[286] = {0}, fd[30] = {0};
  int ml = s->l_desc.max_code, md = s->d_desc.max_code;
  /* scan_tree leaves its guard 0xffff at max_code + 1: lengths are read up to max_code only. */
  for (int v = 0; v < 286; v++) ll[v] = v <= ml ? s->dyn_ltree[v].Len : 0;
  for (int v = 0; v < 30; v++) dl[v] = v <= md ? s->dyn_dtree[v].Len : 0;
  for (int i = 0; i < nsym; i++) {
    if (cur[i].dist == 0) fl[cur[i].lc]++;
    else { fl[_length_code[cur[i].lc] + 257]++; fd[d_code(cur[i].dist - 1)]++; }
  }
  fl[256]++;
  built = 1; blocks++;
  long W = L + 2, kl = 0, kd = 0;
  for (int v = 0; v < 286; v++) {
    if (fl[v] && (ll[v] < 1 || ll[v] > 15 || fl[v] * fib[ll[v] + 1] + fib[ll[v]] > W)) fail("F1 literal tree");
    if (ll[v] && !fl[v] && v > 2) fail("F2 literal tree");
    if (ll[v]) kl += 1L << (15 - ll[v]);
    if (fl[v] && v > ml) fail("used code beyond max_code");
  }
  for (int v = 0; v < 30; v++) {
    if (fd[v] && (dl[v] < 1 || dl[v] > 15 || fd[v] * fib[dl[v] + 1] + fib[dl[v]] > W)) fail("F1 distance tree");
    if (dl[v] && !fd[v] && v > 2) fail("F2 distance tree");
    if (dl[v]) kd += 1L << (15 - dl[v]);
  }
  if (kl > 32768 || kd > 32768) fail("F3 Kraft");
  long f[19] = {0};
  scan(ll, ml, f); scan(dl, md, f);
  long hk = 0, delta = 0;
  for (int k = 0; k < 19; k++) { hk += f[k] * (K0[k] + blx[k]); delta += f[k] * (s->bl_tree[k].Len - K0[k]); }
  if (hk > entries_bound(ll, ml, 1) + entries_bound(dl, md, 0)) fail("F4 scan");
  long E = 0;
  for (int i = 0; i < nsym; i++) {
    long c;
    if (cur[i].dist == 0) c = ll[cur[i].lc];
    else { int lc = _length_code[cur[i].lc], dc = d_code(cur[i].dist - 1); c = ll[lc + 257] + xl[lc] + dl[dc] + xd[dc]; }
    if (c > 24) E += c - 24;
  }
  if (L == 128) { check128(s, ll, dl, fl, fd, ml, md, f, E); return; }
  { long ent = 0;
    for (int v = 0; v < 286; v++) ent += ENTRY2[ll[v]];
    for (int v = 0; v < 30; v++) ent += ENTRY2[dl[v]];
    long cert = 1852 - (71 + ent + occExcess(ll, dl, fl, fd));
    if (cert < 0) fail("F6 certificate side");
    if (cert < minCert2) minCert2 = cert;
    long asmb = 2048 - 25 - (71 + DELTA2 + hk + E);
    if (asmb < minAsm2) minAsm2 = asmb;
    int mb = 3;
    for (int k = 18; k >= 3; k--) if (s->bl_tree[blOrder[k]].Len != 0) { mb = k; break; }
    long H = 14 + 3L * (mb + 1);
    for (int k = 0; k < 19; k++) H += f[k] * (s->bl_tree[k].Len + blx[k]);
    int dynamic = ((s->static_len + 10) >> 3) > ((s->opt_len + 10) >> 3) && s->strategy != Z_FIXED;
    if (dynamic && 2048 - 25 - (H + E) < minReal2) minReal2 = 2048 - 25 - (H + E);
  }
  long sl = BOUND - (71 + hk + E);
  if (sl < 0) fail("F5 bound");
  slack = 1852 - (71 + occExcess(ll, dl, fl, fd));   /* the search minimises the certificate side */
  for (int v = 0; v < 286; v++) slack -= ENTRY2[ll[v]];
  for (int v = 0; v < 30; v++) slack -= ENTRY2[dl[v]];
  if (delta > maxDelta) maxDelta = delta;
}

static long run_block(sym *a, int n) {
  deflate_state *s;
  deflateReset(&strm);
  s = (deflate_state *)strm.state;
  strm.data_type = Z_BINARY;
  cur = a; nsym = n; built = 0;
  for (int i = 0; i < n; i++) {
    int fl;
    if (a[i].dist == 0) { _tr_tally_lit(s, (uch)a[i].lc, fl); }
    else { _tr_tally_dist(s, (unsigned)a[i].dist, (unsigned)a[i].lc, fl); }
    (void)fl;
  }
  s->pending = 0; s->bi_valid = 0; s->bi_buf = 0;
  _tr_flush_block(s, NULL, 0, 0);
  return built ? slack : 1L << 40;
}

static int build(const hist *h, sym *a) {
  int n = 0, lens[512], dsts[512], nl = 0, nd = 0;
  for (int c = 28; c >= 0; c--) for (int k = 0; k < h->len[c]; k++) lens[nl++] = c;
  for (int c = 29; c >= 0; c--) for (int k = 0; k < h->dst[c]; k++) dsts[nd++] = c;
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

static unsigned long long rs = 88172645463325252ULL;
static unsigned long long rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int total(const hist *h) { int n = 0; for (int v = 0; v < 256; v++) n += h->lit[v]; for (int c = 0; c < 29; c++) n += h->len[c]; return n; }

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

int main(int argc, char **argv) {
  if (argc < 3) { fprintf(stderr, "usage: check search <rounds> <seed> | replay <file>\n"); return 2; }
  fib[0] = 0; fib[1] = 1; for (int i = 2; i < 40; i++) fib[i] = fib[i - 1] + fib[i - 2];
  memset(&strm, 0, sizeof strm);
  int memLevel = getenv("MEMLEVEL") ? atoi(getenv("MEMLEVEL")) : 2;
  if (deflateInit2(&strm, 6, Z_DEFLATED, 15, memLevel, Z_DEFAULT_STRATEGY) != Z_OK) return 2;
  L = ((deflate_state *)strm.state)->lit_bufsize;
  if (L != (memLevel == 1 ? 128 : 256)) return 2;
  g_hook2 = hook2;
  sym *a = malloc(sizeof(sym) * 1024);
  if (!strcmp(argv[1], "replay")) {
    int n = 0; FILE *f = fopen(argv[2], "r"); if (!f) return 2;
    while (n < 1024 && fscanf(f, "%d %d", &a[n].dist, &a[n].lc) == 2) n++;
    fclose(f);
    long s = run_block(a, n);
    printf("replay %s: slack %ld bits, repair excess %ld\n", argv[2], s, L == 128 ? maxDelta1 : maxDelta);
    return 0;
  }
  long rounds = atol(argv[2]);
  rs ^= (unsigned long long)atol(argc > 3 ? argv[3] : "1") * 0x9E3779B97F4A7C15ULL;
  for (int i = 0; i < 20; i++) rnd();
  hist h, curh, bh; long bs = 1L << 40;
  memset(&curh, 0, sizeof curh);
  for (int i = 0; i < 64; i++) curh.lit[(i * 7) % 256]++;
  if (L == 128 || getenv("DYNSTART")) { /* cheap matches pay for the header, so the dynamic branch is taken */
    memset(&curh, 0, sizeof curh);
    for (int i = 0; i < 40; i++) curh.lit[(i * 5) % 256]++;
    curh.len[28] += 60; curh.dst[0] += 60;
  }
  int n = build(&curh, a); bs = run_block(a, n); bh = curh;
  long cs = bs; double T = 30;
  for (long it = 0; it < rounds; it++) {
    h = curh; int k = 1 + rnd() % 3;
    for (int j = 0; j < k; j++) mutate(&h);
    if (total(&h) > L - 1) continue;
    n = build(&h, a); if (n < 1) continue;
    long s = run_block(a, n);
    if (s <= cs || (double)(rnd() % 1000000) / 1e6 < exp((double)(cs - s) / T)) { curh = h; cs = s; }
    if (s < bs) { bs = s; bh = h; }
    T *= 0.99997; if (T < 0.5) T = 0.5;
  }
  n = build(&bh, a);
  if (L == 128)
    printf("search (memLevel 1): %ld blocks, %ld dynamic, smallest overlay slack %ld bits (budget 999), largest repair excess against kappa1 %ld;"
           " exact sides: certificate (worst header of both rows at Delta %d) %ld, real header %ld\n",
           blocks, dynBlocks1, minSlack1, maxDelta1, DELTA1, minCert1, minReal1);
  else
    printf("search: %ld blocks, smallest slack %ld bits (bound %d), largest repair excess %ld;"
           " exact sides: certificate (1852) %ld, assembly at Delta %d (2023) %ld, real dynamic header %ld\n",
           blocks, bs, BOUND, maxDelta, minCert2, DELTA2, minAsm2, minReal2);
  for (int i = 0; i < n; i++) fprintf(stderr, "%d %d\n", a[i].dist, a[i].lc);
  return 0;
}
