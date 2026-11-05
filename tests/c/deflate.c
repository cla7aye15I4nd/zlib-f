/* C side of the differential test for deflate.c and compress.c (the exported functions of the REAL libz.a).
 * Input: one line per case, "session TOKEN..." or "compress ..." etc. (grammar: gen/deflate.py and
 * lean/Driver/Deflate.lean, which implements exactly the same). Output: one line per case. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <errno.h>
#include <zlib.h>

static unsigned char *hexdec(const char *s, size_t *n) {
    size_t l = strlen(s);
    if (l % 2) { fprintf(stderr, "odd hex\n"); exit(2); }
    unsigned char *b = malloc(l / 2 + 1);
    for (size_t i = 0; i < l / 2; i++) { unsigned v; if (sscanf(s + 2 * i, "%2x", &v) != 1) { fprintf(stderr, "bad hex\n"); exit(2); } b[i] = (unsigned char)v; }
    *n = l / 2;
    return b;
}
static void hexout(const unsigned char *b, size_t n) { for (size_t i = 0; i < n; i++) printf("%02x", b[i]); }

static z_stream *strm;
static unsigned char *inb, *outb;
static size_t N, fed, consumed, ocap;

static void state(int rc) {
    printf("%d,%u,%u,%lu,%lu,%lu,%d,%s", rc, strm->avail_in, strm->avail_out, strm->total_in, strm->total_out,
           strm->adler, strm->data_type, strm->msg ? strm->msg : "-");
}
static void feed(size_t ic) {
    fed += ic; if (fed > N) fed = N;
    strm->next_in = inb + consumed;
    strm->avail_in = (uInt)(fed - consumed);
}
static void after(void) { consumed = fed - strm->avail_in; }

static gz_header hdr;

static void session(char **tok, int nt) {
    strm = calloc(1, sizeof *strm);
    strm->zalloc = Z_NULL; strm->zfree = Z_NULL; strm->opaque = Z_NULL;
    inb = malloc(1); N = 0; fed = 0; consumed = 0; outb = NULL; ocap = 0;
    int ended = 0;
    for (int i = 0; i < nt; i++) {
        char *t = tok[i];
        if (!strncmp(t, "IN:", 3)) {
            free(inb); inb = hexdec(t + 3, &N);
            ocap = N + N / 2 + 4096; outb = calloc(ocap, 1);
            strm->next_out = outb; strm->avail_out = 0;
        } else if (!strncmp(t, "I1:", 3)) {
            int rc = deflateInit(strm, atoi(t + 3));
            printf("I=%d ", rc);
            if (rc) { printf("\n"); return; }
        } else if (!strncmp(t, "I:", 2)) {
            int lv, me, wb, mem, st; char fl = 0;
            const char *ver = ZLIB_VERSION; int ssz = (int)sizeof(z_stream);
            char buf[8]; int k = sscanf(t + 2, "%d:%d:%d:%d:%d:%1s", &lv, &me, &wb, &mem, &st, buf);
            if (k == 6) fl = buf[0];
            if (fl == 'v') ver = "0.9"; if (fl == 's') ssz = 111;
            int rc = deflateInit2_(strm, lv, me, wb, mem, st, ver, ssz);
            printf("I=%d ", rc);
            if (rc) { printf("\n"); return; }
        } else if (t[0] == 'D' && t[1] == ':') {
            int fl; unsigned ic, oc; sscanf(t + 2, "%d:%u:%u", &fl, &ic, &oc);
            size_t used = (size_t)(strm->next_out - outb);
            if (oc > ocap - used) oc = (unsigned)(ocap - used);
            feed(ic); strm->avail_out = oc;
            int rc = deflate(strm, fl); after();
            printf("D="); state(rc); printf(" ");
        } else if (t[0] == 'P' && t[1] == ':') {
            int lv, st; sscanf(t + 2, "%d:%d", &lv, &st);
            feed(0);
            int rc = deflateParams(strm, lv, st); after();
            printf("P="); state(rc); printf(" ");
        } else if (!strncmp(t, "S:", 2)) {
            size_t n; unsigned char *d = hexdec(t + 2, &n);
            int rc = deflateSetDictionary(strm, d, (uInt)n);
            printf("S=%d,%lu ", rc, strm->adler);
        } else if (!strcmp(t, "G")) {
            unsigned char *d = calloc(32768, 1); uInt len = 0;
            int rc = deflateGetDictionary(strm, d, &len);
            printf("G=%d,%u,", rc, len); hexout(d, rc == 0 ? len : 0); printf(" ");
        } else if (!strcmp(t, "R")) {
            int rc = deflateReset(strm);
            printf("R=%d ", rc);
        } else if (t[0] == 'K' && t[1] == ':') {
            int b, v; sscanf(t + 2, "%d:%d", &b, &v);
            printf("K=%d ", deflatePrime(strm, b, v));
        } else if (!strcmp(t, "C")) {
            z_stream *d = calloc(1, sizeof *d);
            int rc = deflateCopy(d, strm);
            printf("C=%d ", rc);
            if (rc == 0) { deflateEnd(strm); free(strm); strm = d; }
        } else if (!strcmp(t, "B")) {
            printf("B=%lu,%lu ", deflateBound(strm, (uLong)N), (unsigned long)deflateBound_z(strm, N));
        } else if (t[0] == 'T' && t[1] == ':') {
            int a, b, c, d; sscanf(t + 2, "%d:%d:%d:%d", &a, &b, &c, &d);
            printf("T=%d ", deflateTune(strm, a, b, c, d));
        } else if (!strcmp(t, "Q")) {
            unsigned p = 7; int b = 7; int rc = deflatePending(strm, &p, &b);
            printf("Q=%d,%u,%d ", rc, p, b);
        } else if (!strcmp(t, "U")) {
            int b = 7; int rc = deflateUsed(strm, &b);
            printf("U=%d,%d ", rc, b);
        } else if (t[0] == 'H' && t[1] == ':') {
            /* text:time:os:hcrc:extra:name:comment (hex or -) */
            char *f[7]; char *p = t + 2; int k = 0;
            while (k < 7) { f[k++] = p; char *c = strchr(p, ':'); if (!c) break; *c = 0; p = c + 1; }
            memset(&hdr, 0, sizeof hdr);
            hdr.text = atoi(f[0]); hdr.time = strtoul(f[1], 0, 10); hdr.os = atoi(f[2]); hdr.hcrc = atoi(f[3]);
            size_t n;
            if (strcmp(f[4], "-")) { hdr.extra = hexdec(f[4], &n); hdr.extra_len = (uInt)n; hdr.extra_max = (uInt)n; }
            if (strcmp(f[5], "-")) { unsigned char *s = hexdec(f[5], &n); s[n] = 0; hdr.name = s; hdr.name_max = (uInt)n + 1; }
            if (strcmp(f[6], "-")) { unsigned char *s = hexdec(f[6], &n); s[n] = 0; hdr.comment = s; hdr.comm_max = (uInt)n + 1; }
            printf("H=%d ", deflateSetHeader(strm, &hdr));
        } else if (!strcmp(t, "E")) {
            printf("E=%d ", deflateEnd(strm)); ended = 1;
        } else { fprintf(stderr, "bad token %s\n", t); exit(2); }
    }
    size_t used = outb ? (size_t)(strm->next_out - outb) : 0;
    if (!ended) { printf("E=%d ", deflateEnd(strm)); }
    printf("OUT="); if (outb) hexout(outb, used);
    printf("\n");
}

int main(void) {
    char *line = NULL; size_t cap = 0;
    while (getline(&line, &cap, stdin) > 0) {
        char *p = strchr(line, '\n'); if (p) *p = 0;
        if (!*line) continue;
        char *tok[1024]; int nt = 0;
        for (char *t = strtok(line, " "); t && nt < 1024; t = strtok(NULL, " ")) tok[nt++] = t;
        if (!strcmp(tok[0], "session")) session(tok + 1, nt - 1);
        else if (!strcmp(tok[0], "compress2") || !strcmp(tok[0], "compress") ||
                 !strcmp(tok[0], "compress2_z") || !strcmp(tok[0], "compress_z")) {
            /* compress2 <level> <destcap> <srchex> */
            int lv = atoi(tok[1]); unsigned long dc = strtoul(tok[2], 0, 10); size_t n;
            unsigned char *src = hexdec(tok[3] + 1, &n);
            unsigned char *dst = calloc(dc + 1, 1);
            int rc; uLongf dl = dc; z_size_t dlz = dc;
            if (!strcmp(tok[0], "compress2")) rc = compress2(dst, &dl, src, n, lv);
            else if (!strcmp(tok[0], "compress")) rc = compress(dst, &dl, src, n);
            else if (!strcmp(tok[0], "compress2_z")) { rc = compress2_z(dst, &dlz, src, n, lv); dl = dlz; }
            else { rc = compress_z(dst, &dlz, src, n); dl = dlz; }
            printf("%d,%lu,", rc, (unsigned long)dl); hexout(dst, dl <= dc ? dl : 0); printf("\n");
        } else if (!strcmp(tok[0], "bound")) {
            unsigned long long l = strtoull(tok[1], 0, 10);
            printf("%lu,%lu\n", compressBound((uLong)l), (unsigned long)compressBound_z((z_size_t)l));
        } else { fprintf(stderr, "bad case %s\n", tok[0]); return 2; }
    }
    return 0;
}
