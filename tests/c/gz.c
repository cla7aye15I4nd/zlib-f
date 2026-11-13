/* C side of the differential test for gzlib.c, gzread.c, gzwrite.c, gzclose.c, uncompr.c: links the REAL zlib.
 * Line: "gz OP OP ..." (a scenario on real temporary files) or "unc HEX DESTLEN [SRCLEN]" (uncompress2).
 * An OP is fields separated by ':'; see gen/gz.py for the list. Each OP appends one token to the output line,
 * the tokens are joined by '|'. Hex is lowercase. Every scenario runs in a fresh temporary directory. */
#define _GNU_SOURCE
#undef _FORTIFY_SOURCE /* the harness defines read() below; a fortified inline read() would clash */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <errno.h>
#include <unistd.h>
#include <fcntl.h>
#include <signal.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <sys/resource.h>
#include <sys/syscall.h>
#include "zlib.h"

static FILE *outf;

/* "rfail:H:E": the next read() of the library fails with errno E (the model side sets the read oracle of that call
 * to fail with E). This definition interposes on the read() that the statically linked zlib calls; the harness's
 * own stdio does not go through it. */
static int read_fail_errno;
ssize_t read(int fd, void *buf, size_t n) {
    if (read_fail_errno) { errno = read_fail_errno; read_fail_errno = 0; return -1; }
    return syscall(SYS_read, fd, buf, n);
}
#define printf(...) fprintf(outf, __VA_ARGS__)

static int hexv(int c) { return c >= '0' && c <= '9' ? c - '0' : c >= 'a' && c <= 'f' ? c - 'a' + 10 : c >= 'A' && c <= 'F' ? c - 'A' + 10 : -1; }
static unsigned char *unhex(const char *s, size_t *n) {
    size_t l = strlen(s);
    if (l % 2) { fprintf(stderr, "odd hex\n"); exit(2); }
    unsigned char *b = malloc(l / 2 + 1);
    for (size_t i = 0; i < l / 2; i++) {
        int a = hexv(s[2 * i]), c = hexv(s[2 * i + 1]);
        if (a < 0 || c < 0) { fprintf(stderr, "bad hex\n"); exit(2); }
        b[i] = (unsigned char)(a * 16 + c);
    }
    *n = l / 2;
    return b;
}
static void puthex(const unsigned char *b, size_t n) { for (size_t i = 0; i < n; i++) printf("%02x", b[i]); }
static long long num(const char *s) {
    char *e; errno = 0; long long v = strtoll(s, &e, 10);
    if (*s == '\0' || *e != '\0' || errno) { fprintf(stderr, "bad number %s\n", s); exit(2); }
    return v;
}

#define NH 4
static gzFile hs[NH];
static int hdir[NH];      /* harness bookkeeping: 0 = none, 1 = read, 2 = write (as gz_open parses) */
static gzFile orph[4096]; /* handles the harness still owns but no longer tracks in hs[] */
static int norph;

static void orphan(gzFile g) {
    if (!g) return;
    if (norph == (int)(sizeof orph / sizeof *orph)) {
        fprintf(stderr, "too many test-owned gz handles\n"); exit(2);
    }
    orph[norph++] = g;
}

/* the direction gz_open() itself derives from the mode string: the last of r/w/a wins */
static int mode_dir(const char *m) {
    int d = 0;
    for (; *m; m++) {
        if (*m == 'r') d = 1;
        else if (*m == 'w' || *m == 'a') d = 2;
    }
    return d;
}

/* the printf formats: index -> format; arguments are typed by the format */
static int do_printf(gzFile f, int k, char **a, int na) {
    long long v[4]; size_t n; unsigned char *sb[4] = {0};
    for (int i = 0; i < na && i < 4; i++) {
        if (a[i][0] == 's') { sb[i] = unhex(a[i] + 1, &n); sb[i][n] = 0; v[i] = 0; }
        else v[i] = num(a[i] + 1);
    }
    int r;
    switch (k) {
    case 0: r = gzprintf(f, "hello"); break;
    case 1: r = gzprintf(f, "%d", (int)v[0]); break;
    case 2: r = gzprintf(f, "[%5d|%-5d|%05d]", (int)v[0], (int)v[1], (int)v[2]); break;
    case 3: r = gzprintf(f, "%s=%s", sb[0], sb[1]); break;
    case 4: r = gzprintf(f, "%u %x %X %o", (unsigned)v[0], (unsigned)v[1], (unsigned)v[2], (unsigned)v[3]); break;
    case 5: r = gzprintf(f, "%ld %lu", (long)v[0], (unsigned long)v[1]); break;
    case 6: r = gzprintf(f, "%c%c", (int)v[0], (int)v[1]); break;
    case 7: r = gzprintf(f, "%.3s|%10s|%-10s|", sb[0], sb[1], sb[2]); break;
    case 8: r = gzprintf(f, "%+d % d %%", (int)v[0], (int)v[1]); break;
    case 9: r = gzprintf(f, "%s", ""); break;
    case 10: r = gzprintf(f, "%#x %#o", (unsigned)v[0], (unsigned)v[1]); break;
    case 11: r = gzprintf(f, "%s", sb[0]); break;
    case 12: r = gzprintf(f, "%.0d|%.5d", (int)v[0], (int)v[1]); break;
    /* a failing vsnprintf: glibc returns -1 (EOVERFLOW); the model side uses "%d" with its oracle failing */
    case 13: r = gzprintf(f, "%3000000000d", (int)v[0]); break;
    default: fprintf(stderr, "bad format index\n"); exit(2);
    }
    for (int i = 0; i < 4; i++) free(sb[i]);
    return r;
}

static void op(char *o) {
    char *f[8]; int nf = 0; char *save;
    for (char *t = strtok_r(o, ":", &save); t && nf < 8; t = strtok_r(NULL, ":", &save)) f[nf++] = t;
    /* empty fields are not allowed (use '-' for an empty hex string) */
    const char *c = f[0];
    int h = nf > 1 && strcmp(c, "put") && strcmp(c, "mkdir") && strcmp(c, "dump") && strcmp(c, "fsize") ? (int)num(f[1]) : 0;
    gzFile g = (h >= 0 && h < NH) ? hs[h] : NULL;
    size_t n;
    unsigned char *b;
    if (!strcmp(c, "put")) {            /* put:NAME:HEX */
        b = (strcmp(f[2], "-") ? unhex(f[2], &n) : (n = 0, malloc(1)));
        FILE *fp = fopen(f[1], "wb"); if (n) fwrite(b, 1, n, fp); fclose(fp); free(b); printf("p");
    } else if (!strcmp(c, "mkdir")) { mkdir(f[1], 0777); printf("d");
    } else if (!strcmp(c, "fsize")) {
        struct rlimit rl; rl.rlim_max = RLIM_INFINITY;
        long long v = num(f[1]); rl.rlim_cur = v ? (rlim_t)v : RLIM_INFINITY;
        signal(SIGXFSZ, SIG_IGN); setrlimit(RLIMIT_FSIZE, &rl); printf("z");
    } else if (!strcmp(c, "dump")) {    /* dump:NAME */
        FILE *fp = fopen(f[1], "rb");
        if (!fp) printf("=-"); else {
            unsigned char buf[65536]; size_t k; printf("=");
            while ((k = fread(buf, 1, sizeof buf, fp)) > 0) puthex(buf, k);
            fclose(fp);
        }
    } else if (!strcmp(c, "open")) {    /* open:H:NAME:MODE */
        orphan(hs[h]);
        hs[h] = gzopen(f[2], f[3]); hdir[h] = hs[h] != NULL ? mode_dir(f[3]) : 0; printf("o%d", hs[h] != NULL);
    } else if (!strcmp(c, "dopen")) {   /* dopen:H:NAME:K:MODE  K = r w a c, or "bad" for fd -1 */
        int fd;
        if (!strcmp(f[3], "bad")) fd = -1;
        else {
            int fl = !strcmp(f[3], "r") ? O_RDONLY : !strcmp(f[3], "w") ? (O_WRONLY | O_CREAT | O_TRUNC)
                   : !strcmp(f[3], "a") ? (O_WRONLY | O_CREAT | O_APPEND) : (O_WRONLY | O_CREAT);
            fd = open(f[2], fl, 0666);
        }
        orphan(hs[h]);
        hs[h] = gzdopen(fd, f[4]); hdir[h] = hs[h] != NULL ? mode_dir(f[4]) : 0; printf("D%d", hs[h] != NULL);
    } else if (!strcmp(c, "buffer")) { printf("b%d", gzbuffer(g, (unsigned)num(f[2])));
    } else if (!strcmp(c, "write")) {   /* write:H:HEX */
        b = strcmp(f[2], "-") ? unhex(f[2], &n) : (n = 0, malloc(1));
        printf("w%d", gzwrite(g, b, (unsigned)n)); free(b);
    } else if (!strcmp(c, "fwrite")) {  /* fwrite:H:SIZE:HEX */
        b = strcmp(f[3], "-") ? unhex(f[3], &n) : (n = 0, malloc(1)); size_t sz = (size_t)num(f[2]);
        printf("W%zu", gzfwrite(b, sz, sz ? n / sz : 0, g)); free(b);
    } else if (!strcmp(c, "putc")) { printf("c%d", gzputc(g, (int)num(f[2])));
    } else if (!strcmp(c, "puts")) {    /* puts:H:HEX (no NUL inside) */
        b = strcmp(f[2], "-") ? unhex(f[2], &n) : (n = 0, malloc(1)); b[n] = 0; printf("s%d", gzputs(g, (char *)b)); free(b);
    } else if (!strcmp(c, "printf")) { printf("f%d", do_printf(g, (int)num(f[2]), f + 3, nf - 3));
    } else if (!strcmp(c, "flush")) { printf("F%d", gzflush(g, (int)num(f[2])));
    } else if (!strcmp(c, "setparams")) { printf("P%d", gzsetparams(g, (int)num(f[2]), (int)num(f[3])));
    } else if (!strcmp(c, "read")) {    /* read:H:N */
        unsigned len = (unsigned)num(f[2]); b = malloc(len ? len : 1);
        int r = gzread(g, b, len); printf("r%d:", r); if (r > 0) puthex(b, (size_t)r); free(b);
    } else if (!strcmp(c, "fread")) {   /* fread:H:SIZE:N */
        size_t sz = (size_t)num(f[2]), ni = (size_t)num(f[3]); b = malloc(sz * ni ? sz * ni : 1);
        size_t r = gzfread(b, sz, ni, g); printf("R%zu:", r); puthex(b, r * sz); free(b);
    } else if (!strcmp(c, "gets")) {    /* gets:H:LEN */
        int len = (int)num(f[2]); char *s = malloc(len > 0 ? (size_t)len : 1);
        char *r = gzgets(g, s, len); printf("g"); if (!r) printf("N"); else puthex((unsigned char *)s, strlen(s)); free(s);
    } else if (!strcmp(c, "getc")) { printf("C%d", (gzgetc)(g));
    } else if (!strcmp(c, "ungetc")) { printf("u%d", gzungetc((int)num(f[2]), g));
    } else if (!strcmp(c, "seek")) { printf("S%lld", (long long)gzseek(g, (z_off_t)num(f[2]), (int)num(f[3])));
    } else if (!strcmp(c, "tell")) { printf("T%lld", (long long)gztell(g));
    } else if (!strcmp(c, "offset")) { printf("O%lld", (long long)gzoffset(g));
    } else if (!strcmp(c, "rewind")) { printf("rw%d", gzrewind(g));
    } else if (!strcmp(c, "eof")) { printf("E%d", gzeof(g));
    } else if (!strcmp(c, "direct")) { printf("Di%d", gzdirect(g));
    } else if (!strcmp(c, "error")) {
        int e = 12345; const char *m = gzerror(g, &e); printf("e%d:", e); if (m) puthex((const unsigned char *)m, strlen(m));
    } else if (!strcmp(c, "clearerr")) { gzclearerr(g); printf("ce");
    } else if (!strcmp(c, "rfail")) { read_fail_errno = (int)num(f[2]); printf("rf");
    } else if (!strcmp(c, "close")) {  /* a non-NULL handle is always freed, whatever it returns */
        int r = gzclose(g); printf("x%d", r);
        if (g) { hs[h] = NULL; hdir[h] = 0; }          /* freed: drop ownership */
    } else if (!strcmp(c, "closer")) { /* frees only when the handle really is a read handle */
        int r = gzclose_r(g); printf("xr%d", r);
        if (g && hdir[h] != 1) orphan(g);              /* wrong mode: still ours, close later */
        hs[h] = NULL; hdir[h] = 0;
    } else if (!strcmp(c, "closew")) { /* frees only when the handle really is a write handle */
        int r = gzclose_w(g); printf("xw%d", r);
        if (g && hdir[h] != 2) orphan(g);              /* wrong mode: still ours, close later */
        hs[h] = NULL; hdir[h] = 0;
    } else { fprintf(stderr, "unknown op %s\n", c); printf("BADINPUT"); exit(2); }
}

int main(void) {
    char *line = NULL; size_t cap = 0; ssize_t got;
    char home[4096]; if (!getcwd(home, sizeof home)) return 2;
    while ((got = getline(&line, &cap, stdin)) >= 0) {
        char *save, *tok[4096]; int nt = 0;
        for (char *t = strtok_r(line, " \t\r\n", &save); t && nt < 4096; t = strtok_r(NULL, " \t\r\n", &save)) tok[nt++] = t;
        if (nt == 0) continue;
        char *obuf = NULL; size_t osz = 0;
        outf = open_memstream(&obuf, &osz);
        if (!strcmp(tok[0], "gz")) {
            char tmpl[] = "/tmp/gzdiffXXXXXX"; if (!mkdtemp(tmpl)) return 2;
            if (chdir(tmpl)) return 2;
            memset(hs, 0, sizeof hs); memset(hdir, 0, sizeof hdir); norph = 0;
            for (int i = 1; i < nt; i++) { if (i > 1) printf("|"); op(tok[i]); }
            printf("\n");
            /* close still-open handles only after every operation and output token */
            for (int i = 0; i < NH; i++) { orphan(hs[i]); hs[i] = NULL; hdir[i] = 0; }
            for (int i = 0; i < norph; i++) { gzclose(orph[i]); orph[i] = NULL; }
            norph = 0;
            for (int fd = 3; fd < 256; fd++) close(fd);
            struct rlimit rl = { RLIM_INFINITY, RLIM_INFINITY }; setrlimit(RLIMIT_FSIZE, &rl);
            if (chdir(home)) return 2;
            char cmd[4200]; snprintf(cmd, sizeof cmd, "rm -rf %s", tmpl); if (system(cmd)) return 2;
        } else if (!strcmp(tok[0], "unc") && nt >= 3) {   /* unc HEX DESTLEN [SRCLEN] */
            size_t n; unsigned char *src = strcmp(tok[1], "-") ? unhex(tok[1], &n) : (n = 0, malloc(1));
            uLong dl = (uLong)num(tok[2]), sl = nt > 3 ? (uLong)num(tok[3]) : (uLong)n;
            unsigned char *dst = malloc(dl ? dl : 1); uLong dl0 = dl;
            int r = uncompress2(dst, &dl, src, &sl);
            printf("%d:%lu:%lu:", r, dl, sl); puthex(dst, dl <= dl0 ? dl : 0); printf("\n"); free(src); free(dst);
        } else { fprintf(stderr, "unknown line %s\n", tok[0]); printf("BADINPUT\n"); return 1; }
        fclose(outf);
        { struct rlimit rl2 = { RLIM_INFINITY, RLIM_INFINITY }; setrlimit(RLIMIT_FSIZE, &rl2); }
        fwrite(obuf, 1, osz, stdout); fflush(stdout); free(obuf);
    }
    free(line);
    return 0;
}
