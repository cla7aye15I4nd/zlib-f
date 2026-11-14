/* Statement test for Goal.gz_refusal on the real C.
 * Every gz function of the goal is called with a NULL handle, with several values of its other
 * arguments. Each call must return its documented value, allocate and free nothing (malloc and free
 * hooks of the sanitizer allocator), leave errno and the open descriptors unchanged, and write no
 * caller buffer (gzerror leaves *errnum; gzread, gzfread and gzgets leave buf).
 * gzgetc is called as the function (gzgetc)(NULL): the gzgetc macro of zlib.h dereferences its
 * argument, so the macro on NULL is undefined behaviour. */
#define _LARGEFILE64_SOURCE 1
#include <errno.h>
#include <stdarg.h>
#include <stdio.h>
#include <string.h>
#include <unistd.h>
#include <sanitizer/allocator_interface.h>
#include "zlib.h"

#ifndef Z_LARGE64 /* the library defines the 64-bit functions even where zlib.h does not declare them */
ZEXTERN z_off64_t ZEXPORT gzseek64(gzFile, z_off64_t, int);
ZEXTERN z_off64_t ZEXPORT gztell64(gzFile);
ZEXTERN z_off64_t ZEXPORT gzoffset64(gzFile);
#endif

static long allocs, frees, calls, bad;
static void on_malloc(const volatile void *p, size_t n) { (void)p; (void)n; allocs++; }
static void on_free(const volatile void *p) { (void)p; frees++; }

static unsigned char buf[64], before[64];
static long a0, f0;
static int fd0;

/* The lowest free descriptor: a call that opened or closed one would change it. */
static int lowest_fd(void) { int d = dup(0); if (d >= 0) close(d); return d; }

static void start(void) {
    memset(buf, 0xa5, sizeof buf); memcpy(before, buf, sizeof buf);
    fd0 = lowest_fd(); a0 = allocs; f0 = frees;
    errno = 4242;
}

static void finish(const char *what, long got, long want) {
    int e = errno;
    long da = allocs - a0, df = frees - f0;
    calls++;
    if (got != want || e != 4242 || da != 0 || df != 0 || memcmp(buf, before, sizeof buf) != 0 ||
        lowest_fd() != fd0)
        if (bad++ < 40)
            printf("BAD %s: got %ld want %ld errno %d allocs %ld frees %ld\n", what, got, want, e, da, df);
}

static int vp(gzFile f, const char *fmt, ...) {
    va_list va; va_start(va, fmt);
    int r = gzvprintf(f, fmt, va);
    va_end(va);
    return r;
}

#define CHECK(what, expr, want) do { start(); long got_ = (long)(expr); finish(what, got_, (long)(want)); } while (0)

int main(void) {
    __sanitizer_install_malloc_and_free_hooks(on_malloc, on_free);
    unsigned lens[] = {0, 1, 63, 0x7fffffffu, 0x80000000u, 0xffffffffu};
    size_t sizes[] = {0, 1, 3, (size_t)-1};
    int ints[] = {-1, 0, 1, 4, 5, 9, 'a', 256, -2147483647 - 1, 2147483647};
    long offs[] = {0, 1, -1, 1000, -1000, 0x7fffffffffffffffL, -0x7fffffffffffffffL - 1};
    gzFile f = NULL;

    for (unsigned i = 0; i < sizeof lens / sizeof *lens; i++) {
        CHECK("gzread", gzread(f, buf, lens[i]), -1);
        CHECK("gzread NULL buf", gzread(f, NULL, lens[i]), -1);
        CHECK("gzwrite", gzwrite(f, buf, lens[i]), 0);
        CHECK("gzwrite NULL buf", gzwrite(f, NULL, lens[i]), 0);
        CHECK("gzbuffer", gzbuffer(f, lens[i]), -1);
    }
    for (unsigned i = 0; i < sizeof sizes / sizeof *sizes; i++)
        for (unsigned j = 0; j < sizeof sizes / sizeof *sizes; j++) {
            CHECK("gzfread", gzfread(buf, sizes[i], sizes[j], f), 0);
            CHECK("gzfwrite", gzfwrite(buf, sizes[i], sizes[j], f), 0);
        }
    for (unsigned i = 0; i < sizeof ints / sizeof *ints; i++) {
        int v = ints[i];
        CHECK("gzputc", gzputc(f, v), -1);
        CHECK("gzungetc", gzungetc(v, f), -1);
        CHECK("gzflush", gzflush(f, v), Z_STREAM_ERROR);
        CHECK("gzsetparams", gzsetparams(f, v, v), Z_STREAM_ERROR);
        CHECK("gzgets", gzgets(f, (char *)buf, v) != NULL, 0);
        CHECK("gzgets NULL buf", gzgets(f, NULL, v) != NULL, 0);
        CHECK("gzseek whence", gzseek(f, 0, v), -1);
        CHECK("gzseek64 whence", gzseek64(f, 0, v), -1);
    }
    for (unsigned i = 0; i < sizeof offs / sizeof *offs; i++)
        for (int w = 0; w < 3; w++) {
            CHECK("gzseek64", gzseek64(f, offs[i], w), -1);
            CHECK("gzseek", gzseek(f, offs[i], w), -1);
        }
    CHECK("gzputs", gzputs(f, "hello"), -1);
    CHECK("gzputs empty", gzputs(f, ""), -1);
    CHECK("gzprintf", gzprintf(f, "%d %s", 7, "x"), Z_STREAM_ERROR);
    CHECK("gzprintf plain", gzprintf(f, "plain"), Z_STREAM_ERROR);
    CHECK("gzvprintf", vp(f, "%d %s", 7, "x"), Z_STREAM_ERROR);
    CHECK("gzgetc", (gzgetc)(f), -1);
    CHECK("gzgetc_", gzgetc_(f), -1);
    CHECK("gzdirect", gzdirect(f), 0);
    CHECK("gztell", gztell(f), -1);
    CHECK("gztell64", gztell64(f), -1);
    CHECK("gzoffset", gzoffset(f), -1);
    CHECK("gzoffset64", gzoffset64(f), -1);
    CHECK("gzrewind", gzrewind(f), -1);
    CHECK("gzeof", gzeof(f), 0);
    {
        int errnum = 0x5a5a5a5a;
        CHECK("gzerror", gzerror(f, &errnum) != NULL, 0);
        if (errnum != 0x5a5a5a5a && bad++ < 40) printf("BAD gzerror wrote errnum %d\n", errnum);
        CHECK("gzerror NULL errnum", gzerror(f, NULL) != NULL, 0);
    }
    start(); gzclearerr(f); finish("gzclearerr", 0, 0);
    CHECK("gzclose", gzclose(f), Z_STREAM_ERROR);
    CHECK("gzclose_r", gzclose_r(f), Z_STREAM_ERROR);
    CHECK("gzclose_w", gzclose_w(f), Z_STREAM_ERROR);
    printf("calls %ld bad %ld\n", calls, bad);
    return bad != 0;
}
