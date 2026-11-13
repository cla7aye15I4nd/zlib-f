/* Test-only probe, not part of zlib. run.sh rewrites every "state->x.next += n;" in a copy
   of gzlib.c and gzread.c into "state->x.next += ZPROBE_NEXT(state->x.next, n);" and
   compiles that copy with -include probe.h. The probe returns n unchanged, so the
   library computes the same values; it only reports each evaluation of x.next. */
unsigned zprobe_next(const unsigned char *next, unsigned n, const char *file, int line);
#define ZPROBE_NEXT(p, n) zprobe_next((p), (n), __FILE__, __LINE__)
