#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include "deflate.c"

_Static_assert(sizeof(long) * CHAR_BIT == 64, "this fixture targets LP64");

static void observe(long start) {
    z_stream z = {0};
    deflate_state d = {0};
    d.strm = &z;
    d.w_size = 512;
    d.w_mask = 511;
    d.window_size = 1024;
    d.hash_size = 256;
    d.strstart = 762;
    d.block_start = start;
    d.window = calloc(1024, 1);
    d.head = calloc(256, sizeof(Pos));
    d.prev = calloc(512, sizeof(Pos));
    if (!d.window || !d.head || !d.prev) exit(2);
    fill_window(&d);
    printf("block_start=%ld strstart=%u high_water=%lu\n",
           d.block_start, d.strstart, d.high_water);
    free(d.prev);
    free(d.head);
    free(d.window);
}

int main(int argc, char **argv) {
    (void)argv;
    if (argc > 1) {
        observe(LONG_MIN);
        return 0;
    }
    observe(0);
    observe(LONG_MIN + 512);
    observe(LONG_MAX);
    return 0;
}
