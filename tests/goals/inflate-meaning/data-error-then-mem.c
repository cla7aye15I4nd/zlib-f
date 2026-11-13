/* A raw stream rejected with Z_DATA_ERROR before any window exists, then a raw
 * inflateSetDictionary whose window allocation fails: the call returns
 * Z_MEM_ERROR and the decoder is in MEM while the last inflate result is still
 * Z_DATA_ERROR. So ParseMeaning cannot claim `result = Z_DATA_ERROR -> mode = BAD`;
 * MEM is possible on exactly this path (raw wrapper, allocation failure).
 * A wrapped stream refuses inflateSetDictionary outside DICT, so it cannot get there.
 * Build against the patched copy made by tests/build-zlib.sh. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "zlib.h"
#include "zutil.h"
#include "inftrees.h"
#include "inflate.h"

static int allow = 1;
static voidpf alloc_test(voidpf opaque, uInt items, uInt size) {
    (void)opaque;
    return allow ? calloc(items, size) : Z_NULL;
}
static void free_test(voidpf opaque, voidpf p) { (void)opaque; free(p); }

int main(void) {
    z_stream s;
    memset(&s, 0, sizeof s);
    s.zalloc = alloc_test; s.zfree = free_test;
    if (inflateInit2(&s, -15) != Z_OK) return 2;
    unsigned char in[1] = {0x07};          /* BFINAL = 1, BTYPE = 3: invalid block type */
    unsigned char out[16];
    s.next_in = in; s.avail_in = 1; s.next_out = out; s.avail_out = sizeof out;
    int rc1 = inflate(&s, Z_NO_FLUSH);
    struct inflate_state *st = (struct inflate_state *)s.state;
    printf("inflate rc=%d (Z_DATA_ERROR=%d) mode=%d (BAD=%d) window=%s\n", rc1, Z_DATA_ERROR,
           st->mode, BAD, st->window ? "allocated" : "null");
    unsigned char dict[3] = {1, 2, 3};
    allow = 0;                             /* the next allocation fails */
    int rc2 = inflateSetDictionary(&s, dict, 3);
    printf("inflateSetDictionary rc=%d (Z_MEM_ERROR=%d) mode=%d (MEM=%d)\n", rc2, Z_MEM_ERROR,
           st->mode, MEM);
    int mem = st->mode == MEM;
    allow = 1;
    inflateEnd(&s);
    return !(rc1 == Z_DATA_ERROR && rc2 == Z_MEM_ERROR && mem);
}
