/* Statement test for Goal.inflate_refusal and Goal.deflate_refusal on the real C.
 * Every refused stream of the goals' domain is handed to every function of the family:
 *  - a NULL stream;
 *  - a record with no state: zeroed, after End, after a failed init, the destination of a failed copy;
 *  - a record with a null zalloc or a null zfree and a live state;
 *  - a record whose state belongs to another record (a struct copy: wrong back pointer).
 * Each call must return Z_STREAM_ERROR, leave the record unchanged (the copy functions: clear
 * dest->state and nothing else), and allocate nothing. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "zlib.h"

static long live, bad, calls;
static unsigned failat = 0, ncalls;
static voidpf al(voidpf o, uInt n, uInt s) {
    (void)o;
    if (failat && ++ncalls >= failat) return NULL;
    live++;
    return calloc(n, s);
}
static void fr(voidpf o, voidpf p) { (void)o; if (p) { live--; free(p); } }

static unsigned char outb[64], inb[64], dict[32768];

static void expect(const char *what, const char *kind, int rc, z_stream *z, const z_stream *before, long live0) {
    calls++;
    if (rc != Z_STREAM_ERROR || (z && memcmp(z, before, sizeof *z) != 0) || live != live0)
        if (bad++ < 20) printf("BAD %s on %s: rc %d live %ld/%ld\n", what, kind, rc, live, live0);
}

/* Build the refused records of one family. isInf = 1 for inflate, 0 for deflate. */
static int make(int isInf, int k, z_stream *z, z_stream *owner) {
    memset(z, 0, sizeof *z); z->zalloc = al; z->zfree = fr;
    z->next_out = outb; z->avail_out = sizeof outb; z->next_in = inb; z->avail_in = 0;
    switch (k) {
    case 0: return 1;                                         /* zeroed: no state */
    case 1:                                                   /* after End */
        if (isInf ? inflateInit(z) : deflateInit(z, 6)) return 0;
        isInf ? inflateEnd(z) : deflateEnd(z);
        return 1;
    case 2:                                                   /* after a failed init */
        failat = 1; ncalls = 0;
        { int rc = isInf ? inflateInit(z) : deflateInit(z, 6); failat = 0; if (rc != Z_MEM_ERROR) return 0; }
        return 1;
    case 3: {                                                 /* destination of a failed copy */
        z_stream src; memset(&src, 0, sizeof src); src.zalloc = al; src.zfree = fr;
        if (isInf ? inflateInit(&src) : deflateInit(&src, 6)) return 0;
        failat = 1; ncalls = 0;
        int rc = isInf ? inflateCopy(z, &src) : deflateCopy(z, &src);
        failat = 0;
        isInf ? inflateEnd(&src) : deflateEnd(&src);
        if (rc != Z_MEM_ERROR) return 0;
        return 1;
    }
    case 4: case 5:                                           /* null zalloc / zfree, live state */
        if (isInf ? inflateInit(owner) : deflateInit(owner, 6)) return 0;
        *z = *owner;
        if (k == 4) z->zalloc = Z_NULL; else z->zfree = Z_NULL;
        return 2;
    case 6:                                                   /* a struct copy: the state's back pointer is another record */
        if (isInf ? inflateInit(owner) : deflateInit(owner, 6)) return 0;
        *z = *owner;
        return 2;
    }
    return 0;
}

static const char *kinds[] = {"zeroed", "after End", "after failed init", "failed-copy dest",
                              "null zalloc", "null zfree", "struct copy"};

int main(void) {
    for (int fam = 0; fam < 2; fam++) {
        int isInf = fam == 0;
        /* NULL stream */
        long live0 = live;
        if (isInf) {
            expect("inflate", "NULL", inflate(Z_NULL, Z_NO_FLUSH), NULL, NULL, live0);
            expect("inflateEnd", "NULL", inflateEnd(Z_NULL), NULL, NULL, live0);
            expect("inflateReset", "NULL", inflateReset(Z_NULL), NULL, NULL, live0);
            expect("inflateReset2", "NULL", inflateReset2(Z_NULL, 15), NULL, NULL, live0);
            uInt n = 0;
            expect("inflateGetDictionary", "NULL", inflateGetDictionary(Z_NULL, dict, &n), NULL, NULL, live0);
            expect("inflateSetDictionary", "NULL", inflateSetDictionary(Z_NULL, dict, 10), NULL, NULL, live0);
        } else {
            expect("deflate", "NULL", deflate(Z_NULL, Z_NO_FLUSH), NULL, NULL, live0);
            expect("deflateSetDictionary", "NULL", deflateSetDictionary(Z_NULL, dict, 10), NULL, NULL, live0);
            expect("deflateParams", "NULL", deflateParams(Z_NULL, 1, 0), NULL, NULL, live0);
            uInt n = 0;
            expect("deflateGetDictionary", "NULL", deflateGetDictionary(Z_NULL, dict, &n), NULL, NULL, live0);
        }
        for (int k = 0; k < 7; k++)
        for (int fn = 0; fn < 7; fn++)
        for (int flush = 0; flush <= 6; flush++) {
            if (fn != 0 && flush) continue;
            z_stream z, owner;
            memset(&owner, 0, sizeof owner); owner.zalloc = al; owner.zfree = fr;
            int m = make(isInf, k, &z, &owner);
            if (!m) { if (bad++ < 20) printf("setup failed %d %d\n", fam, k); continue; }
            z_stream before = z;
            long l0 = live;
            uInt n = 0;
            int rc = Z_OK, isCopy = 0;
            const char *name = "";
            if (isInf) switch (fn) {
                case 0: name = "inflate"; rc = inflate(&z, flush); break;
                case 1: name = "inflateEnd"; rc = inflateEnd(&z); break;
                case 2: name = "inflateReset"; rc = inflateReset(&z); break;
                case 3: name = "inflateReset2"; rc = inflateReset2(&z, 9 + flush); break;
                case 4: name = "inflateGetDictionary"; rc = inflateGetDictionary(&z, dict, &n); break;
                case 5: name = "inflateSetDictionary"; rc = inflateSetDictionary(&z, dict, 10); break;
                case 6: name = "inflateCopy"; isCopy = 1; break;
            } else switch (fn) {
                case 0: name = "deflate"; rc = deflate(&z, flush); break;
                case 1: name = "deflateSetDictionary"; rc = deflateSetDictionary(&z, dict, 10); break;
                case 2: name = "deflateParams"; rc = deflateParams(&z, 1 + flush, 0); break;
                case 3: name = "deflateGetDictionary"; rc = deflateGetDictionary(&z, dict, &n); break;
                case 4: name = "deflateEnd"; rc = deflateEnd(&z); break;
                case 5: name = "deflateReset"; rc = deflateReset(&z); break;
                case 6: name = "deflateCopy"; isCopy = 1; break;
            }
            if (isCopy) {
                z_stream dst; memset(&dst, 0x5a, sizeof dst);
                z_stream exp = dst; exp.state = NULL;
                rc = isInf ? inflateCopy(&dst, &z) : deflateCopy(&dst, &z);
                expect(name, kinds[k], rc, &dst, &exp, l0);
                if (memcmp(&z, &before, sizeof z) != 0 && bad++ < 20) printf("BAD %s changed its source (%s)\n", name, kinds[k]);
            } else {
                expect(name, kinds[k], rc, &z, &before, l0);
            }
            if (m == 2) isInf ? inflateEnd(&owner) : deflateEnd(&owner);
        }
    }
    printf("calls %ld bad %ld live %ld\n", calls, bad, live);
    return bad != 0 || live != 0;
}
