/* C side of the differential test for trees.c. It #includes the REAL trees.c of the patched copy of zlib
 * (so that the `local` functions can be called as well as the exported ones), and links libz.a for the rest.
 * Input and output formats: see tests/README.md, tests/gen/trees.py and tests/lean/Driver/Trees.lean.
 *
 * Every case builds a deflate_state like deflate.c does (pending_buf of 4*lit_bufsize bytes plus a slack,
 * sym_buf = pending_buf + lit_bufsize, sym_end = (lit_bufsize-1)*3, _tr_init), runs one operation and prints
 * a one-line dump of the state: the bit buffer, the pending output (hex), the counters, and a 64-bit FNV-1a
 * hash of each tree and of heap, depth, bl_count. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <errno.h>
#include <trees.c>  /* angle brackets: the one in the -I directory (the patched zlib), not this file */

#define SLACK 1024

static deflate_state *cur_state;   /* freed after each case, so that LeakSanitizer stays quiet */
static unsigned char *cur_buf;

static unsigned long long parse_u(const char *s) {
    char *e; errno = 0;
    unsigned long long v = strtoull(s, &e, 10);
    if (*s == '\0' || *e != '\0' || errno || *s == '-') { fprintf(stderr, "bad unsigned %s\n", s); exit(2); }
    return v;
}
static long long parse_i(const char *s) {
    char *e; errno = 0;
    long long v = strtoll(s, &e, 10);
    if (*s == '\0' || *e != '\0' || errno) { fprintf(stderr, "bad signed %s\n", s); exit(2); }
    return v;
}

static deflate_state *mk(unsigned lit, int level, int strategy, int data_type, unsigned bi_buf, int bi_valid,
                         unsigned long pend0) {
    deflate_state *s = calloc(1, sizeof *s);
    cur_state = s;
    z_stream *z = calloc(1, sizeof *z);
    z->data_type = data_type;
    s->strm = z;
    s->pending_buf = calloc(4 * (size_t)lit + SLACK, 1);
    s->pending_buf_size = 4 * (ulg)lit;
    s->pending = pend0;
    s->lit_bufsize = lit;
    s->sym_buf = s->pending_buf + lit;
    s->sym_end = (lit - 1) * 3;
    s->level = level;
    s->strategy = strategy;
    /* stale values that _tr_init and init_block must reset */
    s->bi_buf = 0x1234; s->bi_valid = 9; s->bi_used = 5;
    s->opt_len = 77; s->static_len = 88; s->sym_next = 5; s->matches = 6;
    s->dyn_ltree[3].Freq = 9; s->dyn_ltree[285].Freq = 2; s->dyn_ltree[END_BLOCK].Freq = 7;
    s->dyn_dtree[29].Freq = 3; s->bl_tree[18].Freq = 4;
    for (int i = 0; i <= MAX_BITS; i++) s->bl_count[i] = (ush)(i + 3);
    s->heap_len = 5; s->heap_max = 7;
    _tr_init(s);
    if (bi_valid != -99) { s->bi_buf = (ush)bi_buf; s->bi_valid = bi_valid; }  /* -99: keep what _tr_init left */
    return s;
}

static unsigned long long fnv(unsigned long long h, unsigned v) {
    for (int i = 0; i < 4; i++) { h ^= (v >> (8 * i)) & 0xff; h *= 1099511628211ULL; }
    return h;
}
static unsigned long long hash_tree(const ct_data *t, int n) {
    unsigned long long h = 14695981039346656037ULL;
    for (int i = 0; i < n; i++) { h = fnv(h, t[i].Code); h = fnv(h, t[i].Len); }
    return h;
}
static void dump(deflate_state *s) {
    printf("P=%lu O=", (unsigned long)s->pending);
    for (ulg i = 0; i < s->pending; i++) printf("%02x", s->pending_buf[i]);
    printf(" B=%u,%d,%d L=%lu,%lu S=%u,%u H=%d,%d D=%d M=%d,%d,%d", (unsigned)s->bi_buf, s->bi_valid, s->bi_used,
           (unsigned long)s->opt_len, (unsigned long)s->static_len, s->sym_next, s->matches, s->heap_len,
           s->heap_max, s->strm->data_type, s->l_desc.max_code, s->d_desc.max_code, s->bl_desc.max_code);
    printf(" TL=%016llx TD=%016llx TB=%016llx", hash_tree(s->dyn_ltree, HEAP_SIZE), hash_tree(s->dyn_dtree, 2 * D_CODES + 1),
           hash_tree(s->bl_tree, 2 * BL_CODES + 1));
    unsigned long long h = 14695981039346656037ULL;
    for (int i = 0; i < HEAP_SIZE; i++) h = fnv(h, (unsigned)s->heap[i]);
    printf(" HP=%016llx", h);
    h = 14695981039346656037ULL;
    for (int i = 0; i < HEAP_SIZE; i++) h = fnv(h, s->depth[i]);
    printf(" DP=%016llx BC=", h);
    for (int i = 0; i <= MAX_BITS; i++) printf(i ? ",%u" : "%u", s->bl_count[i]);
}

/* "i:v,a-b:v" or "-": calls set(i, v) */
static void parse_spec(char *spec, void (*set)(void *, long, long), void *ctx) {
    if (strcmp(spec, "-") == 0) return;
    for (char *tok = strtok(spec, ","); tok; tok = strtok(NULL, ",")) {
        char *colon = strchr(tok, ':');
        if (!colon) { fprintf(stderr, "bad spec\n"); exit(2); }
        *colon = 0;
        long v = (long)parse_i(colon + 1);
        char *dash = strchr(tok + 1, '-');
        if (dash) { *dash = 0; for (long i = parse_i(tok); i <= parse_i(dash + 1); i++) set(ctx, i, v); }
        else set(ctx, parse_i(tok), v);
    }
}
static void set_fc(void *c, long i, long v) { ((ct_data *)c)[i].Freq = (ush)v; }
static void set_len(void *c, long i, long v) { ((ct_data *)c)[i].Len = (ush)v; }

/* symbols: l<lc>[*n] | m<dist>:<lc>[*n], separated by commas, or "-" */
static unsigned tally_all(deflate_state *s, char *spec, char *rets, size_t cap) {
    unsigned cnt = 0;
    if (strcmp(spec, "-") == 0) return 0;
    for (char *tok = strtok(spec, ","); tok; tok = strtok(NULL, ",")) {
        unsigned long n = 1;
        char *star = strchr(tok, '*');
        if (star) { *star = 0; n = parse_u(star + 1); }
        unsigned dist = 0, lc;
        if (tok[0] == 'l') lc = (unsigned)parse_u(tok + 1);
        else { char *c = strchr(tok, ':'); *c = 0; dist = (unsigned)parse_u(tok + 1); lc = (unsigned)parse_u(c + 1); }
        for (unsigned long i = 0; i < n; i++) {
            int r = _tr_tally(s, dist, lc);
            if (cnt < cap - 1) { rets[cnt] = '0' + r; rets[cnt + 1] = 0; }
            cnt++;
        }
    }
    return cnt;
}

static unsigned char *mkbuf(const char *spec, unsigned long len, int *isnull) {
    *isnull = 0;
    if (strcmp(spec, "null") == 0) { *isnull = 1; return NULL; }
    unsigned char *b = malloc(len ? len : 1);
    cur_buf = b;
    for (unsigned long i = 0; i < len; i++) b[i] = (unsigned char)((i * 7 + 3) & 0xff);
    return b;
}

int main(void) {
    char *line = NULL; size_t cap = 0;
    while (getline(&line, &cap, stdin) > 0) {
        char *save = NULL, *tk[16]; int nt = 0;
        for (char *t = strtok_r(line, " \r\n", &save); t && nt < 16; t = strtok_r(NULL, " \r\n", &save)) tk[nt++] = t;
        if (nt == 0) continue;
        const char *op = tk[0];
        if (!strcmp(op, "bi_reverse") && nt == 3) {
            printf("%u", bi_reverse((unsigned)parse_u(tk[1]), (int)parse_i(tk[2])));
        } else if (!strcmp(op, "sendbits") && nt == 5) { /* bi_buf bi_valid pend0 v:l,v:l */
            deflate_state *s = mk(16, 1, 0, 0, (unsigned)parse_u(tk[1]), (int)parse_i(tk[2]), parse_u(tk[3]));
            if (strcmp(tk[4], "-"))
                for (char *t = strtok(tk[4], ","); t; t = strtok(NULL, ",")) {
                    char *c = strchr(t, ':'); *c = 0;
                    int v = (int)parse_i(t), l = (int)parse_i(c + 1);
                    send_bits(s, v, l);
                }
            dump(s);
        } else if (!strcmp(op, "bitop") && nt == 5) { /* name bi_buf bi_valid pend0 */
            deflate_state *s = mk(16, 1, 0, 0, (unsigned)parse_u(tk[2]), (int)parse_i(tk[3]), parse_u(tk[4]));
            if (!strcmp(tk[1], "windup")) bi_windup(s);
            else if (!strcmp(tk[1], "flush")) bi_flush(s);
            else if (!strcmp(tk[1], "flushbits")) _tr_flush_bits(s);
            else if (!strcmp(tk[1], "align")) _tr_align(s);
            else { fprintf(stderr, "bad bitop\n"); return 2; }
            dump(s);
        } else if (!strcmp(op, "stored") && nt == 7) { /* bi_buf bi_valid pend0 last buf len */
            unsigned long len = parse_u(tk[6]);
            deflate_state *s = mk((unsigned)(len / 2 + 16), 1, 0, 0, (unsigned)parse_u(tk[1]), (int)parse_i(tk[2]), parse_u(tk[3]));
            int isnull; unsigned char *b = mkbuf(tk[5], len, &isnull);
            _tr_stored_block(s, (charf *)b, len, (int)parse_i(tk[4]));
            dump(s);
        } else if (!strcmp(op, "detect") && nt == 2) { /* freqspec */
            deflate_state *s = mk(16, 1, 0, 0, 0, 0, 0);
            parse_spec(tk[1], set_fc, s->dyn_ltree);
            printf("R=%d", detect_data_type(s));
        } else if (!strcmp(op, "gen_codes") && nt == 4) { /* max_code bl_count(16) lens */
            deflate_state *s = mk(16, 1, 0, 0, 0, 0, 0);
            int i = 0;
            for (char *t = strtok(tk[2], ","); t; t = strtok(NULL, ",")) s->bl_count[i++] = (ush)parse_u(t);
            parse_spec(tk[3], set_len, s->dyn_ltree);
            gen_codes(s->dyn_ltree, (int)parse_i(tk[1]), s->bl_count);
            dump(s);
            for (int n = 0; n < 288; n++) printf(n ? ",%u" : " C=%u", s->dyn_ltree[n].Code);
        } else if (!strcmp(op, "buildtree") && nt == 5) { /* which opt static freqspec */
            deflate_state *s = mk(16, 1, 0, 0, 0, 0, 0);
            s->opt_len = parse_u(tk[2]); s->static_len = parse_u(tk[3]);
            tree_desc *d; ct_data *t;
            if (!strcmp(tk[1], "l")) { d = &s->l_desc; t = s->dyn_ltree; }
            else if (!strcmp(tk[1], "d")) { d = &s->d_desc; t = s->dyn_dtree; }
            else { d = &s->bl_desc; t = s->bl_tree; }
            parse_spec(tk[4], set_fc, t);
            build_tree(s, d);
            dump(s);
            int ne = d->stat_desc->elems + 1;
            for (int n = 0; n < ne; n++) printf(n ? ",%u/%u" : " C=%u/%u", t[n].Code, t[n].Len);
        } else if (!strcmp(op, "trees") && nt == 8) { /* lmax llens dmax dlens bi_buf bi_valid pend0 */
            deflate_state *s = mk(16, 1, 0, 0, (unsigned)parse_u(tk[5]), (int)parse_i(tk[6]), parse_u(tk[7]));
            s->l_desc.max_code = (int)parse_i(tk[1]); parse_spec(tk[2], set_len, s->dyn_ltree);
            s->d_desc.max_code = (int)parse_i(tk[3]); parse_spec(tk[4], set_len, s->dyn_dtree);
            int r = build_bl_tree(s);
            send_all_trees(s, s->l_desc.max_code + 1, s->d_desc.max_code + 1, r + 1);
            printf("R=%d ", r);
            dump(s);
        } else if (!strcmp(op, "block") && nt == 11) {
            /* level strategy data_type bi_buf bi_valid lit stored_len buf last syms */
            unsigned lit = (unsigned)parse_u(tk[6]);
            deflate_state *s = mk(lit, (int)parse_i(tk[1]), (int)parse_i(tk[2]), (int)parse_i(tk[3]),
                                  (unsigned)parse_u(tk[4]), (int)parse_i(tk[5]), 0);
            unsigned long len = parse_u(tk[7]);
            int isnull; unsigned char *b = mkbuf(tk[8], len, &isnull);
            char rets[64] = "";
            unsigned cnt = tally_all(s, tk[10], rets, sizeof rets);
            printf("N=%u F=%s ", cnt, rets);
            _tr_flush_block(s, (charf *)b, len, (int)parse_i(tk[9]));
            dump(s);
        } else if (!strcmp(op, "tally") && nt == 3) { /* lit syms */
            unsigned lit = (unsigned)parse_u(tk[1]);
            deflate_state *s = mk(lit, 1, 0, 0, 0, 0, 0);
            char rets[4096] = "";
            unsigned cnt = tally_all(s, tk[2], rets, sizeof rets);
            printf("N=%u F=%s ", cnt, rets);
            dump(s);
        } else if (!strcmp(op, "tables") && nt == 1) {
            /* hashes of every static table of trees.h / trees.c and the three static descriptors */
            unsigned long long h = 14695981039346656037ULL;
            h = hash_tree(static_ltree, L_CODES + 2); printf("SL=%016llx", h);
            h = hash_tree(static_dtree, D_CODES); printf(" SD=%016llx", h);
            h = 14695981039346656037ULL; for (int i = 0; i < DIST_CODE_LEN; i++) h = fnv(h, _dist_code[i]);
            printf(" DC=%016llx", h);
            h = 14695981039346656037ULL; for (int i = 0; i < 256; i++) h = fnv(h, _length_code[i]);
            printf(" LC=%016llx", h);
            h = 14695981039346656037ULL; for (int i = 0; i < LENGTH_CODES; i++) h = fnv(h, (unsigned)base_length[i]);
            printf(" BL=%016llx", h);
            h = 14695981039346656037ULL; for (int i = 0; i < D_CODES; i++) h = fnv(h, (unsigned)base_dist[i]);
            printf(" BD=%016llx", h);
            h = 14695981039346656037ULL; for (int i = 0; i < LENGTH_CODES; i++) h = fnv(h, (unsigned)extra_lbits[i]);
            printf(" XL=%016llx", h);
            h = 14695981039346656037ULL; for (int i = 0; i < D_CODES; i++) h = fnv(h, (unsigned)extra_dbits[i]);
            printf(" XD=%016llx", h);
            h = 14695981039346656037ULL; for (int i = 0; i < BL_CODES; i++) h = fnv(h, (unsigned)extra_blbits[i]);
            printf(" XB=%016llx", h);
            h = 14695981039346656037ULL; for (int i = 0; i < BL_CODES; i++) h = fnv(h, bl_order[i]);
            printf(" BO=%016llx", h);
            printf(" LD=%d,%d,%d,%d,%d", static_l_desc.extra_base, static_l_desc.elems, static_l_desc.max_length,
                   static_l_desc.static_tree == static_ltree, static_l_desc.extra_bits == extra_lbits);
            printf(" DD=%d,%d,%d,%d,%d", static_d_desc.extra_base, static_d_desc.elems, static_d_desc.max_length,
                   static_d_desc.static_tree == static_dtree, static_d_desc.extra_bits == extra_dbits);
            printf(" BLD=%d,%d,%d,%d,%d", static_bl_desc.extra_base, static_bl_desc.elems, static_bl_desc.max_length,
                   static_bl_desc.static_tree == NULL, static_bl_desc.extra_bits == extra_blbits);
        } else if (!strcmp(op, "init") && nt == 1) {
            deflate_state *s = mk(16, 1, 0, 0, 7, -99, 0);
            dump(s);
        } else {
            printf("BADINPUT %s\n", op);
            fprintf(stderr, "bad input line: %s\n", op);
            return 2;
        }
        printf("\n");
        if (cur_state) { free(cur_state->pending_buf); free(cur_state->strm); free(cur_state); cur_state = NULL; }
        free(cur_buf); cur_buf = NULL;
    }
    free(line);
    return 0;
}
