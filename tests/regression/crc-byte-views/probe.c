#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include "deflate.h"
#include "fixtures.h"

typedef struct { const char *name; const unsigned char *bytes; size_t size; } View;

static _Alignas(8) unsigned char raw_bytes[sizeof fixture_raw];
static deflate_state holder;

static void print_data(View v) {
    size_t i;
    printf("DATA|%s|%zu|%u|", v.name, v.size, (unsigned)((uintptr_t)v.bytes & 7));
    for (i = 0; i < v.size; i++) printf("%02x", (unsigned)v.bytes[i]);
    putchar('\n');
}

int main(void) {
    View views[] = {
        {"raw", raw_bytes, sizeof raw_bytes},
        {"str", fixture_str, sizeof fixture_str},
        {"str_empty", fixture_str_empty, sizeof fixture_str_empty},
        {"dstate_depth", holder.depth, sizeof holder.depth},
        {"st_dist_code", _dist_code, 512},
        {"st_length_code", _length_code, 256}
    };
    char fn[16], name[32];
    size_t offset, length, i, cases = 0;
    unsigned long long seed;
    unsigned char raw_before[sizeof raw_bytes], depth_before[sizeof holder.depth];
    int got;
    if (sizeof holder.depth != sizeof fixture_dstate_depth ||
        sizeof fixture_st_dist_code != 512 || sizeof fixture_st_length_code != 256) return 2;
    memcpy(raw_bytes, fixture_raw, sizeof raw_bytes);
    memcpy(holder.depth, fixture_dstate_depth, sizeof holder.depth);
    memcpy(raw_before, raw_bytes, sizeof raw_bytes);
    memcpy(depth_before, holder.depth, sizeof holder.depth);
    if (((uintptr_t)raw_bytes & 7) != 0) return 3;
    if (memcmp(_dist_code, fixture_st_dist_code, 512) ||
        memcmp(_length_code, fixture_st_length_code, 256)) return 4;
    printf("META|%zu|%zu|%zu|%zu\n", sizeof(uLong), sizeof(size_t),
           sizeof(deflate_state), offsetof(deflate_state, depth));
    for (i = 0; i < sizeof views / sizeof views[0]; i++) print_data(views[i]);
    while ((got = scanf("%15s %31s %zu %zu %llu", fn, name, &offset, &length, &seed)) == 5) {
        View *v = NULL;
        const unsigned char *p;
        uLong result;
        for (i = 0; i < sizeof views / sizeof views[0]; i++)
            if (strcmp(name, views[i].name) == 0) v = &views[i];
        if (v == NULL || offset > v->size || length > v->size - offset || length > 0xffffffffUL) return 5;
        p = v->bytes + offset;
        if (strcmp(fn, "crc32_z") == 0) result = crc32_z((uLong)seed, p, (z_size_t)length);
        else if (strcmp(fn, "crc32") == 0) result = crc32((uLong)seed, p, (uInt)length);
        else return 6;
        printf("R|%s|%s|%u|%zu|%zu|%llu|%u|%llu\n", fn, name,
               (unsigned)((uintptr_t)v->bytes & 7), offset, length, seed,
               (unsigned)((uintptr_t)p & 7), (unsigned long long)result);
        cases++;
    }
    if (got != EOF) return 7;
    if (memcmp(raw_bytes, raw_before, sizeof raw_bytes) ||
        memcmp(holder.depth, depth_before, sizeof holder.depth) ||
        memcmp(_dist_code, fixture_st_dist_code, 512) ||
        memcmp(_length_code, fixture_st_length_code, 256)) return 8;
    printf("END|%zu|1\n", cases);
    return 0;
}
