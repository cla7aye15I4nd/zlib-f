/* Deterministic codec experiments. Before compiling, apply the registered
 * 0001-inflate-copy-pointer-equality.patch to the pinned zlib source.
 * Link with that patched source and its header.
 * Default output is JSON. --dump-input writes the generated input bytes.
 * This example runner does not instrument internal codec functions.
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <zlib.h>

#define TRACE_REGION ((size_t)65536)
#define TRACE_INPUT_SIZE (3 * TRACE_REGION)
#define TRACE_CHUNK 4096u
#define TRACE_SOURCE "757f0527154291bcf6bfbd6396ecde6bedd2db95"

struct trace_bytes {
    unsigned char *data;
    size_t size, capacity;
};

struct trace_case {
    const char *name;
    int level, window_bits, memory_level, strategy, decode_window_bits;
};

struct trace_result {
    size_t encoded_size, decoded_size, payload_offset;
    unsigned encode_calls, decode_calls, block_type, final_block;
    int header_window_bits;
};

static uint32_t trace_rotr(uint32_t value, unsigned amount) {
    return (value >> amount) | (value << (32 - amount));
}

static void trace_sha_block(uint32_t state[8], const unsigned char block[64]) {
    static const uint32_t constants[64] = {
        0x428a2f98u,0x71374491u,0xb5c0fbcfu,0xe9b5dba5u,
        0x3956c25bu,0x59f111f1u,0x923f82a4u,0xab1c5ed5u,
        0xd807aa98u,0x12835b01u,0x243185beu,0x550c7dc3u,
        0x72be5d74u,0x80deb1feu,0x9bdc06a7u,0xc19bf174u,
        0xe49b69c1u,0xefbe4786u,0x0fc19dc6u,0x240ca1ccu,
        0x2de92c6fu,0x4a7484aau,0x5cb0a9dcu,0x76f988dau,
        0x983e5152u,0xa831c66du,0xb00327c8u,0xbf597fc7u,
        0xc6e00bf3u,0xd5a79147u,0x06ca6351u,0x14292967u,
        0x27b70a85u,0x2e1b2138u,0x4d2c6dfcu,0x53380d13u,
        0x650a7354u,0x766a0abbu,0x81c2c92eu,0x92722c85u,
        0xa2bfe8a1u,0xa81a664bu,0xc24b8b70u,0xc76c51a3u,
        0xd192e819u,0xd6990624u,0xf40e3585u,0x106aa070u,
        0x19a4c116u,0x1e376c08u,0x2748774cu,0x34b0bcb5u,
        0x391c0cb3u,0x4ed8aa4au,0x5b9cca4fu,0x682e6ff3u,
        0x748f82eeu,0x78a5636fu,0x84c87814u,0x8cc70208u,
        0x90befffau,0xa4506cebu,0xbef9a3f7u,0xc67178f2u
    };
    uint32_t words[64], a, b, c, d, e, f, g, h;
    unsigned i;
    for (i = 0; i < 16; i++)
        words[i] = ((uint32_t)block[4*i] << 24) |
                   ((uint32_t)block[4*i+1] << 16) |
                   ((uint32_t)block[4*i+2] << 8) | block[4*i+3];
    for (i = 16; i < 64; i++) {
        uint32_t x = words[i-15], y = words[i-2];
        uint32_t first = trace_rotr(x,7) ^ trace_rotr(x,18) ^ (x >> 3);
        uint32_t second = trace_rotr(y,17) ^ trace_rotr(y,19) ^ (y >> 10);
        words[i] = words[i-16] + first + words[i-7] + second;
    }
    a=state[0]; b=state[1]; c=state[2]; d=state[3];
    e=state[4]; f=state[5]; g=state[6]; h=state[7];
    for (i = 0; i < 64; i++) {
        uint32_t s1 = trace_rotr(e,6) ^ trace_rotr(e,11) ^ trace_rotr(e,25);
        uint32_t choose = (e & f) ^ (~e & g);
        uint32_t t1 = h + s1 + choose + constants[i] + words[i];
        uint32_t s0 = trace_rotr(a,2) ^ trace_rotr(a,13) ^ trace_rotr(a,22);
        uint32_t majority = (a & b) ^ (a & c) ^ (b & c);
        uint32_t t2 = s0 + majority;
        h=g; g=f; f=e; e=d+t1; d=c; c=b; b=a; a=t1+t2;
    }
    state[0]+=a; state[1]+=b; state[2]+=c; state[3]+=d;
    state[4]+=e; state[5]+=f; state[6]+=g; state[7]+=h;
}

static void trace_sha256(const unsigned char *data, size_t size, char hex[65]) {
    uint32_t state[8] = {0x6a09e667u,0xbb67ae85u,0x3c6ef372u,0xa54ff53au,
                         0x510e527fu,0x9b05688cu,0x1f83d9abu,0x5be0cd19u};
    unsigned char tail[128];
    size_t complete = size / 64, rest = size % 64, padded;
    uint64_t bits = (uint64_t)size * 8;
    size_t i;
    for (i = 0; i < complete; i++) trace_sha_block(state, data + 64*i);
    padded = rest < 56 ? 64 : 128;
    memset(tail, 0, padded);
    memcpy(tail, data + complete*64, rest);
    tail[rest] = 0x80;
    for (i = 0; i < 8; i++) tail[padded-1-i] = (unsigned char)(bits >> (8*i));
    trace_sha_block(state, tail);
    if (padded == 128) trace_sha_block(state, tail + 64);
    for (i = 0; i < 32; i++) {
        unsigned byte = (state[i/4] >> (24 - 8*(i%4))) & 255u;
        hex[2*i] = "0123456789abcdef"[byte >> 4];
        hex[2*i+1] = "0123456789abcdef"[byte & 15u];
    }
    hex[64] = 0;
}

static void trace_input(unsigned char *input) {
    static const unsigned char text[] =
        "kind=reading;value=01234567;pattern=ABABABAB;state=ready;\n";
    uint32_t random = 0x12345678u;
    size_t i;
    for (i = 0; i < TRACE_REGION; i++) {
        unsigned marker = (unsigned)(i % 97);
        input[i] = text[i % (sizeof text - 1)];
        if (marker < 8)
            input[i] = (unsigned char)('0' + ((i / 97) >> (3*marker)) % 10);
    }
    for (i = 0; i < TRACE_REGION; i++)
        input[TRACE_REGION+i] = (unsigned char)('A' + (i / 1024) % 4);
    for (i = 0; i < TRACE_REGION; i++) {
        random ^= random << 13;
        random ^= random >> 17;
        random ^= random << 5;
        input[2*TRACE_REGION+i] = (unsigned char)random;
    }
}

static int trace_append(struct trace_bytes *bytes,
                        const unsigned char *data, size_t size) {
    size_t needed, capacity;
    unsigned char *grown;
    if (size == 0) return 1;
    if (size > SIZE_MAX - bytes->size) return 0;
    needed = bytes->size + size;
    if (needed > bytes->capacity) {
        capacity = bytes->capacity ? bytes->capacity : TRACE_CHUNK;
        while (capacity < needed) {
            if (capacity > SIZE_MAX/2) { capacity = needed; break; }
            capacity *= 2;
        }
        grown = (unsigned char *)realloc(bytes->data, capacity);
        if (grown == NULL) return 0;
        bytes->data = grown;
        bytes->capacity = capacity;
    }
    memcpy(bytes->data + bytes->size, data, size);
    bytes->size = needed;
    return 1;
}

static int trace_encode(const struct trace_case *config,
                        unsigned char *input, size_t size,
                        struct trace_bytes *encoded, unsigned *calls) {
    z_stream stream = {0};
    unsigned char chunk[TRACE_CHUNK];
    size_t offered = 0;
    int result, ended, ok = 1;
    if (deflateInit2(&stream, config->level, Z_DEFLATED, config->window_bits,
                     config->memory_level, config->strategy) != Z_OK) return 0;
    do {
        unsigned before, made;
        int flush;
        if (stream.avail_in == 0 && offered < size) {
            size_t amount = size - offered;
            if (amount > TRACE_CHUNK) amount = TRACE_CHUNK;
            stream.next_in = input + offered;
            stream.avail_in = (uInt)amount;
            offered += amount;
        }
        flush = offered == size ? Z_FINISH : Z_NO_FLUSH;
        before = stream.avail_in;
        stream.next_out = chunk;
        stream.avail_out = TRACE_CHUNK;
        result = deflate(&stream, flush);
        (*calls)++;
        made = TRACE_CHUNK - stream.avail_out;
        if ((result != Z_OK && result != Z_STREAM_END) ||
            !trace_append(encoded, chunk, made) ||
            (result != Z_STREAM_END && before == stream.avail_in && made == 0)) {
            ok = 0; break;
        }
    } while (result != Z_STREAM_END);
    if (stream.avail_in != 0 || offered != size) ok = 0;
    ended = deflateEnd(&stream);
    return ok && ended == Z_OK;
}

static int trace_decode(const struct trace_case *config,
                        struct trace_bytes *encoded,
                        const unsigned char *original, size_t size,
                        struct trace_result *record) {
    z_stream stream = {0};
    unsigned char chunk[TRACE_CHUNK];
    size_t offered = 0, produced = 0;
    int result, ended, ok = 1;
    if (inflateInit2(&stream, config->decode_window_bits) != Z_OK) return 0;
    do {
        unsigned before, made;
        if (stream.avail_in == 0 && offered < encoded->size) {
            size_t amount = encoded->size - offered;
            if (amount > TRACE_CHUNK) amount = TRACE_CHUNK;
            stream.next_in = encoded->data + offered;
            stream.avail_in = (uInt)amount;
            offered += amount;
        }
        before = stream.avail_in;
        stream.next_out = chunk;
        stream.avail_out = TRACE_CHUNK;
        result = inflate(&stream, Z_NO_FLUSH);
        record->decode_calls++;
        made = TRACE_CHUNK - stream.avail_out;
        if ((result != Z_OK && result != Z_STREAM_END) ||
            produced > size || made > size - produced ||
            memcmp(original + produced, chunk, made) != 0 ||
            (result != Z_STREAM_END && before == stream.avail_in && made == 0)) {
            ok = 0; break;
        }
        produced += made;
    } while (result != Z_STREAM_END);
    if (produced != size || offered != encoded->size || stream.avail_in != 0)
        ok = 0;
    record->decoded_size = produced;
    ended = inflateEnd(&stream);
    return ok && ended == Z_OK;
}

static int trace_header(const struct trace_case *config,
                        const struct trace_bytes *encoded,
                        struct trace_result *record) {
    size_t offset = 0;
    record->header_window_bits = 0;
    if (config->window_bits > 15) {
        if (encoded->size < 11 || encoded->data[0] != 31 ||
            encoded->data[1] != 139 || encoded->data[2] != 8 ||
            encoded->data[3] != 0) return 0;
        offset = 10; /* This runner uses the default gzip header, no options. */
    } else if (config->window_bits > 0) {
        unsigned header;
        if (encoded->size < 3) return 0;
        header = ((unsigned)encoded->data[0] << 8) | encoded->data[1];
        if ((encoded->data[0] & 15u) != 8 || header % 31 != 0 ||
            (encoded->data[1] & 32u) != 0) return 0;
        offset = 2; /* No preset dictionary in these cases. */
        record->header_window_bits = (encoded->data[0] >> 4) + 8;
    }
    if (offset >= encoded->size) return 0;
    record->payload_offset = offset;
    record->final_block = encoded->data[offset] & 1u;
    record->block_type = (encoded->data[offset] >> 1) & 3u;
    return record->block_type != 3;
}

int main(int argc, char **argv) {
    static const struct trace_case cases[] = {
        {"default",6,15,8,Z_DEFAULT_STRATEGY,15},
        {"level-0",0,15,8,Z_DEFAULT_STRATEGY,15},
        {"level-1",1,15,8,Z_DEFAULT_STRATEGY,15},
        {"level-9",9,15,8,Z_DEFAULT_STRATEGY,15},
        {"filtered",6,15,8,Z_FILTERED,15},
        {"huffman-only",6,15,8,Z_HUFFMAN_ONLY,15},
        {"rle",6,15,8,Z_RLE,15},
        {"fixed",6,15,8,Z_FIXED,15},
        {"window-9",6,9,8,Z_DEFAULT_STRATEGY,9},
        {"memory-1",6,15,1,Z_DEFAULT_STRATEGY,15},
        {"window-9-memory-1",6,9,1,Z_DEFAULT_STRATEGY,9},
        {"window-8-normalized",6,8,8,Z_DEFAULT_STRATEGY,9},
        {"raw",6,-15,8,Z_DEFAULT_STRATEGY,-15},
        {"gzip",6,31,8,Z_DEFAULT_STRATEGY,31},
        {"zlib-auto",6,15,8,Z_DEFAULT_STRATEGY,47},
        {"gzip-auto",6,31,8,Z_DEFAULT_STRATEGY,47}
    };
    static const char *block_names[] = {"stored", "fixed", "dynamic"};
    struct trace_result results[sizeof cases / sizeof cases[0]] = {{0}};
    unsigned char *input = (unsigned char *)malloc(TRACE_INPUT_SIZE);
    char digest[65];
    size_t i, count = sizeof cases / sizeof cases[0];
    if (input == NULL) return 1;
    trace_input(input);
    if (argc == 2 && strcmp(argv[1], "--dump-input") == 0) {
        int ok = fwrite(input, 1, TRACE_INPUT_SIZE, stdout) == TRACE_INPUT_SIZE;
        free(input); return ok ? 0 : 1;
    }
    if (argc != 1) { free(input); return 1; }
    for (i = 0; i < count; i++) {
        struct trace_bytes encoded = {0};
        if (!trace_encode(cases+i, input, TRACE_INPUT_SIZE, &encoded,
                          &results[i].encode_calls) ||
            !trace_header(cases+i, &encoded, results+i) ||
            !trace_decode(cases+i, &encoded, input, TRACE_INPUT_SIZE, results+i)) {
            fprintf(stderr, "Codec experiment failed: %s\n", cases[i].name);
            free(encoded.data); free(input); return 1;
        }
        results[i].encoded_size = encoded.size;
        free(encoded.data);
    }
    trace_sha256(input, TRACE_INPUT_SIZE, digest);
    free(input);
    printf("{\n  \"schema\": 1,\n  \"kind\": \"fixed-source-native-example-runs\",\n");
    printf("  \"source_commit\": \"%s\",\n  \"zlib_version\": \"%s\",\n", TRACE_SOURCE, zlibVersion());
    printf("  \"source_patches\": [\"0001-inflate-copy-pointer-equality.patch\"],\n");
    printf("  \"input\": {\"bytes\": %zu, \"sha256\": \"%s\",\n", TRACE_INPUT_SIZE, digest);
    printf("    \"generator\": \"three 65536-byte regions: periodic text with numeric markers; 1024-byte runs; xorshift32 bytes\",\n");
    printf("    \"random_seed\": \"0x12345678\", \"random_shifts\": [13, 17, 5]},\n");
    printf("  \"build\": {\"allocator\": \"default\", \"compile_flags\": [\"-O2\", \"-std=c99\", \"-Wall\", \"-Wextra\"],\n");
    printf("    \"sizeof_uint\": %zu, \"sizeof_ulong\": %zu, \"sizeof_pointer\": %zu,\n", sizeof(uInt), sizeof(uLong), sizeof(void *));
    printf("    \"zlib_compile_flags\": %lu},\n", zlibCompileFlags());
    printf("  \"calls\": {\"input_chunk_bytes\": %u, \"output_chunk_bytes\": %u,\n", TRACE_CHUNK, TRACE_CHUNK);
    printf("    \"deflate_flush\": \"Z_NO_FLUSH until the final input slice is offered, then Z_FINISH until Z_STREAM_END\",\n");
    printf("    \"inflate_flush\": \"Z_NO_FLUSH\", \"dictionary\": null, \"extra_flushes\": false},\n");
    printf("  \"measurement\": {\"first_block_only\": true, \"internal_function_counts\": null},\n  \"cases\": [\n");
    for (i = 0; i < count; i++) {
        const struct trace_case *c = cases+i;
        const struct trace_result *r = results+i;
        const char *wrapper = c->window_bits < 0 ? "raw" : c->window_bits > 15 ? "gzip" : "zlib";
        printf("    {\"name\": \"%s\", \"wrapper\": \"%s\",\n", c->name, wrapper);
        printf("     \"deflate_init\": {\"level\": %d, \"method\": %d, \"window_bits\": %d, \"memory_level\": %d, \"strategy\": %d},\n", c->level, Z_DEFLATED, c->window_bits, c->memory_level, c->strategy);
        printf("     \"inflate_init\": {\"window_bits\": %d},\n", c->decode_window_bits);
        printf("     \"compressed_bytes\": %zu, \"decoded_bytes\": %zu, \"roundtrip\": true,\n", r->encoded_size, r->decoded_size);
        printf("     \"deflate_calls\": %u, \"inflate_calls\": %u, \"payload_offset\": %zu,\n", r->encode_calls, r->decode_calls, r->payload_offset);
        printf("     \"first_block\": {\"type\": \"%s\", \"type_bits\": %u, \"final\": %s},\n", block_names[r->block_type], r->block_type, r->final_block ? "true" : "false");
        if (r->header_window_bits)
            printf("     \"header_window_bits\": %d}%s\n", r->header_window_bits, i+1 == count ? "" : ",");
        else
            printf("     \"header_window_bits\": null}%s\n", i+1 == count ? "" : ",");
    }
    printf("  ]\n}\n");
    return ferror(stdout) ? 1 : 0;
}
