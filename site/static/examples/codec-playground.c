/* Browser exercise of the selected zlib C, using its default public APIs.
 * The result buffers belong to this module until codec_reset(). */
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include "zlib.h"

#define INPUT_LIMIT 262144u
#define RECORD_LIMIT 8u

typedef struct {
    uint32_t kind;
    int32_t result;
    uint32_t input_before, input_after;
    uint32_t output_before, output_after;
    uint32_t total_input, total_output;
} CallRecord;

static CallRecord records[RECORD_LIMIT];
static uint32_t record_count;
static unsigned char *packed, *restored;
static uint32_t packed_length, restored_length, equal_result, error_code;

static void record(uint32_t kind, int result, const z_stream *stream,
                   uint32_t input_before, uint32_t output_before) {
    CallRecord *entry;
    if (record_count >= RECORD_LIMIT) return;
    entry = &records[record_count++];
    entry->kind = kind;
    entry->result = result;
    entry->input_before = input_before;
    entry->input_after = stream ? stream->avail_in : 0;
    entry->output_before = output_before;
    entry->output_after = stream ? stream->avail_out : 0;
    entry->total_input = stream ? (uint32_t)stream->total_in : 0;
    entry->total_output = stream ? (uint32_t)stream->total_out : 0;
}

void codec_reset(void) {
    free(packed);
    free(restored);
    packed = restored = NULL;
    packed_length = restored_length = equal_result = error_code = 0;
    record_count = 0;
    memset(records, 0, sizeof records);
}

int codec_run(const unsigned char *input, uint32_t length) {
    z_stream encoder = {0}, decoder = {0};
    int rc, end_rc, encoder_live = 0, decoder_live = 0;
    uint32_t in_before, out_before;
    uLong bound;
    codec_reset();
    if (length > INPUT_LIMIT || (length != 0 && input == NULL)) {
        error_code = 1;
        return -1;
    }
    bound = compressBound(length);
    packed = (unsigned char *)malloc((size_t)bound);
    restored = (unsigned char *)malloc((size_t)length + 1);
    if (!packed || !restored) { error_code = 2; goto cleanup; }

    rc = deflateInit(&encoder, Z_DEFAULT_COMPRESSION);
    record(1, rc, &encoder, 0, 0);
    if (rc != Z_OK) { error_code = 3; goto cleanup; }
    encoder_live = 1;
    encoder.next_in = (Bytef *)input;
    encoder.avail_in = length;
    encoder.next_out = packed;
    encoder.avail_out = (uInt)bound;
    in_before = encoder.avail_in;
    out_before = encoder.avail_out;
    rc = deflate(&encoder, Z_FINISH);
    record(2, rc, &encoder, in_before, out_before);
    packed_length = (uint32_t)encoder.total_out;
    end_rc = deflateEnd(&encoder);
    encoder_live = 0;
    record(3, end_rc, &encoder, encoder.avail_in, encoder.avail_out);
    if (rc != Z_STREAM_END) { error_code = 4; goto cleanup; }
    if (end_rc != Z_OK) { error_code = 5; goto cleanup; }

    rc = inflateInit(&decoder);
    record(4, rc, &decoder, 0, 0);
    if (rc != Z_OK) { error_code = 6; goto cleanup; }
    decoder_live = 1;
    decoder.next_in = packed;
    decoder.avail_in = packed_length;
    decoder.next_out = restored;
    /* One extra position keeps empty input ordinary and detects extra output. */
    decoder.avail_out = length + 1;
    in_before = decoder.avail_in;
    out_before = decoder.avail_out;
    rc = inflate(&decoder, Z_NO_FLUSH);
    record(5, rc, &decoder, in_before, out_before);
    restored_length = (uint32_t)decoder.total_out;
    end_rc = inflateEnd(&decoder);
    decoder_live = 0;
    record(6, end_rc, &decoder, decoder.avail_in, decoder.avail_out);
    if (rc != Z_STREAM_END) { error_code = 7; goto cleanup; }
    if (end_rc != Z_OK) { error_code = 8; goto cleanup; }

    equal_result = restored_length == length &&
        (length == 0 || memcmp(input, restored, length) == 0);
    record(7, (int)equal_result, NULL, 0, 0);
    if (!equal_result) error_code = 9;
cleanup:
    if (encoder_live) deflateEnd(&encoder);
    if (decoder_live) inflateEnd(&decoder);
    if (error_code) {
        free(packed); free(restored);
        packed = restored = NULL;
        packed_length = restored_length = 0;
        return -(int)error_code;
    }
    return 0;
}

uint32_t codec_record_count(void) { return record_count; }
const CallRecord *codec_records(void) { return records; }
const unsigned char *codec_packed(void) { return packed; }
uint32_t codec_packed_length(void) { return packed_length; }
const unsigned char *codec_restored(void) { return restored; }
uint32_t codec_restored_length(void) { return restored_length; }
uint32_t codec_equal(void) { return equal_result; }
uint32_t codec_error(void) { return error_code; }
uint32_t codec_stream_size(void) { return sizeof(z_stream); }
