#include <stdio.h>
#include <string.h>
#include "zlib.h"
#include "deflate.h"
#ifndef EXPECTED_RESULT
#error EXPECTED_RESULT must name the expected refusal code
#endif
int main(void) {
    z_stream stream = {0};
    int init_rc, call_rc, end_rc, status_before, status_after, state_same;
    int level, memory, window, strategy, wrap;
    struct internal_state *allocated_state;
    char message[80];
    init_rc = deflateInit(&stream, Z_DEFAULT_COMPRESSION);
    if (init_rc != Z_OK) {
        fprintf(stderr, "default initialization failed: %d\n", init_rc);
        return 10;
    }
    allocated_state = stream.state;
    status_before = ((deflate_state *)stream.state)->status;
    level = ((deflate_state *)stream.state)->level;
    memory = (int)((deflate_state *)stream.state)->hash_bits - 7;
    window = (int)((deflate_state *)stream.state)->w_bits;
    strategy = ((deflate_state *)stream.state)->strategy;
    wrap = ((deflate_state *)stream.state)->wrap;
    /* The actual request under review. No input/output object is dereferenced. */
    stream.next_in = Z_NULL;
    stream.avail_in = 0;
    stream.next_out = Z_NULL;
    stream.avail_out = 0;
    call_rc = deflate(&stream, Z_NO_FLUSH);
    status_after = ((deflate_state *)stream.state)->status;
    state_same = stream.state == allocated_state;
    snprintf(message, sizeof(message), "%s", stream.msg != Z_NULL ? stream.msg : "");
    if (stream.total_in != 0 || stream.total_out != 0 ||
        stream.next_in != Z_NULL || stream.next_out != Z_NULL ||
        stream.avail_in != 0 || stream.avail_out != 0 || !state_same) {
        fprintf(stderr, "unexpected buffer/accounting/state mutation\n");
        deflateEnd(&stream);
        return 11;
    }
    end_rc = deflateEnd(&stream);
    printf("{\"init_rc\":%d,\"level\":%d,\"memory\":%d,\"window\":%d,"
           "\"strategy\":%d,\"wrap\":%d,\"call_rc\":%d,\"message\":\"%s\","
           "\"flush\":%d,\"status_before\":%d,\"status_after\":%d,"
           "\"state_same_after_refusal\":%d,\"end_rc\":%d,\"state_null_after_end\":%d}\n",
           init_rc, level, memory, window, strategy, wrap, call_rc, message,
           Z_NO_FLUSH, status_before, status_after, state_same, end_rc, stream.state == Z_NULL);
    return !(call_rc == EXPECTED_RESULT && end_rc == Z_OK && stream.state == Z_NULL &&
             status_before == status_after && level == 6 && memory == 8 && window == 15 &&
             strategy == Z_DEFAULT_STRATEGY && wrap == 1);
}
