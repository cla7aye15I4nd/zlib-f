#include <stdio.h>
#include "zlib.h"
#include "deflate.h"

int main(void) {
    z_stream stream = {0};
    unsigned char first[3] = {0};
    unsigned char output[64] = {0};
    unsigned char extra[1] = {42};
    int init = deflateInit(&stream, Z_DEFAULT_COMPRESSION);
    if (init != Z_OK) return 2;
    unsigned long bound = deflateBound(&stream, 1);
    stream.next_in = Z_NULL;
    stream.avail_in = 0;
    stream.next_out = first;
    stream.avail_out = sizeof(first);
    int initial_finish = deflate(&stream, Z_FINISH);
    unsigned long observed_output = stream.total_out;
    int status = ((deflate_state *)stream.state)->status;
    unsigned long pending = ((deflate_state *)stream.state)->pending;
    stream.next_in = extra;
    stream.avail_in = sizeof(extra);
    stream.next_out = output;
    stream.avail_out = sizeof(output);
    int next_finish = deflate(&stream, Z_FINISH);
    printf("init=%d first_finish=%d status=%d FINISH_STATE=%d pending=%lu "
           "observed_output=%lu bound=%lu next_capacity=%zu "
           "next_finish=%d remaining_input=%u total_input=%lu total_output=%lu\n",
           init, initial_finish, status, FINISH_STATE, pending,
           observed_output, bound, sizeof(output), next_finish,
           stream.avail_in, stream.total_in, stream.total_out);
    int demonstrated = initial_finish == Z_OK && status == FINISH_STATE &&
        bound <= observed_output + sizeof(output) &&
        next_finish == Z_BUF_ERROR && stream.avail_in == 1;
    deflateEnd(&stream);
    return demonstrated ? 0 : 1;
}
