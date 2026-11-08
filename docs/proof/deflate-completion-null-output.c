#include <stdio.h>
#include "zlib.h"

int main(void) {
    z_stream stream = {0};
    int init = deflateInit(&stream, Z_DEFAULT_COMPRESSION);
    if (init != Z_OK) return 2;
    unsigned long bound = deflateBound(&stream, 0);
    stream.next_in = Z_NULL;
    stream.avail_in = 0;
    stream.next_out = Z_NULL;
    stream.avail_out = 64;
    int finish = deflate(&stream, Z_FINISH);
    printf("init=%d bound=%lu capacity=%u finish=%d total_out=%lu\n",
           init, bound, stream.avail_out, finish, stream.total_out);
    int demonstrated = bound <= 64 && finish == Z_STREAM_ERROR && stream.total_out == 0;
    deflateEnd(&stream);
    return demonstrated ? 0 : 1;
}
