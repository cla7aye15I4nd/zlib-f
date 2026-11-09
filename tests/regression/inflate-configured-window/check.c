#include <stdio.h>
#include <string.h>
#include "zlib.h"

int main(void) {
    unsigned char dictionary[512];
    unsigned char output[32] = {0};
    unsigned char source[] = {0x08,0x3c,0x4a,0x9e,0x82,0x01,
                             0x03,0x06,0x00,0x00,0x01,0x89,0x00,0xc4};
    z_stream stream;
    memset(dictionary, 'A', sizeof dictionary);
    memset(&stream, 0, sizeof stream);
    int init = inflateInit(&stream);
    if (init != Z_OK) return 2;
    stream.next_in = source;
    stream.avail_in = sizeof source;
    stream.next_out = output;
    stream.avail_out = sizeof output;
    int first = inflate(&stream, Z_NO_FLUSH);
    int setter = first == Z_NEED_DICT
        ? inflateSetDictionary(&stream, dictionary, sizeof dictionary) : -999;
    int final = setter == Z_OK ? inflate(&stream, Z_FINISH) : -999;
    printf("version=%s init=%d first=%d dictionary=%d final=%d total_in=%lu total_out=%lu output=%02x%02x%02x\n",
        zlibVersion(), init, first, setter, final, stream.total_in, stream.total_out,
        output[0], output[1], output[2]);
    int good = first == Z_NEED_DICT && setter == Z_OK && final == Z_STREAM_END &&
        stream.total_out == 3 && memcmp(output, "AAA", 3) == 0;
    int cleanup = inflateEnd(&stream);
    return good && cleanup == Z_OK ? 0 : 1;
}
