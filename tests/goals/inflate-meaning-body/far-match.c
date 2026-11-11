/* A too-far distance waits in MATCH while the call returns Z_OK (P12).

   `case MATCH` leaves for want of output room (`left == 0`) before it checks
   the distance against the window. The raw stream `03 02` is a final fixed
   block with one match: length symbol 257 (length 3) and distance symbol 0
   (distance 1), with no history. Inflated with no output room, the first call
   decodes the whole match and stops in MATCH with Z_OK; the second call, with
   room, reports "invalid distance too far back".

   Expected output:
     call1 rc=0 mode=16204 (MATCH=16204) offset=1 length=3 whave=0 avail_in=0
     call2 rc=-3 mode=16209 msg=invalid distance too far back

   Build against the pinned source (it reads the internal state):
     cc -fsanitize=address,undefined -I"$ZLIB_SRC" far-match.c "$ZLIB_SRC"/inflate.c \
       "$ZLIB_SRC"/inftrees.c "$ZLIB_SRC"/inffast.c "$ZLIB_SRC"/adler32.c \
       "$ZLIB_SRC"/crc32.c "$ZLIB_SRC"/zutil.c -o far-match && ./far-match
*/
#include <stdio.h>
#include "zlib.h"
#include "zutil.h"
#include "inftrees.h"
#include "inflate.h"
int main(void){
  unsigned char in[2]={0x03,0x02}; unsigned char out[16]; z_stream s={0};
  inflateInit2(&s,-15);
  s.next_in=in; s.avail_in=2; s.next_out=out; s.avail_out=0;
  int rc=inflate(&s,Z_NO_FLUSH);
  struct inflate_state *st=(struct inflate_state*)s.state;
  printf("call1 rc=%d mode=%d (MATCH=%d) offset=%u length=%u whave=%u avail_in=%u\n",rc,st->mode,MATCH,st->offset,st->length,st->whave,s.avail_in);
  s.avail_out=16; rc=inflate(&s,Z_NO_FLUSH);
  printf("call2 rc=%d mode=%d msg=%s\n",rc,st->mode,s.msg?s.msg:"");
  return 0;}
