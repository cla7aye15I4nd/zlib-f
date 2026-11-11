#include <stdio.h>
#include <string.h>
#include "zutil.h"
#include "inftrees.h"
#include "inflate.h"
static unsigned char buf[64]; static int nb;
static void put(unsigned v, int n){ for(int i=0;i<n;i++){ if((v>>i)&1) buf[nb>>3]|=1<<(nb&7); nb++; } }
static void run(const char *name){
  z_stream s; memset(&s,0,sizeof s); inflateInit2(&s,-15);
  s.next_in=buf; s.avail_in=(nb+7)/8; unsigned char o[16]; s.next_out=o; s.avail_out=16;
  int r=inflate(&s,Z_NO_FLUSH); struct inflate_state *st=(void*)s.state;
  printf("%s: bits=%d bytes=%u ret=%d mode=%d (LENLENS=%d CODELENS=%d BAD=%d) have=%u held=%u\n",
    name,nb,(nb+7)/8,r,st->mode,LENLENS,CODELENS,BAD,st->have,st->bits);
  inflateEnd(&s); memset(buf,0,sizeof buf); nb=0; }
int main(void){
  /* A: code-length code lengths so far over-subscribed (16,17,18 all length 1) */
  put(1,1); put(2,2); put(0,5); put(0,5); put(15,4); put(1,3);put(1,3);put(1,3);put(0,3);put(0,3); run("A oversubscribed cl prefix");
  /* B: empty code-length code (HCLEN=0, four zero lengths), then 8 more bits */
  put(1,1); put(2,2); put(0,5); put(0,5); put(0,4); put(0,12); put(0,7); run("B empty cl code");
  /* C: lens[256] = 0 already read: cl {0:1, 18:1}; 18+127, 18+108 = 257 zeros; then 18 without its extra bits */
  put(1,1); put(2,2); put(0,5); put(0,5); put(0,4); put(0,3);put(0,3);put(1,3);put(1,3);
  put(1,1); put(127,7); put(1,1); put(108,7); put(7,3); run("C missing end-of-block already read");
  return 0; }
