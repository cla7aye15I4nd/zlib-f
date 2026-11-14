/* Regression for the statement correction of GzReadInv.copyDirect (ZlibF/Proof/gz.inv-model.lean).
 * The old clause `how = COPY -> direct = 1` is false: after a gzip member with trailing data, gzclearerr and a
 * further gzread, gz_look takes its COPY branch with direct = 0 and junk = 1.
 * Build against zlib/ with patches/*.patch applied (ASan and UBSan report nothing). Expected last line:
 *   read3 4 how=1 (COPY=1) direct=0 junk=1 gzdirect=0
 */
#include <stdio.h>
#include <string.h>
#include "zlib.h"
#include "gzguts.h"
int main(void){
  /* a gzip member of "hi", then 20000 bytes of 'A' */
  gzFile w = gzopen("f.gz","wb"); gzwrite(w,"hi",2); gzclose(w);
  FILE *f=fopen("f.gz","ab"); for(int k=0;k<20000;k++) fputc('A',f); fclose(f);
  gzFile r = gzopen("f.gz","rb"); char buf[4];
  int n = gzread(r,buf,2); printf("read1 %d\n",n);
  n = gzread(r,buf,1); printf("read2 %d eof=%d\n",n,gzeof(r));
  gzclearerr(r);
  n = gzread(r,buf,4); 
  gz_statep s=(gz_statep)r;
  printf("read3 %d how=%d (COPY=1) direct=%d junk=%d gzdirect=%d\n",n,s->how,s->direct,s->junk,gzdirect(r));
  return 0;
}
