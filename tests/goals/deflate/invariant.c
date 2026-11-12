/* Checks the fields of DInv (ZlibF/Proof/deflate.c.universal-invariant.lean) that are scalar
   facts of the C state, at every call boundary of random histories of the real C: deflate with
   every flush, deflateParams, deflateSetDictionary (raw at any block end, zlib before data),
   deflatePrime, deflateTune. Reads the state through deflate.h. Evidence, not proof.
   Usage: invariant [SESSIONS] [SEED]. Exit 1 if a fact fails. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "deflate.h"
static unsigned char in[1<<16], out[1<<17], dict[2048];
static long fails[32]; static const char*names[32];
#define CHK(i,name,cond) do{ names[i]=name; if(!(cond)){ if(fails[i]++<6) printf("FAIL %s seed %u step %d level %d strat %d ml %u ms %u ss %u la %u ma %d ws %u\n",name,seed,step,s->level,s->strategy,s->match_length,s->match_start,s->strstart,s->lookahead,s->match_available,s->w_size);} }while(0)
static void check(deflate_state*s, unsigned seed, int step){
  long span=(long)s->strstart - s->block_start;
  CHK(0,"blockStart", s->block_start <= (long)s->strstart);
  CHK(1,"blockSpan", s->level==0 || span <= 258L*(s->sym_next/3) + s->match_available);
  CHK(2,"levelZero", s->level!=0 || (s->block_start>=0 && s->lookahead==0 && s->sym_next==0));
  CHK(3,"available", !s->match_available || s->strstart>=1);
  CHK(4,"pendingMatch", s->match_length<3 || ((unsigned)(s->strstart-1-s->match_start)>=1 && (unsigned)(s->strstart-1-s->match_start) <= s->w_size-262 && s->match_length<=s->lookahead+1));
  CHK(5,"fastLazy", !(s->level>=1&&s->level<=3&&s->strategy!=2&&s->strategy!=3) || (s->match_length<=2 && s->prev_length<=2));
  CHK(6,"biValid", s->bi_valid<=7);
  CHK(7,"cursor", s->pending!=0 || s->pending_out==s->pending_buf);
  CHK(8,"symRoom", s->sym_next < s->sym_end);
  CHK(9,"matches", s->matches<=2 && (s->level==0 || s->matches==0));
  CHK(10,"insertDone", s->lookahead<3 || s->insert==0);
  CHK(11,"blockClear", s->opt_len==0 && s->static_len==0);
  int bl=1; for(int k=0;k<BL_CODES;k++) if(s->bl_tree[k].Freq) bl=0; CHK(12,"blFreq",bl);
  CHK(13,"insert", s->insert<=s->strstart);
  CHK(14,"room", s->strstart+s->lookahead<=s->window_size);
  CHK(15,"matchAvail01", s->match_available==0||s->match_available==1);
  CHK(16,"lengths", s->prev_length<=258 && s->match_length<=258);
  CHK(20,"P1lastFlush", s->last_flush!=-2 || (s->lookahead==0 && s->sym_next==0 && s->match_available==0 && s->match_length<=2 && s->prev_length<=2 && s->block_start>=0));
  CHK(21,"P2prevLength", s->prev_length<3 || (s->level>=4 && s->strategy!=2 && s->strategy!=3 && s->prev_length < s->match_length));
  CHK(22,"P3symBlock", s->sym_next==0 || s->block_start < (long)s->strstart);
  CHK(23,"P4finish", s->status!=FINISH_STATE || s->sym_next==0);
  CHK(24,"headerSymbols", !(s->status==INIT_STATE||s->status==GZIP_STATE||s->status==EXTRA_STATE||s->status==NAME_STATE||s->status==COMMENT_STATE||s->status==HCRC_STATE) || s->sym_next==0);
  CHK(25,"P5availSlow", !s->match_available || (s->level>=4 && s->strategy!=2 && s->strategy!=3));
  CHK(19,"windowInit", s->strstart + s->lookahead <= s->high_water);
  CHK(18,"headerFlush", !(s->status==INIT_STATE||s->status==GZIP_STATE) || s->last_flush==-2 || s->last_flush==-1);
  if (s->sym_next) { CHK(17,"below", (s->pending_out - s->pending_buf) + s->pending <= s->lit_bufsize); }
}
int main(int argc,char**argv){
  unsigned N=argc>1?atoi(argv[1]):20000; unsigned base=argc>2?atoi(argv[2]):0;
  for(unsigned seed=base;seed<base+N;seed++){
    srand(seed);
    int wb=9+rand()%7, mem=1+rand()%9, lvl=rand()%10, strat=rand()%5, raw=rand()%3;
    z_stream st; memset(&st,0,sizeof st);
    int wbits = raw==0? -wb : raw==1? wb : wb+16;
    if(deflateInit2(&st,lvl,Z_DEFLATED,wbits,mem,strat)!=Z_OK) continue;
    deflate_state*s=(deflate_state*)st.state;
    int alpha=1+rand()%8;
    for(int i=0;i<(int)sizeof in;i++) in[i]= (rand()%5==0)? rand()%256 : 'a'+rand()%alpha;
    for(int i=0;i<(int)sizeof dict;i++) dict[i]='a'+rand()%alpha;
    int pos=0, step=0, started=0;
    check(s,seed,step);
    for(step=1;step<60;step++){
      int op=rand()%10;
      if(op<6){ int n=rand()%3==0? rand()%4000 : rand()%300; if(pos+n>(int)sizeof in) n=sizeof in-pos;
        int fl=(int[]){0,0,0,1,2,3,5,4}[rand()%8]; st.next_in=in+pos; st.avail_in=n;
        int ao=1+rand()%(rand()%2?50:3000); st.next_out=out; st.avail_out=ao;
        int rc=deflate(&st,fl); pos+=n-st.avail_in; started=1;
        if(rc==Z_STREAM_END) break; }
      else if(op<8){ st.next_out=out; st.avail_out=1+rand()%2000; st.next_in=in+pos; st.avail_in=0;
        deflateParams(&st,rand()%10,rand()%5); }
      else if(op==8){ if(raw==0 || !started) deflateSetDictionary(&st,dict,1+rand()%(rand()%2?2000:100)); }
      else { if(!started && rand()%2) deflatePrime(&st,rand()%17,rand()); else deflateTune(&st,rand()%300,rand()%300,rand()%300,rand()%5000); }
      check(s,seed,step);
    }
    deflateEnd(&st);
  }
  long total=0; for(int i=0;i<26;i++){ total+=fails[i]; if(fails[i]) printf("%-14s %ld\n",names[i],fails[i]); }
  printf("invariant: %u sessions, %ld failures\n",N,total);
  return total!=0;
}
