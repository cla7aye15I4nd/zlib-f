import ZlibF.Zlib.«inflate.c»

/-!
# infback.c — faithful translation

Source: `infback.c` of the verified source, default x86_64 Linux build (same configuration as `inflate.c.lean`; read its
header first: the registers, the monad `X`, `goto inf_leave` as `throw Ex.leave`, the loops).

## The call-backs

`inflateBack` takes the caller's functions as parameters (they are caller code, not library code):

* `in_func`: `unsigned (*)(void *in_desc, z_const unsigned char **buf)` is `InCb`. The C passes `&next`, the address of
  the local `next`. A pointer to a scalar is passed by value (decision D3 of the notes): the call-back receives the
  current value of `next` and returns `(count, new value of *buf)`. A call-back that keeps the address and writes
  through it after it returned is not modelled.
* `out_func`: `int (*)(void *out_desc, unsigned char *buf, unsigned len)` is `OutCb`.

Both run on the shared heap, so they can read and write any block. `inflateBack` makes no assumption about them; a
theorem about it has to state what it needs (`docs/translation-notes/inflate-side.md`, section 9.4).

## Other decisions

* `inflateBackInit_` does **not** zero the state: the record is `allocInflateState`, arbitrary integers and null
  pointers, and only the fields the C writes are written.
* `ret` is not initialised in the C before `for (;;)`; it is set before every `goto inf_leave`. It starts as `0` here.
-/

namespace Zlib.Infback
open C
open Zlib.Crc32 (crc32)
open Zlib.Inffast (inflate_fast)
open Zlib.Inftrees (inflate_table inflate_fixed)
open Zlib.Inflate (X Ex IL Stop xwhile xwhileBrk xdoWhile xloopBrk shl32 shr32 shl64 u2i i2u chkI32 BITS DROPBITS BYTEBITS
  INITBITS LOAD RESTORE rdS wrS rdZ wrZ lensP workP codesP orderAt setMsg setMode ZALLOCS ZFREES)

/-- `in_func`: `unsigned (*)(void FAR *, z_const unsigned char FAR * FAR *)`; see the file comment. -/
abbrev InCb := BPtr → BPtr → M (UInt32 × BPtr)
/-- `out_func`: `int (*)(void FAR *, unsigned char FAR *, unsigned)` -/
abbrev OutCb := BPtr → BPtr → UInt32 → M Int32

/-- What `inflateBack()` and its macros share. -/
structure BCtx where
  strm : ZStreamPtr
  st : InflateStatePtr
  inCb : InCb
  inDesc : BPtr
  outCb : OutCb
  outDesc : BPtr

/-- `int ZEXPORT inflateBackInit_(z_streamp strm, int windowBits, unsigned char FAR *window, const char *version,
int stream_size)` -/
def inflateBackInit_ (strm : ZStreamPtr) (windowBits : Int32) (window : BPtr) (version : BPtr) (stream_size : Int32) :
    M Int32 := do
  -- if (version == Z_NULL || version[0] != ZLIB_VERSION[0] || stream_size != (int)(sizeof(z_stream))) return Z_VERSION_ERROR;
  if version == .null then return Z_VERSION_ERROR
  if (← index8 version 0) != 49 then return Z_VERSION_ERROR
  if stream_size != 112 then return Z_VERSION_ERROR
  -- if (strm == Z_NULL || window == Z_NULL || windowBits < 8 || windowBits > 15) return Z_STREAM_ERROR;
  if strm == none || window == .null || windowBits < 8 || windowBits > 15 then return Z_STREAM_ERROR
  -- strm->msg = Z_NULL;
  wrZ strm fun z => { z with msg := .null }
  -- if (strm->zalloc == (alloc_func)0) { strm->zalloc = zcalloc; strm->opaque = (voidpf)0; }
  if (← rdZ strm (·.zalloc)) == .null then
    wrZ strm fun z => { z with zalloc := .fn "zcalloc", «opaque» := .null }
  -- if (strm->zfree == (free_func)0) strm->zfree = zcfree;
  if (← rdZ strm (·.zfree)) == .null then
    wrZ strm fun z => { z with zfree := .fn "zcfree" }
  -- state = (struct inflate_state FAR *)ZALLOC(strm, 1, sizeof(struct inflate_state));   (not zeroed)
  let state ← ZALLOCS strm
  -- if (state == Z_NULL) return Z_MEM_ERROR;
  if state == none then return Z_MEM_ERROR
  -- strm->state = (struct internal_state FAR *)state;
  wrZ strm fun z => { z with state := StateRef.ofInflateState state }
  -- state->dmax = 32768U; state->wbits = (uInt)windowBits; state->wsize = 1U << windowBits;
  let ws ← shl32 1 (i2u windowBits)
  -- state->window = window; state->wnext = 0; state->whave = 0; state->sane = 1;
  wrS state fun s => { s with
    dmax := 32768, wbits := i2u windowBits, wsize := ws, window := window, wnext := 0, whave := 0, sane := 1 }
  return Z_OK

/-! ## The macros of `infback.c` that differ from `inflate.c` -/

/-- `PULL()`: calls the caller's `in` when `have == 0`; `goto inf_leave` with `next = NULL`, `ret = Z_BUF_ERROR` if it
returns 0. -/
def PULL (c : BCtx) : X Unit := do
  let l ← get
  if l.have_ == 0 then
    -- have = in(in_desc, &next);
    let (h, nx) ← c.inCb c.inDesc l.next
    set { l with have_ := h, next := nx }
    if h == 0 then
      -- next = Z_NULL; ret = Z_BUF_ERROR; goto inf_leave;
      set { l with have_ := h, next := .null, ret := Z_BUF_ERROR }
      throw Ex.leave

/-- `PULLBYTE()` -/
def PULLBYTE (c : BCtx) : X Unit := do
  PULL c
  let l ← get
  -- have--; hold += (unsigned long)(*next++) << bits; bits += 8;
  let b ← load8 l.next
  let nx ← l.next.add 1
  let sh ← shl64 b.toUInt64 l.bits
  set { l with have_ := l.have_ - 1, next := nx, hold := l.hold + sh, bits := l.bits + 8 }

/-- `NEEDBITS(n)` -/
def NEEDBITS (c : BCtx) (n : UInt32) : X Unit :=
  xwhile (do return (← get).bits < n) (PULLBYTE c)

/-- `ROOM()`: when the window is full, hand it to `out`. -/
def ROOM (c : BCtx) : X Unit := do
  let l ← get
  if l.left == 0 then
    -- put = state->window; left = state->wsize; state->whave = left;
    let s ← ldInflateState c.st
    set { l with put := s.window, left := s.wsize }
    wrS c.st fun s => { s with whave := s.wsize }
    -- if (out(out_desc, put, left)) { ret = Z_BUF_ERROR; goto inf_leave; }
    if (← c.outCb c.outDesc s.window s.wsize) != 0 then
      modify fun l => { l with ret := Z_BUF_ERROR }
      throw Ex.leave

/-- `strm->msg = "..."; state->mode = BAD;` -/
def badMode (c : BCtx) (msg : String) : M Unit := do
  setMsg c.strm msg
  setMode c.st BAD

/-- `for (;;) { here = TABLE[BITS(bitsOfTable)]; if ((unsigned)(here.bits) <= bits) break; PULLBYTE(); }` -/
def lookup1 (c : BCtx) (dist : Bool) : X Unit :=
  xloopBrk (do
    let s ← ldInflateState c.st
    let tab := if dist then s.distcode else s.lencode
    let nb := if dist then s.distbits else s.lenbits
    let b ← BITS nb
    let here ← Ptr.index tab (b.toNat : Int)
    modify fun l => { l with here := here }
    if here.bits.toUInt32 <= (← get).bits then return true
    PULLBYTE c
    return false)

/-- `for (;;) { here = TABLE[last.val + (BITS(last.bits + last.op) >> last.bits)]; if ((unsigned)(last.bits + here.bits) <= bits) break; PULLBYTE(); }` -/
def lookup2 (c : BCtx) (dist : Bool) : X Unit :=
  xloopBrk (do
    let s ← ldInflateState c.st
    let tab := if dist then s.distcode else s.lencode
    let last := (← get).last
    let b ← BITS (last.bits.toUInt32 + last.op.toUInt32)
    let sh ← shr32 b last.bits.toUInt32
    let here ← Ptr.index tab ((last.val.toUInt32 + sh).toNat : Int)
    modify fun l => { l with here := here }
    if (last.bits.toUInt32 + here.bits.toUInt32) <= (← get).bits then return true
    PULLBYTE c
    return false)

/-! ## The modes -/

/-- `case LEN:` -/
def back_LEN (c : BCtx) : X Unit := do
  let l ← get
  -- if (have >= 6 && left >= 258) { RESTORE(); inflate_fast(strm, state->wsize); LOAD(); break; }
  if l.have_ >= 6 && l.left >= 258 then
    RESTORE c.strm c.st
    inflate_fast c.strm (← rdS c.st (·.wsize))
    LOAD c.strm c.st
    return
  lookup1 c false
  let here := (← get).here
  -- if (here.op && (here.op & 0xf0) == 0) {
  if here.op != 0 && (here.op &&& 0xf0) == 0 then
    modify fun l => { l with last := here }
    lookup2 c false
    DROPBITS (← get).last.bits.toUInt32
  -- DROPBITS(here.bits); state->length = (unsigned)here.val;
  let here := (← get).here
  DROPBITS here.bits.toUInt32
  wrS c.st fun s => { s with length := here.val.toUInt32 }
  -- if (here.op == 0) { ROOM(); *put++ = (unsigned char)(state->length); left--; state->mode = LEN; break; }
  if here.op == 0 then
    ROOM c
    let l ← get
    store8 l.put (← ldInflateState c.st).length.toUInt8
    let p ← l.put.add 1
    set { l with put := p, left := l.left - 1 }
    setMode c.st LEN
    return
  -- if (here.op & 32) { state->mode = TYPE; break; }
  if (here.op &&& 32) != 0 then
    setMode c.st TYPE
    return
  -- if (here.op & 64) { "invalid literal/length code"; BAD; break; }
  if (here.op &&& 64) != 0 then
    badMode c "invalid literal/length code"
    return
  -- state->extra = (unsigned)(here.op) & 15; if (state->extra != 0) { NEEDBITS; length += BITS(extra); DROPBITS(extra); }
  wrS c.st fun s => { s with extra := here.op.toUInt32 &&& 15 }
  let ex := here.op.toUInt32 &&& 15
  if ex != 0 then
    NEEDBITS c ex
    let b ← BITS ex
    wrS c.st fun s => { s with length := s.length + b }
    DROPBITS ex
  -- get distance code
  lookup1 c true
  let here := (← get).here
  if (here.op &&& 0xf0) == 0 then
    modify fun l => { l with last := here }
    lookup2 c true
    DROPBITS (← get).last.bits.toUInt32
  let here := (← get).here
  DROPBITS here.bits.toUInt32
  -- if (here.op & 64) { "invalid distance code"; BAD; break; }
  if (here.op &&& 64) != 0 then
    badMode c "invalid distance code"
    return
  -- state->offset = (unsigned)here.val; state->extra = (unsigned)(here.op) & 15;
  wrS c.st fun s => { s with offset := here.val.toUInt32, extra := here.op.toUInt32 &&& 15 }
  let ex := here.op.toUInt32 &&& 15
  if ex != 0 then
    NEEDBITS c ex
    let b ← BITS ex
    wrS c.st fun s => { s with offset := s.offset + b }
    DROPBITS ex
  -- if (state->offset > state->wsize - (state->whave < state->wsize ? left : 0)) { "invalid distance too far back"; BAD; break; }
  let s ← ldInflateState c.st
  let l ← get
  if s.offset > s.wsize - (if s.whave < s.wsize then l.left else 0) then
    badMode c "invalid distance too far back"
    return
  -- do { ROOM(); copy = state->wsize - state->offset; ...; do { *put++ = *from++; } while (--copy); } while (state->length != 0);
  xdoWhile
    (do
      ROOM c
      let s ← ldInflateState c.st
      let l ← get
      -- copy = state->wsize - state->offset;
      let copy := s.wsize - s.offset
      -- if (copy < left) { from = put + copy; copy = left - copy; } else { from = put - state->offset; copy = left; }
      let (from_, copy) ← if copy < l.left then do
          pure (← l.put.add (copy.toNat : Int), l.left - copy)
        else do
          pure (← l.put.add (-(s.offset.toNat : Int)), l.left)
      -- if (copy > state->length) copy = state->length;
      let copy := if copy > s.length then s.length else copy
      -- state->length -= copy; left -= copy;
      wrS c.st fun s => { s with length := s.length - copy }
      set { l with copy := copy, from_ := from_, left := l.left - copy }
      xdoWhile
        (do
          let l ← get
          let b ← load8 l.from_
          store8 l.put b
          let p ← l.put.add 1
          let f ← l.from_.add 1
          set { l with put := p, from_ := f })
        (do
          let l ← get
          let n := l.copy - 1
          set { l with copy := n }
          return n != 0))
    (do return (← rdS c.st (·.length)) != 0)

/-- `case TABLE:` (falls through into `LEN`) -/
def back_TABLE (c : BCtx) : X Unit := do
  NEEDBITS c 14
  let b ← BITS 5
  wrS c.st fun s => { s with nlen := b + 257 }
  DROPBITS 5
  let b ← BITS 5
  wrS c.st fun s => { s with ndist := b + 1 }
  DROPBITS 5
  let b ← BITS 4
  wrS c.st fun s => { s with ncode := b + 4 }
  DROPBITS 4
  -- if (state->nlen > 286 || state->ndist > 30) { "too many length or distance symbols"; BAD; break; }
  let s ← ldInflateState c.st
  if s.nlen > 286 || s.ndist > 30 then
    badMode c "too many length or distance symbols"
    return
  -- state->have = 0; while (state->have < state->ncode) { NEEDBITS(3); lens[order[have++]] = BITS(3); DROPBITS(3); }
  wrS c.st fun s => { s with «have» := 0 }
  xwhile
    (do let s ← ldInflateState c.st; return s.«have» < s.ncode)
    (do
      NEEDBITS c 3
      let s ← ldInflateState c.st
      wrS c.st fun s => { s with «have» := s.«have» + 1 }
      let o ← orderAt s.«have»
      let b ← BITS 3
      Ptr.store (← (lensP c.st).add (o.toNat : Int)) b.toUInt16
      DROPBITS 3)
  xwhile
    (do let s ← ldInflateState c.st; return s.«have» < 19)
    (do
      let s ← ldInflateState c.st
      wrS c.st fun s => { s with «have» := s.«have» + 1 }
      let o ← orderAt s.«have»
      Ptr.store (← (lensP c.st).add (o.toNat : Int)) (0 : UInt16))
  -- state->next = state->codes; state->lencode = (code const FAR *)(state->next); state->lenbits = 7;
  wrS c.st fun s => { s with next := codesP c.st, lencode := codesP c.st, lenbits := 7 }
  let s ← ldInflateState c.st
  let (r, nx, lb) ← inflate_table CODES (lensP c.st) 19 s.next s.lenbits (workP c.st)
  wrS c.st fun s => { s with next := nx, lenbits := lb }
  modify fun l => { l with ret := r }
  if r != 0 then
    badMode c "invalid code lengths set"
    return
  -- state->have = 0; while (state->have < state->nlen + state->ndist) { ... }
  wrS c.st fun s => { s with «have» := 0 }
  xwhileBrk
    (do let s ← ldInflateState c.st; return s.«have» < s.nlen + s.ndist)
    (do
      lookup1 c false
      let here := (← get).here
      if here.val < 16 then
        DROPBITS here.bits.toUInt32
        let s ← ldInflateState c.st
        Ptr.store (← (lensP c.st).add (s.«have».toNat : Int)) here.val
        wrS c.st fun s => { s with «have» := s.«have» + 1 }
        return false
      else
        if here.val == 16 then
          NEEDBITS c (here.bits.toUInt32 + 2)
          DROPBITS here.bits.toUInt32
          let s ← ldInflateState c.st
          if s.«have» == 0 then
            badMode c "invalid bit length repeat"
            return true
          -- len = (unsigned)(state->lens[state->have - 1]); copy = 3 + BITS(2); DROPBITS(2);
          let v ← Ptr.index (lensP c.st) ((s.«have» - 1).toNat : Int)
          let b ← BITS 2
          modify fun l => { l with len := v.toUInt32, copy := 3 + b }
          DROPBITS 2
        else if here.val == 17 then
          NEEDBITS c (here.bits.toUInt32 + 3)
          DROPBITS here.bits.toUInt32
          let b ← BITS 3
          modify fun l => { l with len := 0, copy := 3 + b }
          DROPBITS 3
        else
          NEEDBITS c (here.bits.toUInt32 + 7)
          DROPBITS here.bits.toUInt32
          let b ← BITS 7
          modify fun l => { l with len := 0, copy := 11 + b }
          DROPBITS 7
        let s ← ldInflateState c.st
        if s.«have» + (← get).copy > s.nlen + s.ndist then
          badMode c "invalid bit length repeat"
          return true
        xwhile
          (do
            let l ← get
            set { l with copy := l.copy - 1 }
            return l.copy != 0)
          (do
            let s ← ldInflateState c.st
            Ptr.store (← (lensP c.st).add (s.«have».toNat : Int)) (← get).len.toUInt16
            wrS c.st fun s => { s with «have» := s.«have» + 1 })
        return false)
  -- if (state->mode == BAD) break;
  if (← rdS c.st (·.mode)) == BAD then return
  -- if (state->lens[256] == 0) { "invalid code -- missing end-of-block"; BAD; break; }
  if (← Ptr.index (lensP c.st) 256) == (0 : UInt16) then
    badMode c "invalid code -- missing end-of-block"
    return
  wrS c.st fun s => { s with next := codesP c.st, lencode := codesP c.st, lenbits := 9 }
  let s ← ldInflateState c.st
  let (r, nx, lb) ← inflate_table LENS (lensP c.st) s.nlen s.next s.lenbits (workP c.st)
  wrS c.st fun s => { s with next := nx, lenbits := lb }
  modify fun l => { l with ret := r }
  if r != 0 then
    badMode c "invalid literal/lengths set"
    return
  wrS c.st fun s => { s with distcode := s.next, distbits := 6 }
  let s ← ldInflateState c.st
  let (r, nx, db) ← inflate_table DISTS (← (lensP c.st).add (s.nlen.toNat : Int)) s.ndist s.next s.distbits (workP c.st)
  wrS c.st fun s => { s with next := nx, distbits := db }
  modify fun l => { l with ret := r }
  if r != 0 then
    badMode c "invalid distances set"
    return
  -- state->mode = LEN; /* fallthrough */
  setMode c.st LEN
  back_LEN c

/-- `case STORED:` -/
def back_STORED (c : BCtx) : X Unit := do
  BYTEBITS
  NEEDBITS c 32
  let l ← get
  if (l.hold &&& (0xffff : UInt64)) != ((l.hold >>> 16) ^^^ (0xffff : UInt64)) then
    badMode c "invalid stored block lengths"
    return
  wrS c.st fun s => { s with length := l.hold.toUInt32 &&& 0xffff }
  INITBITS
  -- while (state->length != 0) { copy = state->length; PULL(); ROOM(); ... }
  xwhile
    (do return (← rdS c.st (·.length)) != 0)
    (do
      let s ← ldInflateState c.st
      modify fun l => { l with copy := s.length }
      PULL c
      ROOM c
      let l ← get
      let mut copy := l.copy
      if copy > l.have_ then copy := l.have_
      if copy > l.left then copy := l.left
      memcpyB l.put l.next copy.toNat
      let nx ← l.next.add (copy.toNat : Int)
      let pt ← l.put.add (copy.toNat : Int)
      set { l with copy := copy, have_ := l.have_ - copy, next := nx, left := l.left - copy, put := pt }
      wrS c.st fun s => { s with length := s.length - copy })
  setMode c.st TYPE

/-- `case TYPE:` -/
def back_TYPE (c : BCtx) : X Unit := do
  -- if (state->last) { BYTEBITS(); state->mode = DONE; break; }
  if (← rdS c.st (·.last)) != 0 then
    BYTEBITS
    setMode c.st DONE
    return
  NEEDBITS c 3
  let b ← BITS 1
  wrS c.st fun s => { s with last := u2i b }
  DROPBITS 1
  match (← BITS 2) with
  | 0 => setMode c.st STORED
  | 1 =>
    inflate_fixed c.st
    setMode c.st LEN
  | 2 => setMode c.st TABLE
  | _ => badMode c "invalid block type"
  DROPBITS 2

/-- The `switch (state->mode)` of `inflateBack()`. -/
def back_dispatch (c : BCtx) : X Unit := do
  let m ← rdS c.st (·.mode)
  if m == TYPE then back_TYPE c
  else if m == STORED then back_STORED c
  else if m == TABLE then back_TABLE c
  else if m == LEN then back_LEN c
  else if m == DONE then
    -- ret = Z_STREAM_END; goto inf_leave;
    modify fun l => { l with ret := Z_STREAM_END }
    throw Ex.leave
  else if m == BAD then
    modify fun l => { l with ret := Z_DATA_ERROR }
    throw Ex.leave
  else
    -- default: ret = Z_STREAM_ERROR; goto inf_leave;
    modify fun l => { l with ret := Z_STREAM_ERROR }
    throw Ex.leave

/-- `int ZEXPORT inflateBack(z_streamp strm, in_func in, void FAR *in_desc, out_func out, void FAR *out_desc)` -/
def inflateBack (strm : ZStreamPtr) (inCb : InCb) (in_desc : BPtr) (outCb : OutCb) (out_desc : BPtr) : M Int32 := do
  -- if (strm == Z_NULL || strm->state == Z_NULL) return Z_STREAM_ERROR;
  if strm == none then return Z_STREAM_ERROR
  let z ← ldZStream strm
  if z.state == none then return Z_STREAM_ERROR
  -- state = (struct inflate_state FAR *)strm->state;
  let st ← castInflateState z.state
  -- strm->msg = Z_NULL; state->mode = TYPE; state->last = 0; state->whave = 0;
  wrZ strm fun z => { z with msg := .null }
  wrS st fun s => { s with mode := TYPE, last := 0, whave := 0 }
  -- next = strm->next_in; have = next != Z_NULL ? strm->avail_in : 0; hold = 0; bits = 0;
  let z ← ldZStream strm
  let s ← ldInflateState st
  let next := z.next_in
  let have_ := if next != .null then z.avail_in else 0
  -- put = state->window; left = state->wsize;
  let l0 : IL := { IL.init with next := next, have_ := have_, hold := 0, bits := 0, put := s.window, left := s.wsize }
  let c : BCtx := { strm, st, inCb, inDesc := in_desc, outCb, outDesc := out_desc }
  -- for (;;) switch (state->mode) { ... }
  let (_, l) ← StateT.run (ExceptT.run (xwhile (pure true) (back_dispatch c))) l0
  -- inf_leave: if (left < state->wsize) { if (out(out_desc, state->window, state->wsize - left) && ret == Z_STREAM_END) ret = Z_BUF_ERROR; }
  let s ← ldInflateState st
  let mut ret := l.ret
  if l.left < s.wsize then
    if (← outCb out_desc s.window (s.wsize - l.left)) != 0 && ret == Z_STREAM_END then ret := Z_BUF_ERROR
  -- strm->next_in = next; strm->avail_in = have; return ret;
  wrZ strm fun z => { z with next_in := l.next, avail_in := l.have_ }
  return ret

/-- `int ZEXPORT inflateBackEnd(z_streamp strm)` -/
def inflateBackEnd (strm : ZStreamPtr) : M Int32 := do
  -- if (strm == Z_NULL || strm->state == Z_NULL || strm->zfree == (free_func)0) return Z_STREAM_ERROR;
  if strm == none then return Z_STREAM_ERROR
  let z ← ldZStream strm
  if z.state == none || z.zfree == .null then return Z_STREAM_ERROR
  -- ZFREE(strm, strm->state); strm->state = Z_NULL;
  let st ← castInflateState z.state
  ZFREES strm st
  wrZ strm fun z => { z with state := none }
  return Z_OK

end Zlib.Infback
