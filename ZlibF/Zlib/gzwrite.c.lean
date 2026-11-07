import ZlibF.Zlib.«gzlib.c»
import ZlibF.Zlib.«deflate.c»

/-!
# gzwrite.c — faithful translation

Source: `gzwrite.c` of the verified source (unpatched), default x86_64 Linux build. `STDC` is defined, so
`gz_vacate`, `gzvprintf` and the `va_list` version of `gzprintf` are compiled; `HAVE_VSNPRINTF` is defined and
`HAS_vsnprintf_void` is not, so the live call is `len = vsnprintf(next, state->size, format, va);`. The old-style
`gzprintf` with twenty `int` arguments is not compiled.

Decisions: `gzvprintf`/`gzprintf` take the variadic arguments as a list `VaArg` (`Zlib.GzFs`); `vsnprintf` is the
model of `gzfs.lean`. `unsigned char buf[1]` of `gzputc` is a local block freed before every return.
`write` goes through `GzFs.fsWrite`: the bytes it writes are read from the heap first (a fault if the range is not
inside its object).
-/

namespace Zlib.Gzwrite
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib
open Zlib.Deflate (deflateInit2_ deflateReset deflate deflateParams deflateEnd)

/-- `local int gz_init(gz_statep state)` -/
def gz_init (state : GzStatePtr) : G Int32 := do
  let strm := strmOf state
  -- state->in = (unsigned char *)malloc(state->want << 1);
  let s ← ldS state
  let inb ← allocB (s.want <<< 1).toNat
  updS state fun s => { s with «in» := inb }
  if inb == .null then
    gz_error state Z_MEM_ERROR (← strLit "out of memory")
    return -1
  -- if (!state->direct) { ... }
  let s ← ldS state
  if s.direct == 0 then
    -- state->out = (unsigned char *)malloc(state->want);
    let outb ← allocB s.want.toNat
    updS state fun s => { s with out := outb }
    if outb == .null then
      freeB (← ldS state).«in»
      gz_error state Z_MEM_ERROR (← strLit "out of memory")
      return -1
    -- strm->zalloc = Z_NULL; strm->zfree = Z_NULL; strm->opaque = Z_NULL;
    updZ strm fun z => { z with zalloc := .null, zfree := .null, «opaque» := .null }
    -- ret = deflateInit2(strm, state->level, Z_DEFLATED, MAX_WBITS + 16, DEF_MEM_LEVEL, state->strategy);
    let s ← ldS state
    let ver ← strLit ZLIB_VERSION
    let ret ← deflateInit2_ strm s.level Z_DEFLATED (MAX_WBITS + 16) DEF_MEM_LEVEL s.strategy ver 112
    if ret != Z_OK then
      let s ← ldS state
      freeB s.out
      freeB s.«in»
      gz_error state Z_MEM_ERROR (← strLit "out of memory")
      return -1
  -- strm->next_in = NULL;
  updZ strm fun z => { z with next_in := .null }
  -- state->size = state->want;
  updS state fun s => { s with size := s.want }
  -- if (!state->direct) { strm->avail_out = state->size; strm->next_out = state->out; state->x.next = strm->next_out; }
  let s ← ldS state
  if s.direct == 0 then
    updZ strm fun z => { z with avail_out := s.size, next_out := s.out }
    let z ← ldZ strm
    updX state fun x => { x with next := z.next_out }
  return 0

structure CompLoop where
  ret : Int32
  «have» : UInt32
  res : Option Int32

/-- `local int gz_comp(gz_statep state, int flush)`. `max` is `((unsigned)-1 >> 2) + 1`; the `return -1` inside the
loops is the tag `res`. -/
def gz_comp (state : GzStatePtr) (flush : Int32) : G Int32 := do
  let strm := strmOf state
  let max : UInt32 := (((0 : UInt32) - 1) >>> 2) + 1
  -- if (state->size == 0 && gz_init(state) == -1) return -1;
  if (← ldS state).size == 0 then
    if (← gz_init state) == -1 then return -1
  -- if (state->direct) { while (strm->avail_in) {...} return 0; }
  if (← ldS state).direct != 0 then
    let r ← gwhile
      (fun (r : Option Int32) => do
        if r.isSome then return (false, r)
        return ((← ldZ strm).avail_in != 0, r))
      (fun _ => do
        setErrno 0
        updS state fun s => { s with again := 0 }
        let z ← ldZ strm
        let s ← ldS state
        let put : UInt32 := if z.avail_in > max then max else z.avail_in
        let bs ← loadBytes z.next_in put.toNat
        let writ := (← fsWrite s.fd bs).toInt32
        if writ < 0 then
          if BLOCKED (← getErrno) then updS state fun s => { s with again := 1 }
          gz_error state Z_ERRNO (← zstrerror)
          return some (-1)
        let z ← ldZ strm
        let np ← z.next_in.add writ.toInt
        updZ strm fun z => { z with avail_in := z.avail_in - writ.toUInt32, next_in := np }
        return none)
      none
    return r.getD 0
  -- if (state->reset) { ... }
  if (← ldS state).reset != 0 then
    let z ← ldZ strm
    if z.avail_in == 0 && flush == Z_NO_FLUSH then return 0
    let _ ← deflateReset strm
    updS state fun s => { s with reset := 0 }
  -- ret = Z_OK; do { ... } while (have);
  let l ← gdoWhile
    (fun (l : CompLoop) => do
      let z ← ldZ strm
      let mut l := l
      -- if (strm->avail_out == 0 || (flush != Z_NO_FLUSH && (flush != Z_FINISH || ret == Z_STREAM_END))) {
      if z.avail_out == 0 || (flush != Z_NO_FLUSH && (flush != Z_FINISH || l.ret == Z_STREAM_END)) then
        -- while (strm->next_out > state->x.next) {
        let r ← gwhile
          (fun (r : Option Int32) => do
            if r.isSome then return (false, r)
            let z ← ldZ strm
            let s ← ldS state
            return (← Ptr.lt s.x.next z.next_out, r))
          (fun _ => do
            setErrno 0
            updS state fun s => { s with again := 0 }
            let z ← ldZ strm
            let s ← ldS state
            -- put = next_out - x.next > (int)max ? max : (unsigned)(next_out - x.next);
            let d ← Ptr.diff z.next_out s.x.next
            let put : UInt32 := if d > (Int64.ofNat max.toNat) then max else d.toUInt64.toUInt32
            let bs ← loadBytes s.x.next put.toNat
            let writ := (← fsWrite s.fd bs).toInt32
            if writ < 0 then
              if BLOCKED (← getErrno) then updS state fun s => { s with again := 1 }
              gz_error state Z_ERRNO (← zstrerror)
              return some (-1)
            let s ← ldS state
            let nx ← s.x.next.add writ.toInt
            updX state fun x => { x with next := nx }
            return none)
          none
        if r.isSome then return { l with res := r }
        -- if (strm->avail_out == 0) { strm->avail_out = state->size; next_out = out; x.next = out; }
        if (← ldZ strm).avail_out == 0 then
          let s ← ldS state
          updZ strm fun z => { z with avail_out := s.size, next_out := s.out }
          updX state fun x => { x with next := s.out }
      -- have = strm->avail_out; ret = deflate(strm, flush);
      let hv := (← ldZ strm).avail_out
      let ret ← deflate strm flush
      if ret == Z_STREAM_ERROR then
        gz_error state Z_STREAM_ERROR (← strLit "internal error: deflate stream corrupt")
        return { l with ret, res := some (-1) }
      -- have -= strm->avail_out;
      return { l with ret, «have» := hv - (← ldZ strm).avail_out })
    (fun l => pure (l.res.isNone && l.«have» != 0, l))
    { ret := Z_OK, «have» := 0, res := none }
  if let some r := l.res then return r
  -- if (flush == Z_FINISH) state->reset = 1;
  if flush == Z_FINISH then updS state fun s => { s with reset := 1 }
  return 0

structure ZeroLoop where
  first : Bool
  res : Option Int32

/-- `local int gz_zero(gz_statep state)` -/
def gz_zero (state : GzStatePtr) : G Int32 := do
  let strm := strmOf state
  -- if (state->size == 0 && gz_init(state) == -1) return -1;
  if (← ldS state).size == 0 then
    if (← gz_init state) == -1 then return -1
  -- if (strm->avail_in && gz_comp(state, Z_NO_FLUSH) == -1) return -1;
  if (← ldZ strm).avail_in != 0 then
    if (← gz_comp state Z_NO_FLUSH) == -1 then return -1
  -- first = 1; do { ... } while (state->skip);
  let l ← gdoWhile
    (fun (l : ZeroLoop) => do
      let s ← ldS state
      -- n = GT_OFF(state->size) || (z_off64_t)state->size > state->skip ? (unsigned)state->skip : state->size;
      let mut n : UInt32 ← if (← GT_OFF s.size) || u32ToI64 s.size > s.skip then pure s.skip.toUInt64.toUInt32
        else pure s.size
      let mut first := l.first
      if first then
        memsetB s.«in» 0 n.toNat
        first := false
      -- strm->avail_in = n; strm->next_in = state->in; ret = gz_comp(state, Z_NO_FLUSH);
      updZ strm fun z => { z with avail_in := n, next_in := s.«in» }
      let ret ← gz_comp state Z_NO_FLUSH
      -- n -= strm->avail_in; state->x.pos += n; state->skip -= n;
      n := n - (← ldZ strm).avail_in
      let s ← ldS state
      let np ← i64add s.x.pos (u32ToI64 n)
      updX state fun x => { x with pos := np }
      let s ← ldS state
      let sk ← i64sub s.skip (u32ToI64 n)
      updS state fun s => { s with skip := sk }
      if ret == -1 then
        let s ← ldS state
        updZ strm fun z => { z with avail_in := 0, next_in := s.«in» }
        return { first, res := some (-1) }
      return { first, res := none })
    (fun l => do
      if l.res.isSome then return (false, l)
      return ((← ldS state).skip != 0, l))
    { first := true, res := none }
  return l.res.getD 0

structure WriteLoop where
  len : UInt64
  buf : BPtr
  res : Option UInt64
  brk : Bool

/-- `local z_size_t gz_write(gz_statep state, voidpc buf, z_size_t len)` -/
def gz_write (state : GzStatePtr) (buf : BPtr) (len : UInt64) : G UInt64 := do
  let strm := strmOf state
  -- z_size_t put = len;
  let put := len
  -- if (len == 0) return 0;
  if len == 0 then return 0
  -- if (state->size == 0 && gz_init(state) == -1) return 0;
  if (← ldS state).size == 0 then
    if (← gz_init state) == -1 then return 0
  -- if (state->skip && gz_zero(state) == -1) return 0;
  if (← ldS state).skip != 0 then
    if (← gz_zero state) == -1 then return 0
  -- if (len < state->size) { for (;;) {...} }
  if len < (← ldS state).size.toUInt64 then
    let l ← gwhile
      (fun (l : WriteLoop) => pure (!l.brk && l.res.isNone, l))
      (fun (l : WriteLoop) => do
        -- if (state->strm.avail_in == 0) state->strm.next_in = state->in;
        if (← ldZ strm).avail_in == 0 then
          let s ← ldS state
          updZ strm fun z => { z with next_in := s.«in» }
        -- have = (unsigned)((state->strm.next_in + state->strm.avail_in) - state->in);
        let z ← ldZ strm
        let s ← ldS state
        let tp ← z.next_in.add z.avail_in.toNat
        let hv : UInt32 := (← Ptr.diff tp s.«in»).toUInt64.toUInt32
        -- copy = state->size - have; if (copy > len) copy = (unsigned)len;
        let mut copy := s.size - hv
        if copy.toUInt64 > l.len then copy := l.len.toUInt32
        -- memcpy(state->in + have, buf, copy);
        memcpyB (← s.«in».add hv.toNat) l.buf copy.toNat
        -- state->strm.avail_in += copy; state->x.pos += copy;
        updZ strm fun z => { z with avail_in := z.avail_in + copy }
        let s ← ldS state
        let np ← i64add s.x.pos (u32ToI64 copy)
        updX state fun x => { x with pos := np }
        -- buf = (const char *)buf + copy; len -= copy;
        let buf ← l.buf.add copy.toNat
        let len := l.len - copy.toUInt64
        -- if (len == 0) break;
        if len == 0 then return { l with buf, len, brk := true }
        -- if (gz_comp(state, Z_NO_FLUSH) == -1) return state->again ? put - len : 0;
        if (← gz_comp state Z_NO_FLUSH) == -1 then
          return { l with buf, len, res := some (if (← ldS state).again != 0 then put - len else 0) }
        return { l with buf, len })
      { len, buf, res := none, brk := false }
    if let some r := l.res then return r
  else
    -- if (state->strm.avail_in && gz_comp(state, Z_NO_FLUSH) == -1) return 0;
    if (← ldZ strm).avail_in != 0 then
      if (← gz_comp state Z_NO_FLUSH) == -1 then return 0
    -- state->strm.next_in = (z_const Bytef *)buf;
    updZ strm fun z => { z with next_in := buf }
    -- do { unsigned n = (unsigned)-1; ... } while (len);
    let l ← gdoWhile
      (fun (l : WriteLoop) => do
        let mut n : UInt32 := 0xFFFFFFFF
        if n.toUInt64 > l.len then n := l.len.toUInt32
        updZ strm fun z => { z with avail_in := n }
        let ret ← gz_comp state Z_NO_FLUSH
        n := n - (← ldZ strm).avail_in
        let s ← ldS state
        let np ← i64add s.x.pos (u32ToI64 n)
        updX state fun x => { x with pos := np }
        let len := l.len - n.toUInt64
        if ret == -1 then
          let s ← ldS state
          updZ strm fun z => { z with avail_in := 0, next_in := s.«in» }
          return { l with len, res := some (if s.again != 0 then put - len else 0) }
        return { l with len })
      (fun l => pure (l.res.isNone && l.len != 0, l))
      { len, buf, res := none, brk := false }
    if let some r := l.res then return r
    -- state->strm.next_in = state->in;
    let s ← ldS state
    updZ strm fun z => { z with next_in := s.«in» }
  -- return put;
  return put

/-- `int ZEXPORT gzwrite(gzFile file, voidpc buf, unsigned len)` -/
def gzwrite (file : GzFilePtr) (buf : BPtr) (len : UInt32) : G Int32 := do
  if file.isNone then return 0
  let state := castState file
  let s ← ldS state
  -- if (state->mode != GZ_WRITE || (state->err != Z_OK && !state->again)) return 0;
  if s.mode != GZ_WRITE || (s.err != Z_OK && s.again == 0) then return 0
  gz_error state Z_OK .null
  -- if ((int)len < 0) { gz_error(state, Z_DATA_ERROR, "requested length does not fit in int"); return 0; }
  if len.toInt32 < 0 then
    gz_error state Z_DATA_ERROR (← strLit "requested length does not fit in int")
    return 0
  -- return (int)gz_write(state, buf, len);
  return (← gz_write state buf len.toUInt64).toUInt32.toInt32

/-- `z_size_t ZEXPORT gzfwrite(voidpc buf, z_size_t size, z_size_t nitems, gzFile file)` -/
def gzfwrite (buf : BPtr) (size nitems : UInt64) (file : GzFilePtr) : G UInt64 := do
  if file.isNone then return 0
  let state := castState file
  let s ← ldS state
  if s.mode != GZ_WRITE || (s.err != Z_OK && s.again == 0) then return 0
  gz_error state Z_OK .null
  -- len = nitems * size; if (size && len / size != nitems) { ... return 0; }
  let len := nitems * size
  if size != 0 && len / size != nitems then
    gz_error state Z_STREAM_ERROR (← strLit "request does not fit in a size_t")
    return 0
  -- return len ? gz_write(state, buf, len) / size : 0;
  if len != 0 then return (← gz_write state buf len) / size else return 0

/-- `int ZEXPORT gzputc(gzFile file, int c)` -/
def gzputc (file : GzFilePtr) (c : Int32) : G Int32 := do
  -- unsigned have; unsigned char buf[1];
  if file.isNone then return -1
  let state := castState file
  let strm := strmOf state
  let s ← ldS state
  if s.mode != GZ_WRITE || (s.err != Z_OK && s.again == 0) then return -1
  gz_error state Z_OK .null
  -- if (state->skip && gz_zero(state) == -1) return -1;
  if (← ldS state).skip != 0 then
    if (← gz_zero state) == -1 then return -1
  -- if (state->size) { ... }
  if (← ldS state).size != 0 then
    if (← ldZ strm).avail_in == 0 then
      let s ← ldS state
      updZ strm fun z => { z with next_in := s.«in» }
    let z ← ldZ strm
    let s ← ldS state
    let tp ← z.next_in.add z.avail_in.toNat
    let hv : UInt32 := (← Ptr.diff tp s.«in»).toUInt64.toUInt32
    if hv < s.size then
      store8 (← s.«in».add hv.toNat) c.toUInt32.toUInt8
      updZ strm fun z => { z with avail_in := z.avail_in + 1 }
      let np ← i64add s.x.pos 1
      updX state fun x => { x with pos := np }
      return c &&& 0xff
  -- buf[0] = (unsigned char)c; if (gz_write(state, buf, 1) != 1) return -1; return c & 0xff;
  let buf ← allocLocal 1
  store8 buf c.toUInt32.toUInt8
  let w ← gz_write state buf 1
  freeB buf
  if w != 1 then return -1
  return c &&& 0xff

/-- `int ZEXPORT gzputs(gzFile file, const char *s)` -/
def gzputs (file : GzFilePtr) (str : BPtr) : G Int32 := do
  if file.isNone then return -1
  let state := castState file
  let s ← ldS state
  if s.mode != GZ_WRITE || (s.err != Z_OK && s.again == 0) then return -1
  gz_error state Z_OK .null
  -- len = strlen(s); if ((int)len < 0 || (unsigned)len != len) { ... return -1; }
  let len ← strlenB str
  if len.toUInt32.toInt32 < 0 || len.toUInt32.toUInt64 != len then
    gz_error state Z_STREAM_ERROR (← strLit "string length does not fit in int")
    return -1
  -- put = gz_write(state, s, len); return len && put == 0 ? -1 : (int)put;
  let put ← gz_write state str len
  return if len != 0 && put == 0 then -1 else put.toUInt32.toInt32

/-- `local int gz_vacate(gz_statep state)` -/
def gz_vacate (state : GzStatePtr) : G Int32 := do
  let strm := strmOf state
  -- if (strm->next_in == NULL || strm->next_in + strm->avail_in <= state->in + state->size) return 0;
  let z ← ldZ strm
  if z.next_in == .null then return 0
  let s ← ldS state
  let a ← z.next_in.add z.avail_in.toNat
  let b ← s.«in».add s.size.toNat
  if (← Ptr.le a b) then return 0
  -- (void)gz_comp(state, Z_NO_FLUSH);
  let _ ← gz_comp state Z_NO_FLUSH
  -- if (strm->avail_in == 0) { strm->next_in = state->in; return 0; }
  if (← ldZ strm).avail_in == 0 then
    let s ← ldS state
    updZ strm fun z => { z with next_in := s.«in» }
    return 0
  -- memmove(state->in, strm->next_in, strm->avail_in); strm->next_in = state->in;
  let z ← ldZ strm
  let s ← ldS state
  memmoveB s.«in» z.next_in z.avail_in.toNat
  updZ strm fun z => { z with next_in := s.«in» }
  -- return strm->avail_in > state->size;
  return if (← ldZ strm).avail_in > s.size then 1 else 0

/-- `int ZEXPORTVA gzvprintf(gzFile file, const char *format, va_list va)` -/
def gzvprintf (file : GzFilePtr) (format : BPtr) (va : List VaArg) : G Int32 := do
  if file.isNone then return Z_STREAM_ERROR
  let state := castState file
  let strm := strmOf state
  let s ← ldS state
  if s.mode != GZ_WRITE || (s.err != Z_OK && s.again == 0) then return Z_STREAM_ERROR
  gz_error state Z_OK .null
  -- if (state->size == 0 && gz_init(state) == -1) return state->err;
  if (← ldS state).size == 0 then
    if (← gz_init state) == -1 then return (← ldS state).err
  -- if (state->skip && gz_zero(state) == -1) return state->err;
  if (← ldS state).skip != 0 then
    if (← gz_zero state) == -1 then return (← ldS state).err
  -- ret = gz_vacate(state);
  let ret ← gz_vacate state
  let s ← ldS state
  if s.err != 0 then
    if ret != 0 && s.again != 0 then
      gz_error state Z_BUF_ERROR (← strLit "stalled write on gzprintf")
      return (← ldS state).err
    if s.again == 0 then return s.err
  -- if (strm->avail_in == 0) strm->next_in = state->in;
  if (← ldZ strm).avail_in == 0 then
    let s ← ldS state
    updZ strm fun z => { z with next_in := s.«in» }
  -- next = (char *)(state->in + (strm->next_in - state->in) + strm->avail_in);
  let z ← ldZ strm
  let s ← ldS state
  let d ← Ptr.diff z.next_in s.«in»
  let next ← (← s.«in».add d.toInt).add z.avail_in.toNat
  -- next[state->size - 1] = 0;
  store8 (← next.add (s.size - 1).toNat) 0
  -- len = vsnprintf(next, state->size, format, va);
  let len ← vsnprintf next s.size.toUInt64 format va
  -- if (len == 0 || (unsigned)len >= state->size || next[state->size - 1] != 0) return 0;
  if len == 0 || len.toUInt32 ≥ s.size then return 0
  if (← index8 next (s.size - 1).toNat) != 0 then return 0
  -- strm->avail_in += (unsigned)len; state->x.pos += len;
  updZ strm fun z => { z with avail_in := z.avail_in + len.toUInt32 }
  let s ← ldS state
  let np ← i64add s.x.pos len.toInt64
  updX state fun x => { x with pos := np }
  -- ret = gz_vacate(state); if (ret) { ... }
  let ret ← gz_vacate state
  if ret != 0 then
    updZ strm fun z => { z with avail_in := z.avail_in - len.toUInt32 }
    let s ← ldS state
    let np ← i64sub s.x.pos len.toInt64
    updX state fun x => { x with pos := np }
    if (← ldS state).again != 0 then
      gz_error state Z_BUF_ERROR (← strLit "stalled write on gzprintf")
    return (← ldS state).err
  -- if (state->err && !state->again) return state->err; return len;
  let s ← ldS state
  if s.err != 0 && s.again == 0 then return s.err
  return len

/-- `int ZEXPORTVA gzprintf(gzFile file, const char *format, ...)`: `va_start` / `gzvprintf` / `va_end`. -/
def gzprintf (file : GzFilePtr) (format : BPtr) (va : List VaArg) : G Int32 :=
  gzvprintf file format va

/-- `int ZEXPORT gzflush(gzFile file, int flush)` -/
def gzflush (file : GzFilePtr) (flush : Int32) : G Int32 := do
  if file.isNone then return Z_STREAM_ERROR
  let state := castState file
  let s ← ldS state
  if s.mode != GZ_WRITE || (s.err != Z_OK && s.again == 0) then return Z_STREAM_ERROR
  gz_error state Z_OK .null
  -- if (flush < 0 || flush > Z_FINISH) return Z_STREAM_ERROR;
  if flush < 0 || flush > Z_FINISH then return Z_STREAM_ERROR
  -- if (state->skip && gz_zero(state) == -1) return state->err;
  if (← ldS state).skip != 0 then
    if (← gz_zero state) == -1 then return (← ldS state).err
  -- (void)gz_comp(state, flush); return state->err;
  let _ ← gz_comp state flush
  return (← ldS state).err

/-- `int ZEXPORT gzsetparams(gzFile file, int level, int strategy)`. Candidate finding (unconfirmed): the result
(`Z_BUF_ERROR`) of `deflateParams` is ignored and the new level and strategy are stored anyway; see
`docs/design/external-io.md`. -/
def gzsetparams (file : GzFilePtr) (level strategy : Int32) : G Int32 := do
  if file.isNone then return Z_STREAM_ERROR
  let state := castState file
  let strm := strmOf state
  let s ← ldS state
  -- if (state->mode != GZ_WRITE || (state->err != Z_OK && !state->again) || state->direct) return Z_STREAM_ERROR;
  if s.mode != GZ_WRITE || (s.err != Z_OK && s.again == 0) || s.direct != 0 then return Z_STREAM_ERROR
  gz_error state Z_OK .null
  -- if (level == state->level && strategy == state->strategy) return Z_OK;
  let s ← ldS state
  if level == s.level && strategy == s.strategy then return Z_OK
  -- if (state->skip && gz_zero(state) == -1) return state->err;
  if s.skip != 0 then
    if (← gz_zero state) == -1 then return (← ldS state).err
  -- if (state->size) { ... }
  if (← ldS state).size != 0 then
    if (← ldZ strm).avail_in != 0 then
      if (← gz_comp state Z_BLOCK) == -1 then return (← ldS state).err
    let _ ← deflateParams strm level strategy
  -- state->level = level; state->strategy = strategy; return Z_OK;
  updS state fun s => { s with level, strategy }
  return Z_OK

/-- `int ZEXPORT gzclose_w(gzFile file)` -/
def gzclose_w (file : GzFilePtr) : G Int32 := do
  let mut ret := Z_OK
  if file.isNone then return Z_STREAM_ERROR
  let state := castState file
  let s ← ldS state
  -- if (state->mode != GZ_WRITE) return Z_STREAM_ERROR;
  if s.mode != GZ_WRITE then return Z_STREAM_ERROR
  -- if (state->skip && gz_zero(state) == -1) ret = state->err;
  if s.skip != 0 then
    if (← gz_zero state) == -1 then ret := (← ldS state).err
  -- if (gz_comp(state, Z_FINISH) == -1) ret = state->err;
  if (← gz_comp state Z_FINISH) == -1 then ret := (← ldS state).err
  -- if (state->size) { if (!state->direct) { (void)deflateEnd(&(state->strm)); free(state->out); } free(state->in); }
  let s ← ldS state
  if s.size != 0 then
    if s.direct == 0 then
      let _ ← deflateEnd (strmOf state)
      freeB s.out
    freeB s.«in»
  -- gz_error(state, Z_OK, NULL); free(state->path);
  gz_error state Z_OK .null
  let s ← ldS state
  freeB s.path
  -- if (close(state->fd) == -1) ret = Z_ERRNO;
  if (← fsClose s.fd) == -1 then ret := Z_ERRNO
  -- free(state); return ret;
  freeGzState state
  return ret

end Zlib.Gzwrite
