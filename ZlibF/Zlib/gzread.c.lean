import ZlibF.Zlib.«gzlib.c»
import ZlibF.Zlib.«inflate.c»

/-!
# gzread.c — faithful translation

Source: `gzread.c` of the verified source (with `patches/0003-gzread-partial-copy-read-error.patch` and
`patches/0004-gz-position-overflow.patch`), default x86_64 Linux build (`errno`, `EAGAIN == EWOULDBLOCK`,
`STDC`). Reads go through `Zlib.GzFs`.

Patch 0004 (local, F-1): `gz_room` bounds what `gz_look`'s COPY branch buffers, what `gz_fetch` loads and what
`gz_read` and `gzgets` deliver, so that `x.pos` never passes `GZ_OFF_MAX`; data beyond it gives `Z_DATA_ERROR`
"position overflow".

`gz_fetch`, `case COPY` follows the patched C (R-2, upstream PR 1363, applied as patch 0003): `x.next = out` is set
before `gz_load`, so a failing `read` that returned some bytes leaves `x.have != 0` with `x.next` at the new bytes.

`gz_read` leaves `x.next` pointing into the user's buffer after a direct decompression (R-4), and `gz_reset` never
writes it (R-3). With patch 0005 (local), `gz_skip_have` and `gzseek64` advance `x.next` only by a nonzero count, so
neither value is used.

Decisions: `unsigned *have` of `gz_load` is returned (the caller stores it right after the call; nothing in `gz_load`
observes the aliased cell); `unsigned char buf[1]` of `gzgetc` is a local block; `memchr` is `memchrB`.
-/

namespace Zlib.Gzread
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib
open Zlib.Inflate (inflateInit2_ inflateReset inflate inflateEnd)

structure LoadLoop where
  «have» : UInt32
  ret : Int32
  brk : Bool

/-- `local int gz_load(gz_statep state, unsigned char *buf, unsigned len, unsigned *have)`; `*have` is the second
component of the result. -/
def gz_load (state : GzStatePtr) (buf : BPtr) (len : UInt32) : G (Int32 × UInt32) := do
  -- unsigned get, max = ((unsigned)-1 >> 2) + 1;
  let max : UInt32 := (((0 : UInt32) - 1) >>> 2) + 1
  -- state->again = 0; errno = 0; *have = 0;
  updS state fun s => { s with again := 0 }
  setErrno 0
  let l ← gdoWhile
    (fun (l : LoadLoop) => do
      -- get = len - *have; if (get > max) get = max;
      let mut get := len - l.«have»
      if get > max then get := max
      -- ret = (int)read(state->fd, buf + *have, get); if (ret <= 0) break;
      let s ← ldS state
      let p ← buf.add l.«have».toNat
      let (r, bs) ← fsRead s.fd get.toUInt64
      storeBytes p bs
      let ret := r.toInt32
      if ret ≤ 0 then return { l with ret, brk := true }
      -- *have += (unsigned)ret;
      return { l with ret, «have» := l.«have» + ret.toUInt32 })
    (fun l => pure (!l.brk && l.«have» < len, l))
    { «have» := 0, ret := 0, brk := false }
  -- if (ret < 0) { ... }
  if l.ret < 0 then
    let e ← getErrno
    if BLOCKED e then
      updS state fun s => { s with again := 1 }
      if l.«have» != 0 then return (0, l.«have»)
    gz_error state Z_ERRNO (← zstrerror)
    return (-1, l.«have»)
  -- if (ret == 0) state->eof = 1;
  if l.ret == 0 then updS state fun s => { s with eof := 1 }
  return (0, l.«have»)

/-- `local int gz_avail(gz_statep state)` -/
def gz_avail (state : GzStatePtr) : G Int32 := do
  let strm := strmOf state
  let s ← ldS state
  -- if (state->err != Z_OK && state->err != Z_BUF_ERROR) return -1;
  if s.err != Z_OK && s.err != Z_BUF_ERROR then return -1
  -- if (state->eof == 0) { ... }
  if s.eof == 0 then
    let z ← ldZ strm
    -- if (strm->avail_in) { copy what's there to the start }
    if z.avail_in != 0 then
      let p := s.«in»
      let q := z.next_in
      if q != p then
        -- do { *p++ = *q++; } while (--n);
        let _ ← cdoWhile
          (fun (st : BPtr × BPtr × UInt32) => do
            let (p, q, n) := st
            let b ← load8 q
            store8 p b
            return (← p.add 1, ← q.add 1, n))
          (fun (st : BPtr × BPtr × UInt32) => do
            let (p, q, n) := st
            let n := n - 1
            pure (n != 0, (p, q, n)))
          (p, q, z.avail_in)
    -- if (gz_load(state, state->in + strm->avail_in, state->size - strm->avail_in, &got) == -1) return -1;
    let s ← ldS state
    let z ← ldZ strm
    let (r, got) ← gz_load state (← s.«in».add z.avail_in.toNat) (s.size - z.avail_in)
    if r == -1 then return -1
    -- strm->avail_in += got; strm->next_in = state->in;
    let s ← ldS state
    updZ strm fun z => { z with avail_in := z.avail_in + got, next_in := s.«in» }
  return 0

/-- `local unsigned gz_room(gz_statep state, unsigned max)` (patch 0004). `GZ_OFF_MAX - state->x.pos < max`
compares in `z_off64_t` (the `unsigned` operand converts to `long`). -/
def gz_room (state : GzStatePtr) (max : UInt32) : M UInt32 := do
  -- if (state->x.pos > 0 && GZ_OFF_MAX - state->x.pos < max) return (unsigned)(GZ_OFF_MAX - state->x.pos);
  let s ← ldS state
  if s.x.pos > 0 then
    let d ← i64sub GZ_OFF_MAX s.x.pos
    if d < u32ToI64 max then return d.toUInt64.toUInt32
  -- return max;
  return max

/-- `local int gz_look(gz_statep state)` -/
def gz_look (state : GzStatePtr) : G Int32 := do
  let strm := strmOf state
  let s ← ldS state
  -- if (state->size == 0) { allocate read buffers and inflate memory }
  if s.size == 0 then
    -- state->in = malloc(state->want); state->out = malloc(state->want << 1);
    let inb ← allocB s.want.toNat
    updS state fun s => { s with «in» := inb }
    let s ← ldS state
    let outb ← allocB (s.want <<< 1).toNat
    updS state fun s => { s with out := outb }
    -- if (state->in == NULL || state->out == NULL) { free(state->out); free(state->in); gz_error(...); return -1; }
    if inb == .null || outb == .null then
      freeB outb
      freeB inb
      gz_error state Z_MEM_ERROR (← strLit "out of memory")
      return -1
    -- state->size = state->want;
    let s ← ldS state
    updS state fun s => { s with size := s.want }
    -- state->strm.zalloc = Z_NULL; zfree; opaque; avail_in = 0; next_in = Z_NULL;
    updZ strm fun z => { z with zalloc := .null, zfree := .null, «opaque» := .null, avail_in := 0, next_in := .null }
    -- if (inflateInit2(&(state->strm), 15 + 16) != Z_OK) { ... }
    let ver ← strLit ZLIB_VERSION
    let r ← inflateInit2_ strm 31 ver 112
    if r != Z_OK then
      let s ← ldS state
      freeB s.out
      freeB s.«in»
      updS state fun s => { s with size := 0 }
      gz_error state Z_MEM_ERROR (← strLit "out of memory")
      return -1
  -- if (state->direct == -1 || state->junk == 0) { ... }
  let s ← ldS state
  if s.direct == -1 || s.junk == 0 then
    -- if (state->junk == 0 && strm->avail_in == 0) { ... }
    if s.junk == 0 && (← ldZ strm).avail_in == 0 then
      if (← gz_avail state) == -1 then return -1
      if (← ldZ strm).avail_in == 0 then return 0
    -- inflateReset(strm); state->how = GZIP; state->junk = state->junk != -1; state->direct = 0;
    let _ ← inflateReset strm
    updS state fun s => { s with how := GZIP, junk := if s.junk != -1 then 1 else 0, direct := 0 }
    return 0
  -- if (gz_avail(state) == -1) return -1;
  if (← gz_avail state) == -1 then return -1
  -- if (strm->avail_in == 0 || (state->again && strm->avail_in < 4)) return 0;
  let z ← ldZ strm
  let s ← ldS state
  if z.avail_in == 0 || (s.again != 0 && z.avail_in < 4) then return 0
  -- if (strm->avail_in > 3 && next_in[0] == 31 && next_in[1] == 139 && next_in[2] == 8 && next_in[3] < 32) {...}
  let mut isGz := false
  if z.avail_in > 3 then
    if (← index8 z.next_in 0) == 31 then
      if (← index8 z.next_in 1) == 139 then
        if (← index8 z.next_in 2) == 8 then
          if (← index8 z.next_in 3) < 32 then isGz := true
  if isGz then
    let _ ← inflateReset strm
    updS state fun s => { s with how := GZIP, junk := 0, direct := 0 }
    return 0
  -- state->x.next = state->out; memcpy(state->x.next, strm->next_in, strm->avail_in);
  let s ← ldS state
  updX state fun x => { x with next := s.out }
  memcpyB s.out z.next_in z.avail_in.toNat
  -- state->x.have = gz_room(state, strm->avail_in);   (patch 0004)
  let room ← gz_room state z.avail_in
  updX state fun x => { x with «have» := room }
  -- if (state->x.have < strm->avail_in) gz_error(state, Z_DATA_ERROR, "position overflow");   (patch 0004)
  if (← ldS state).x.«have» < (← ldZ strm).avail_in then
    gz_error state Z_DATA_ERROR (← strLit "position overflow")
  -- strm->avail_in = 0; state->how = COPY; return 0;
  updZ strm fun z => { z with avail_in := 0 }
  updS state fun s => { s with how := GZ_COPY }
  return 0

structure DecompLoop where
  ret : Int32
  brk : Bool

/-- `local int gz_decomp(gz_statep state)` -/
def gz_decomp (state : GzStatePtr) : G Int32 := do
  let strm := strmOf state
  -- int ret = Z_OK; had = strm->avail_out;
  let had := (← ldZ strm).avail_out
  let l ← gdoWhile
    (fun (l : DecompLoop) => do
      -- if (strm->avail_in == 0 && gz_avail(state) == -1) { ret = state->err; break; }
      if (← ldZ strm).avail_in == 0 then
        if (← gz_avail state) == -1 then
          return { ret := (← ldS state).err, brk := true }
      -- if (strm->avail_in == 0) { if (!state->again) gz_error(..."unexpected end of file"); break; }
      if (← ldZ strm).avail_in == 0 then
        if (← ldS state).again == 0 then
          gz_error state Z_BUF_ERROR (← strLit "unexpected end of file")
        return { l with brk := true }
      -- ret = inflate(strm, Z_NO_FLUSH);
      let ret ← inflate strm Z_NO_FLUSH
      -- if (strm->avail_out < had) state->junk = 0;
      if (← ldZ strm).avail_out < had then updS state fun s => { s with junk := 0 }
      if ret == Z_STREAM_ERROR || ret == Z_NEED_DICT then
        gz_error state Z_STREAM_ERROR (← strLit "internal error: inflate stream corrupt")
        return { ret, brk := true }
      if ret == Z_MEM_ERROR then
        gz_error state Z_MEM_ERROR (← strLit "out of memory")
        return { ret, brk := true }
      if ret == Z_DATA_ERROR then
        -- if (state->junk == 1) { trailing garbage is ok }
        if (← ldS state).junk == 1 then
          updZ strm fun z => { z with avail_in := 0 }
          updS state fun s => { s with eof := 1, how := LOOK }
          return { ret := Z_OK, brk := true }
        let z ← ldZ strm
        let msg ← if z.msg == .null then strLit "compressed data error" else pure z.msg
        gz_error state Z_DATA_ERROR msg
        return { ret, brk := true }
      return { l with ret })
    (fun l => do
      let z ← ldZ strm
      pure (!l.brk && z.avail_out != 0 && l.ret != Z_STREAM_END, l))
    { ret := Z_OK, brk := false }
  let ret := l.ret
  -- state->x.have = had - strm->avail_out; state->x.next = strm->next_out - state->x.have;
  let z ← ldZ strm
  let hv := had - z.avail_out
  updX state fun x => { x with «have» := hv }
  let nx ← z.next_out.add (-(hv.toNat : Int))
  updX state fun x => { x with next := nx }
  -- if (ret == Z_STREAM_END) { state->junk = 0; state->how = LOOK; return 0; }
  if ret == Z_STREAM_END then
    updS state fun s => { s with junk := 0, how := LOOK }
    return 0
  -- return ret != Z_OK ? -1 : 0;
  return if ret != Z_OK then -1 else 0

/-- `local int gz_fetch(gz_statep state)`. With patches 0003 (upstream PR 1363) and 0004, see the file comment. The
control tag of the loop is the result (`some r`: return `r`). The local `unsigned room` is assigned before each
read. -/
def gz_fetch (state : GzStatePtr) : G Int32 := do
  let strm := strmOf state
  -- if (state->err != Z_OK && state->err != Z_BUF_ERROR && !state->again) return -1;
  let s ← ldS state
  if s.err != Z_OK && s.err != Z_BUF_ERROR && s.again == 0 then return -1
  let r ← gdoWhile
    (fun (r : Option Int32) => do
      -- switch (state->how)
      let s ← ldS state
      if s.how == LOOK then
        -- case LOOK
        if (← gz_look state) == -1 then return some (-1)
        if (← ldS state).how == LOOK then return some 0
        return none
      else if s.how == GZ_COPY then
        -- case COPY: room = gz_room(state, state->size << 1);
        let room ← gz_room state (s.size <<< 1)
        -- state->x.next = state->out;
        updX state fun x => { x with next := s.out }
        -- if (gz_load(state, state->out, room ? room : 1, &(state->x.have)) == -1) return -1;
        let s ← ldS state
        let (r, hv) ← gz_load state s.out (if room != 0 then room else 1)
        updX state fun x => { x with «have» := hv }
        if r == -1 then return some (-1)
        -- return 0;
        return some 0
      else if s.how == GZIP then
        -- case GZIP: room = gz_room(state, state->size << 1);
        let room ← gz_room state (s.size <<< 1)
        -- strm->avail_out = room ? room : 1; strm->next_out = state->out;
        updZ strm fun z => { z with avail_out := if room != 0 then room else 1, next_out := s.out }
        if (← gz_decomp state) == -1 then return some (-1)
        return none
      else
        -- default
        gz_error state Z_STREAM_ERROR (← strLit "state corrupt")
        return some (-1))
    (fun r => do
      if r.isSome then return (false, r)
      -- while (state->x.have == 0 && (!state->eof || strm->avail_in))
      let s ← ldS state
      if s.x.«have» != 0 then return (false, r)
      if s.eof == 0 then return (true, r)
      return ((← ldZ strm).avail_in != 0, r))
    none
  return r.getD 0

/-- `local void gz_skip_have(gz_statep state)`. With patch 0005: `x.next` is advanced only when `n != 0` (R-3,
R-4). -/
def gz_skip_have (state : GzStatePtr) : M Unit := do
  let s ← ldS state
  -- n = GT_OFF(state->x.have) || (z_off64_t)state->x.have > state->skip ? (unsigned)state->skip : state->x.have;
  let n : UInt32 ← if (← GT_OFF s.x.«have») || u32ToI64 s.x.«have» > s.skip then pure s.skip.toUInt64.toUInt32
    else pure s.x.«have»
  -- state->x.have -= n;
  updX state fun x => { x with «have» := x.«have» - n }
  -- if (n) state->x.next += n;   (patch 0005)
  if n != 0 then
    let s ← ldS state
    let nx ← s.x.next.add n.toNat
    updX state fun x => { x with next := nx }
  -- state->x.pos += n; state->skip -= n;
  let s ← ldS state
  let np ← i64add s.x.pos (u32ToI64 n)
  updX state fun x => { x with pos := np }
  let s ← ldS state
  let sk ← i64sub s.skip (u32ToI64 n)
  updS state fun s => { s with skip := sk }

/-- `local int gz_skip(gz_statep state)`; the loop tag `some r` means break (`0`) or `return -1`. -/
def gz_skip (state : GzStatePtr) : G Int32 := do
  let strm := strmOf state
  let r ← gdoWhile
    (fun (_ : Option Int32) => do
      let s ← ldS state
      -- if (state->x.have) gz_skip_have(state);
      if s.x.«have» != 0 then
        gz_skip_have state
        return none
      -- else if (state->eof && state->strm.avail_in == 0) { ... break; }
      else if s.eof != 0 && (← ldZ strm).avail_in == 0 then
        if s.how == GZIP && s.err == Z_OK then
          gz_error state Z_BUF_ERROR (← strLit "unexpected end of file")
        updS state fun s => { s with skip := 0, past := 1 }
        return some 0
      -- else { if (gz_fetch(state) == -1 && state->x.have == 0) return -1; }
      else
        if (← gz_fetch state) == -1 && (← ldS state).x.«have» == 0 then return some (-1)
        return none)
    (fun r => do
      if r.isSome then return (false, r)
      -- while (state->skip)
      return ((← ldS state).skip != 0, r))
    none
  return r.getD 0

structure ReadLoop where
  got : UInt64
  len : UInt64
  buf : BPtr
  err : Int32
  brk : Bool

/-- `local z_size_t gz_read(gz_statep state, voidp buf, z_size_t len)`. The direct decompression into the user's
buffer leaves `x.next` pointing into it (R-4; harmless with patch 0005). -/
def gz_read (state : GzStatePtr) (buf : BPtr) (len : UInt64) : G UInt64 := do
  let strm := strmOf state
  -- if (len == 0) return 0;
  if len == 0 then return 0
  -- if (state->skip && gz_skip(state) == -1) return 0;
  if (← ldS state).skip != 0 then
    if (← gz_skip state) == -1 then return 0
  -- got = 0; err = 0; do { ... } while (len && !err);
  let l ← gdoWhile
    (fun (l : ReadLoop) => do
      -- n = (unsigned)-1; if (n > len) n = (unsigned)len;
      let mut n : UInt32 := 0xFFFFFFFF
      if n.toUInt64 > l.len then n := l.len.toUInt32
      -- n = gz_room(state, n);
      n ← gz_room state n
      -- if (n == 0 && state->x.have) { state->x.have = 0; gz_error(state, Z_DATA_ERROR, "position overflow"); break; }
      if n == 0 && (← ldS state).x.«have» != 0 then
        updX state fun x => { x with «have» := 0 }
        gz_error state Z_DATA_ERROR (← strLit "position overflow")
        return { l with brk := true }
      let s ← ldS state
      let mut l := l
      if s.x.«have» != 0 then
        -- first just try copying data from the output buffer
        if s.x.«have» < n then n := s.x.«have»
        memcpyB l.buf s.x.next n.toNat
        let nx ← s.x.next.add n.toNat
        updX state fun x => { x with next := nx, «have» := x.«have» - n }
        if (← ldS state).err != Z_OK then l := { l with err := -1 }
      else if s.eof != 0 && (← ldZ strm).avail_in == 0 then
        -- output buffer empty -- return if we're at the end of the input
        if s.how == GZIP && s.err == Z_OK then
          gz_error state Z_BUF_ERROR (← strLit "unexpected end of file")
        return { l with brk := true }
      else if s.how == LOOK || n < (s.size <<< 1) then
        -- need output data -- for small len or new stream load up our output buffer
        if (← gz_fetch state) == -1 && (← ldS state).x.«have» == 0 then l := { l with err := -1 }
        return l          -- continue
      else if s.how == GZ_COPY then
        -- large len -- read directly into user buffer: err = gz_load(state, buf, n, &n);
        let (e, nn) ← gz_load state l.buf n
        l := { l with err := e }
        n := nn
      else
        -- large len -- decompress directly into user buffer
        updZ strm fun z => { z with avail_out := n, next_out := l.buf }
        let e ← gz_decomp state
        l := { l with err := e }
        n := (← ldS state).x.«have»
        updX state fun x => { x with «have» := 0 }
      -- len -= n; buf = (char *)buf + n; got += n; state->x.pos += n;
      let buf ← l.buf.add n.toNat
      let s ← ldS state
      let np ← i64add s.x.pos (u32ToI64 n)
      updX state fun x => { x with pos := np }
      return { l with len := l.len - n.toUInt64, buf, got := l.got + n.toUInt64 })
    (fun l => pure (!l.brk && l.len != 0 && l.err == 0, l))
    { got := 0, len, buf, err := 0, brk := false }
  -- if (len && state->eof) state->past = 1;
  if l.len != 0 && (← ldS state).eof != 0 then updS state fun s => { s with past := 1 }
  return l.got

/-- `int ZEXPORT gzread(gzFile file, voidp buf, unsigned len)` -/
def gzread (file : GzFilePtr) (buf : BPtr) (len : UInt32) : G Int32 := do
  if file.isNone then return -1
  let state := castState file
  let s ← ldS state
  if s.mode != GZ_READ then return -1
  -- if (state->err != Z_OK && state->err != Z_BUF_ERROR && !state->again && state->x.have == 0) return -1;
  if s.err != Z_OK && s.err != Z_BUF_ERROR && s.again == 0 && s.x.«have» == 0 then return -1
  -- if (state->again) gz_error(state, Z_OK, NULL);
  if s.again != 0 then gz_error state Z_OK .null
  -- if ((int)len < 0) { ... return -1; }
  if len.toInt32 < 0 then
    let s ← ldS state
    if s.err == Z_OK || s.err == Z_BUF_ERROR then
      gz_error state Z_STREAM_ERROR (← strLit "request does not fit in an int")
    return -1
  -- len = (unsigned)gz_read(state, buf, len);
  let len : UInt32 := (← gz_read state buf len.toUInt64).toUInt32
  -- if (len == 0) { ... }
  if len == 0 then
    let s ← ldS state
    if s.err != Z_OK && s.err != Z_BUF_ERROR then return -1
    if s.again != 0 then
      gz_error state Z_ERRNO (← zstrerror)
      return -1
  return len.toInt32

/-- `z_size_t ZEXPORT gzfread(voidp buf, z_size_t size, z_size_t nitems, gzFile file)` -/
def gzfread (buf : BPtr) (size nitems : UInt64) (file : GzFilePtr) : G UInt64 := do
  if file.isNone then return 0
  let state := castState file
  let s ← ldS state
  if s.mode != GZ_READ then return 0
  if s.err != Z_OK && s.err != Z_BUF_ERROR && s.again == 0 && s.x.«have» == 0 then return 0
  if s.again != 0 then gz_error state Z_OK .null
  -- len = nitems * size; if (size && len / size != nitems) { ... return 0; }
  let len := nitems * size
  if size != 0 && len / size != nitems then
    let s ← ldS state
    if s.err == Z_OK || s.err == Z_BUF_ERROR then
      gz_error state Z_STREAM_ERROR (← strLit "request does not fit in a size_t")
    return 0
  -- return len ? gz_read(state, buf, len) / size : 0;
  if len != 0 then return (← gz_read state buf len) / size else return 0

/-- `int ZEXPORT gzgetc(gzFile file)` -/
def gzgetc (file : GzFilePtr) : G Int32 := do
  -- unsigned char buf[1];
  if file.isNone then return -1
  let state := castState file
  let s ← ldS state
  if s.mode != GZ_READ then return -1
  if s.err != Z_OK && s.err != Z_BUF_ERROR && s.again == 0 && s.x.«have» == 0 then return -1
  if s.again != 0 then gz_error state Z_OK .null
  -- if (state->x.have) { state->x.have--; state->x.pos++; return *(state->x.next)++; }
  let s ← ldS state
  if s.x.«have» != 0 then
    updX state fun x => { x with «have» := x.«have» - 1 }
    let np ← i64add s.x.pos 1
    updX state fun x => { x with pos := np }
    let s ← ldS state
    let b ← load8 s.x.next
    let nx ← s.x.next.add 1
    updX state fun x => { x with next := nx }
    return b.toUInt32.toInt32
  -- return gz_read(state, buf, 1) < 1 ? -1 : buf[0];
  let buf ← allocLocal 1
  let got ← gz_read state buf 1
  let r ← if got < 1 then pure (-1 : Int32) else do pure (← load8 buf).toUInt32.toInt32
  freeB buf
  return r

/-- `int ZEXPORT gzgetc_(gzFile file)` -/
def gzgetc_ (file : GzFilePtr) : G Int32 := gzgetc file

/-- `int ZEXPORT gzungetc(int c, gzFile file)` -/
def gzungetc (c : Int32) (file : GzFilePtr) : G Int32 := do
  if file.isNone then return -1
  let state := castState file
  let s ← ldS state
  if s.mode != GZ_READ then return -1
  -- if (state->how == LOOK && state->x.have == 0) (void)gz_look(state);
  if s.how == LOOK && s.x.«have» == 0 then
    let _ ← gz_look state
  -- if (state->err != Z_OK && state->err != Z_BUF_ERROR && !state->again && state->size == 0) return -1;
  let s ← ldS state
  if s.err != Z_OK && s.err != Z_BUF_ERROR && s.again == 0 && s.size == 0 then return -1
  if s.again != 0 then gz_error state Z_OK .null
  -- if (state->skip && gz_skip(state) == -1) return -1;
  if (← ldS state).skip != 0 then
    if (← gz_skip state) == -1 then return -1
  -- if (c < 0) return -1;
  if c < 0 then return -1
  -- if (state->x.have == 0) { ... return c; }
  let s ← ldS state
  if s.x.«have» == 0 then
    updX state fun x => { x with «have» := 1 }
    let p ← (← s.out.add (s.size <<< 1).toNat).add (-1)
    updX state fun x => { x with next := p }
    store8 p c.toUInt32.toUInt8
    let s ← ldS state
    let np ← i64sub s.x.pos 1
    updX state fun x => { x with pos := np }
    updS state fun s => { s with past := 0 }
    return c
  -- if (state->x.have == (state->size << 1)) { ... return -1; }
  if s.x.«have» == (s.size <<< 1) then
    if s.err == Z_OK || s.err == Z_BUF_ERROR then
      gz_error state Z_DATA_ERROR (← strLit "out of room to push characters")
    return -1
  -- if (state->x.next == state->out) { slide output data }
  if s.x.next == s.out then
    let src0 ← s.out.add s.x.«have».toNat
    let dest0 ← s.out.add (s.size <<< 1).toNat
    -- while (src > state->out) *--dest = *--src;
    let (_, dest) ← cwhile
      (fun (st : BPtr × BPtr) => do
        pure (← Ptr.lt s.out st.1, st))
      (fun (st : BPtr × BPtr) => do
        let dest ← st.2.add (-1)
        let src ← st.1.add (-1)
        store8 dest (← load8 src)
        return (src, dest))
      (src0, dest0)
    updX state fun x => { x with next := dest }
  -- state->x.have++; state->x.next--; state->x.next[0] = (unsigned char)c; state->x.pos--; state->past = 0;
  updX state fun x => { x with «have» := x.«have» + 1 }
  let s ← ldS state
  let nx ← s.x.next.add (-1)
  updX state fun x => { x with next := nx }
  store8 nx c.toUInt32.toUInt8
  let s ← ldS state
  let np ← i64sub s.x.pos 1
  updX state fun x => { x with pos := np }
  updS state fun s => { s with past := 0 }
  return c

structure GetsLoop where
  left : UInt32
  buf : BPtr
  eol : BPtr
  brk : Bool

/-- `char * ZEXPORT gzgets(gzFile file, char *buf, int len)` -/
def gzgets (file : GzFilePtr) (buf : BPtr) (len : Int32) : G BPtr := do
  -- if (file == NULL || buf == NULL || len < 1) return NULL;
  if file.isNone || buf == .null || len < 1 then return .null
  let state := castState file
  let s ← ldS state
  if s.mode != GZ_READ then return .null
  if s.err != Z_OK && s.err != Z_BUF_ERROR && s.again == 0 && s.x.«have» == 0 then return .null
  if s.again != 0 then gz_error state Z_OK .null
  if (← ldS state).skip != 0 then
    if (← gz_skip state) == -1 then return .null
  -- str = buf; left = (unsigned)len - 1;
  let str := buf
  let left : UInt32 := len.toUInt32 - 1
  let mut buf := buf
  -- if (left) do { ... } while (left && eol == NULL);
  if left != 0 then
    let l ← gdoWhile
      (fun (l : GetsLoop) => do
        -- if (state->x.have == 0 && gz_fetch(state) == -1 && state->x.have == 0) break;
        if (← ldS state).x.«have» == 0 then
          if (← gz_fetch state) == -1 then
            if (← ldS state).x.«have» == 0 then return { l with brk := true }
        -- if (state->x.have == 0) { state->past = 1; break; }
        if (← ldS state).x.«have» == 0 then
          updS state fun s => { s with past := 1 }
          return { l with brk := true }
        -- n = state->x.have > left ? left : state->x.have;
        let s ← ldS state
        let mut n : UInt32 := if s.x.«have» > l.left then l.left else s.x.«have»
        -- n = gz_room(state, n);
        n ← gz_room state n
        -- if (n == 0) { state->x.have = 0; gz_error(state, Z_DATA_ERROR, "position overflow"); break; }
        if n == 0 then
          updX state fun x => { x with «have» := 0 }
          gz_error state Z_DATA_ERROR (← strLit "position overflow")
          return { l with brk := true }
        -- eol = memchr(state->x.next, '\n', n);
        let eol ← memchrB s.x.next 10 n.toNat
        -- if (eol != NULL) n = (unsigned)(eol - state->x.next) + 1;
        if eol != .null then
          let d ← Ptr.diff eol s.x.next
          n := d.toUInt64.toUInt32 + 1
        -- memcpy(buf, state->x.next, n); have -= n; next += n; pos += n; left -= n; buf += n;
        memcpyB l.buf s.x.next n.toNat
        updX state fun x => { x with «have» := x.«have» - n }
        let s ← ldS state
        let nx ← s.x.next.add n.toNat
        updX state fun x => { x with next := nx }
        let s ← ldS state
        let np ← i64add s.x.pos (u32ToI64 n)
        updX state fun x => { x with pos := np }
        return { l with left := l.left - n, buf := ← l.buf.add n.toNat, eol })
      (fun l => pure (!l.brk && l.left != 0 && l.eol == .null, l))
      { left, buf, eol := .null, brk := false }
    buf := l.buf
  -- if (buf == str && len > 1) return NULL; buf[0] = 0; return str;
  if buf == str && len > 1 then return .null
  store8 buf 0
  return str

/-- `int ZEXPORT gzdirect(gzFile file)` -/
def gzdirect (file : GzFilePtr) : G Int32 := do
  if file.isNone then return 0
  let state := castState file
  let s ← ldS state
  -- if (state->mode == GZ_READ && state->how == LOOK && state->x.have == 0) { (void)gz_look(state); gz_skip_have(state); }
  if s.mode == GZ_READ && s.how == LOOK && s.x.«have» == 0 then
    let _ ← gz_look state
    gz_skip_have state
  -- return state->direct == 1;
  return if (← ldS state).direct == 1 then 1 else 0

/-- `int ZEXPORT gzclose_r(gzFile file)` -/
def gzclose_r (file : GzFilePtr) : G Int32 := do
  if file.isNone then return Z_STREAM_ERROR
  let state := castState file
  let s ← ldS state
  if s.mode != GZ_READ then return Z_STREAM_ERROR
  -- if (state->size) { inflateEnd(&(state->strm)); free(state->out); free(state->in); }
  if s.size != 0 then
    let _ ← inflateEnd (strmOf state)
    freeB s.out
    freeB s.«in»
  -- err = state->err == Z_BUF_ERROR ? Z_BUF_ERROR : Z_OK;
  let err : Int32 := if s.err == Z_BUF_ERROR then Z_BUF_ERROR else Z_OK
  gz_error state Z_OK .null
  -- free(state->path); ret = close(state->fd); free(state);
  let s ← ldS state
  freeB s.path
  let ret ← fsClose s.fd
  freeGzState state
  return if ret != 0 then Z_ERRNO else err

end Zlib.Gzread
