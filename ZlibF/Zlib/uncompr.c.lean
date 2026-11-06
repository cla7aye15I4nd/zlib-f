import ZlibF.Zlib.«gzguts.h»
import ZlibF.Zlib.«inflate.c»

/-!
# uncompr.c — faithful translation

Source: `uncompr.c` of the verified source, default x86_64 Linux build.

Decisions (see `docs/translation-notes/gz-files.md`):
* `z_stream stream;` is a local record made by `allocLocalZ` (no allocation oracle: automatic storage cannot fail),
  with arbitrary content, and freed before every return.
* `(Bytef *)&stream.reserved` (D-5) is a local 8-byte block, freed before every return. It is only ever passed as
  `next_out` with `avail_out == 0`.
* A pointer to a scalar (`z_size_t *destLen`, `uLong *sourceLen`) is a pointer to an 8-byte block holding the
  value in little-endian order (`load64`/`store64` of `gzguts.h.lean`).
* `inflateInit(&stream)` is `inflateInit_(&stream, ZLIB_VERSION, (int)sizeof(z_stream))`, `sizeof(z_stream) == 112`.
-/

namespace Zlib.Uncompr
open C Zlib.GzFs Zlib.Gzguts
open Zlib.Inflate (inflateInit_ inflate inflateEnd)

/-- A local `z_stream`: a fresh record with arbitrary integers and null pointers, outside the allocation oracle
(automatic storage cannot fail). Made by the runtime allocator `allocZStream` with the oracle set to succeed. -/
def allocLocalZ : M ZStreamPtr := fun h =>
  match allocZStream { h with allocOk := fun _ => true } with
  | .ok (p, h') => .ok (p, { h' with allocOk := h.allocOk, nalloc := h.nalloc })
  | .error e => .error e

structure UncLoop where
  err : Int32
  len : UInt64
  left : UInt64

/-- `int ZEXPORT uncompress2_z(Bytef *dest, z_size_t *destLen, const Bytef *source, z_size_t *sourceLen)` -/
def uncompress2_z (dest : BPtr) (destLen : BPtr) (source : BPtr) (sourceLen : BPtr) : M Int32 := do
  -- z_stream stream; int err; const uInt max = (uInt)-1; z_size_t len, left;
  let stream ← allocLocalZ
  let reserved ← allocLocal 8
  let max : UInt32 := 0xFFFFFFFF
  let free : M Unit := do
    freeB reserved
    freeZStream stream
  -- if (sourceLen == Z_NULL || (*sourceLen > 0 && source == Z_NULL) || destLen == Z_NULL || (*destLen > 0 && dest == Z_NULL))
  --   return Z_STREAM_ERROR;
  let mut bad := false
  if sourceLen == .null then bad := true
  else if (← load64 sourceLen) > 0 && source == .null then bad := true
  else if destLen == .null then bad := true
  else if (← load64 destLen) > 0 && dest == .null then bad := true
  if bad then
    free
    return Z_STREAM_ERROR
  -- len = *sourceLen; left = *destLen;
  let len ← load64 sourceLen
  let left ← load64 destLen
  -- if (left == 0 && dest == Z_NULL) dest = (Bytef *)&stream.reserved;
  let dest := if left == 0 && dest == .null then reserved else dest
  -- stream.next_in = (z_const Bytef *)source; stream.avail_in = 0; zalloc, zfree, opaque = 0;
  updZ stream fun z => { z with next_in := source, avail_in := 0, zalloc := .null, zfree := .null, «opaque» := .null }
  -- err = inflateInit(&stream); if (err != Z_OK) return err;
  let ver ← Zlib.GzFs.strLit ZLIB_VERSION
  let err ← inflateInit_ stream ver 112
  if err != Z_OK then
    free
    return err
  -- stream.next_out = dest; stream.avail_out = 0;
  updZ stream fun z => { z with next_out := dest, avail_out := 0 }
  -- do { ... } while (err == Z_OK);
  let l ← cdoWhile
    (fun (l : UncLoop) => do
      let mut l := l
      -- if (stream.avail_out == 0) { stream.avail_out = left > (z_size_t)max ? max : (uInt)left; left -= stream.avail_out; }
      if (← ldZ stream).avail_out == 0 then
        let a : UInt32 := if l.left > max.toUInt64 then max else l.left.toUInt32
        updZ stream fun z => { z with avail_out := a }
        l := { l with left := l.left - a.toUInt64 }
      -- if (stream.avail_in == 0) { stream.avail_in = len > (z_size_t)max ? max : (uInt)len; len -= stream.avail_in; }
      if (← ldZ stream).avail_in == 0 then
        let a : UInt32 := if l.len > max.toUInt64 then max else l.len.toUInt32
        updZ stream fun z => { z with avail_in := a }
        l := { l with len := l.len - a.toUInt64 }
      -- err = inflate(&stream, Z_NO_FLUSH);
      let err ← inflate stream Z_NO_FLUSH
      return { l with err })
    (fun l => pure (l.err == Z_OK, l))
    { err, len, left }
  -- len += stream.avail_in; left += stream.avail_out; *sourceLen -= len; *destLen -= left;
  let z ← ldZ stream
  let len := l.len + z.avail_in.toUInt64
  let left := l.left + z.avail_out.toUInt64
  store64 sourceLen ((← load64 sourceLen) - len)
  store64 destLen ((← load64 destLen) - left)
  -- inflateEnd(&stream);
  let _ ← inflateEnd stream
  -- return err == Z_STREAM_END ? Z_OK : err == Z_NEED_DICT ? Z_DATA_ERROR : err == Z_BUF_ERROR && len == 0 ? Z_DATA_ERROR : err;
  let err := l.err
  let r : Int32 :=
    if err == Z_STREAM_END then Z_OK
    else if err == Z_NEED_DICT then Z_DATA_ERROR
    else if err == Z_BUF_ERROR && len == 0 then Z_DATA_ERROR
    else err
  free
  return r

/-- `int ZEXPORT uncompress2(Bytef *dest, uLongf *destLen, const Bytef *source, uLong *sourceLen)` -/
def uncompress2 (dest : BPtr) (destLen : BPtr) (source : BPtr) (sourceLen : BPtr) : M Int32 := do
  -- int ret; z_size_t got = *destLen, used = *sourceLen;
  let got ← allocLocal 8
  let used ← allocLocal 8
  store64 got (← load64 destLen)
  store64 used (← load64 sourceLen)
  -- ret = uncompress2_z(dest, &got, source, &used);
  let ret ← uncompress2_z dest got source used
  -- *sourceLen = (uLong)used; *destLen = (uLong)got;
  store64 sourceLen (← load64 used)
  store64 destLen (← load64 got)
  freeB got
  freeB used
  return ret

/-- `int ZEXPORT uncompress_z(Bytef *dest, z_size_t *destLen, const Bytef *source, z_size_t sourceLen)` -/
def uncompress_z (dest : BPtr) (destLen : BPtr) (source : BPtr) (sourceLen : UInt64) : M Int32 := do
  -- z_size_t used = sourceLen;
  let used ← allocLocal 8
  store64 used sourceLen
  let r ← uncompress2_z dest destLen source used
  freeB used
  return r

/-- `int ZEXPORT uncompress(Bytef *dest, uLongf *destLen, const Bytef *source, uLong sourceLen)` -/
def uncompress (dest : BPtr) (destLen : BPtr) (source : BPtr) (sourceLen : UInt64) : M Int32 := do
  -- uLong used = sourceLen;
  let used ← allocLocal 8
  store64 used sourceLen
  let r ← uncompress2 dest destLen source used
  freeB used
  return r

end Zlib.Uncompr
