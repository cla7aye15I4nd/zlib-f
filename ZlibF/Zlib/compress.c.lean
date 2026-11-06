import ZlibF.Zlib.«deflate.c»

/-!
# compress.c — faithful translation

Source: `compress.c` of the verified source. `z_size_t *destLen` and `uLongf *destLen` are modelled as an input
value (`none` is a NULL pointer) and a result (the value stored through the pointer); the runtime has no pointer to a
scalar cell. `compress2` reads `*destLen` before any NULL test (R-2 of the notes), so a NULL `destLen` there is
`Fault.ub`. `deflateInit(&stream, level)` is `deflateInit_(&stream, level, ZLIB_VERSION, (int)sizeof(z_stream))`.
`z_stream stream` is an automatic record in the `streams` table. Creating it cannot fail or
consume a default-allocator call; it is freed before the returns.
-/

namespace Zlib.Compress
open C Zlib.Deflate

/-- Pointer difference `p - q` with the model's allowance for `NULL - NULL` (D-4). -/
def ptrDiff (p q : BPtr) : M Int64 :=
  if p == .null && q == .null then pure 0 else Ptr.diff p q

/-- Automatic storage for the local `z_stream`. As in `uncompr.c`, the runtime creates a fresh
record without consulting or advancing the allocation-failure oracle. Only the subsequent
`deflateInit` allocations are default-allocator calls in the C. -/
def allocLocalZ : M ZStreamPtr := fun h =>
  match allocZStream { h with allocOk := fun _ => true } with
  | .ok (p, h') => .ok (p, { h' with allocOk := h.allocOk, nalloc := h.nalloc })
  | .error e => .error e

/-- `int ZEXPORT compress2_z(Bytef *dest, z_size_t *destLen, const Bytef *source, z_size_t sourceLen, int level)`;
the result is the return value and the value stored in `*destLen` (unchanged `none` when NULL). -/
def compress2_z (dest : BPtr) (destLen : Option UInt64) (source : BPtr) (sourceLen : UInt64) (level : Int32) :
    M (Int32 × Option UInt64) := do
  let max : UInt32 := 0xffffffff                       -- const uInt max = (uInt)-1;
  -- if ((sourceLen > 0 && source == Z_NULL) || destLen == Z_NULL || (*destLen > 0 && dest == Z_NULL)) return Z_STREAM_ERROR;
  let some dl := destLen | return (Z_STREAM_ERROR, none)
  if (sourceLen > 0 && source == .null) || (dl > 0 && dest == .null) then return (Z_STREAM_ERROR, destLen)
  -- left = *destLen; *destLen = 0;
  let mut left : UInt64 := dl
  -- z_stream stream;  stream.zalloc = 0; stream.zfree = 0; stream.opaque = 0;
  let strm ← allocLocalZ
  zwr strm (fun z => { z with zalloc := FnPtr.null, zfree := FnPtr.null, «opaque» := .null })
  -- err = deflateInit(&stream, level); if (err != Z_OK) return err;
  let ver ← Zlib.Zutil.zlibVersion
  let mut err ← deflateInit_ strm level ver sizeof_z_stream
  if err != Z_OK then
    freeZStream strm
    return (err, some 0)
  -- stream.next_out = dest; stream.avail_out = 0; stream.next_in = source; stream.avail_in = 0;
  zwr strm (fun z => { z with next_out := dest, avail_out := 0, next_in := source, avail_in := 0 })
  let mut sourceLen := sourceLen
  -- do { ... } while (err == Z_OK);
  let (e, l, sl) ← cdoWhile
    (fun ((_, left, sourceLen) : Int32 × UInt64 × UInt64) => do
      let mut left := left
      let mut sourceLen := sourceLen
      -- if (stream.avail_out == 0) { stream.avail_out = left > (z_size_t)max ? max : (uInt)left; left -= stream.avail_out; }
      if (← zrd strm (·.avail_out)) == 0 then
        let ao : UInt32 := if left > max.toUInt64 then max else left.toUInt32
        zwr strm (fun z => { z with avail_out := ao })
        left := left - ao.toUInt64
      -- if (stream.avail_in == 0) { stream.avail_in = sourceLen > (z_size_t)max ? max : (uInt)sourceLen; sourceLen -= stream.avail_in; }
      if (← zrd strm (·.avail_in)) == 0 then
        let ai : UInt32 := if sourceLen > max.toUInt64 then max else sourceLen.toUInt32
        zwr strm (fun z => { z with avail_in := ai })
        sourceLen := sourceLen - ai.toUInt64
      -- err = deflate(&stream, sourceLen ? Z_NO_FLUSH : Z_FINISH);
      let err ← deflate strm (if sourceLen != 0 then Z_NO_FLUSH else Z_FINISH)
      pure (err, left, sourceLen))
    (fun (st : Int32 × UInt64 × UInt64) => pure (st.1 == Z_OK, st))
    (err, left, sourceLen)
  err := e
  left := l
  sourceLen := sl
  -- *destLen = (z_size_t)(stream.next_out - dest);
  let no ← zrd strm (·.next_out)
  let n ← ptrDiff no dest
  -- deflateEnd(&stream);
  let _ ← deflateEnd strm
  freeZStream strm
  -- return err == Z_STREAM_END ? Z_OK : err;
  return (if err == Z_STREAM_END then Z_OK else err, some n.toUInt64)

/-- `int ZEXPORT compress2(Bytef *dest, uLongf *destLen, const Bytef *source, uLong sourceLen, int level)`;
`destLen` is the value of `*destLen`, `none` for NULL (undefined: `*destLen` is read first). -/
def compress2 (dest : BPtr) (destLen : Option UInt64) (source : BPtr) (sourceLen : UInt64) (level : Int32) :
    M (Int32 × UInt64) := do
  -- z_size_t got = *destLen;
  let some got := destLen | ub "null dereference of destLen"
  -- ret = compress2_z(dest, &got, source, sourceLen, level);
  let (ret, g) ← compress2_z dest (some got) source sourceLen level
  -- *destLen = (uLong)got;
  return (ret, g.getD got)

/-- `int ZEXPORT compress_z(Bytef *dest, z_size_t *destLen, const Bytef *source, z_size_t sourceLen)` -/
def compress_z (dest : BPtr) (destLen : Option UInt64) (source : BPtr) (sourceLen : UInt64) :
    M (Int32 × Option UInt64) :=
  compress2_z dest destLen source sourceLen Z_DEFAULT_COMPRESSION

/-- `int ZEXPORT compress(Bytef *dest, uLongf *destLen, const Bytef *source, uLong sourceLen)` -/
def compress (dest : BPtr) (destLen : Option UInt64) (source : BPtr) (sourceLen : UInt64) :
    M (Int32 × UInt64) :=
  compress2 dest destLen source sourceLen Z_DEFAULT_COMPRESSION

/-- `z_size_t ZEXPORT compressBound_z(z_size_t sourceLen)` -/
def compressBound_z (sourceLen : UInt64) : UInt64 :=
  let bound := sourceLen + (sourceLen >>> 12) + (sourceLen >>> 14) + (sourceLen >>> 25) + 13
  if bound < sourceLen then 0xffffffffffffffff else bound

/-- `uLong ZEXPORT compressBound(uLong sourceLen)` -/
def compressBound (sourceLen : UInt64) : UInt64 :=
  -- (uLong)bound != bound is always false: both are 64 bits
  compressBound_z sourceLen

end Zlib.Compress
