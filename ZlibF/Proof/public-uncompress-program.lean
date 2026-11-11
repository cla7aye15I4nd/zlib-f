import ZlibF.Proof.«public-uncompress-loop»

/-!
# uncompr.c: `uncompress2_z` with its loop named

`program` is the translation of `uncompress2_z` with the loop body and condition
replaced by `loopBody` and `loopCond`. It is the translation, by definition.
-/

namespace ZlibF.Spec.Public.Proofs.Uncompress
open C ZlibF.Spec ZlibF.Spec.Public Zlib.Gzguts Zlib.Inflate.Proofs Zlib.Uncompr
open Zlib.Inflate (inflateInit_ inflate inflateEnd)
set_option autoImplicit false

/-- `uncompress2_z` with the loop named. -/
def program (dest : BPtr) (destLen : BPtr) (source : BPtr) (sourceLen : BPtr) : M Int32 := do
  let stream ← allocLocalZ
  let reserved ← allocLocal 8
  let free : M Unit := do
    freeB reserved
    freeZStream stream
  let mut bad := false
  if sourceLen == .null then bad := true
  else if (← load64 sourceLen) > 0 && source == .null then bad := true
  else if destLen == .null then bad := true
  else if (← load64 destLen) > 0 && dest == .null then bad := true
  if bad then
    free
    return Z_STREAM_ERROR
  let len ← load64 sourceLen
  let left ← load64 destLen
  let dest := if left == 0 && dest == .null then reserved else dest
  updZ stream fun z => { z with next_in := source, avail_in := 0, zalloc := .null, zfree := .null, «opaque» := .null }
  let ver ← Zlib.GzFs.strLit ZLIB_VERSION
  let err ← inflateInit_ stream ver 112
  if err != Z_OK then
    free
    return err
  updZ stream fun z => { z with next_out := dest, avail_out := 0 }
  let l ← cdoWhile (loopBody stream) loopCond { err, len, left }
  let z ← ldZ stream
  let len := l.len + z.avail_in.toUInt64
  let left := l.left + z.avail_out.toUInt64
  store64 sourceLen ((← load64 sourceLen) - len)
  store64 destLen ((← load64 destLen) - left)
  let _ ← inflateEnd stream
  let err := l.err
  let r : Int32 :=
    if err == Z_STREAM_END then Z_OK
    else if err == Z_NEED_DICT then Z_DATA_ERROR
    else if err == Z_BUF_ERROR && len == 0 then Z_DATA_ERROR
    else err
  free
  return r

theorem program_eq (dest destLen source sourceLen : BPtr) :
    uncompress2_z dest destLen source sourceLen = program dest destLen source sourceLen := rfl

end ZlibF.Spec.Public.Proofs.Uncompress
