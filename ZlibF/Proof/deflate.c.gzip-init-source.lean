import ZlibF.Proof.«deflate.c.init.default»

namespace Zlib.Deflate.Proofs.DefaultGzipInit
open C Zlib.Deflate Zlib.Deflate.Spec ZlibF.Spec.Public
open Zlib.Deflate.Proofs.DefaultInit (levelValue)
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

/-- The exact allocation suffix of Init2 with windowBits31/memLevel8/strategy0.
Only the wrapper field differs from the default zlib allocation suffix. -/
def allocate (strm : ZStreamPtr) (level : Int32) : M Int32 := do
  zalloc_default strm
  let s ← allocDeflateState
  if s == none then return Z_MEM_ERROR
  stDeflateState s DeflateState.zeroed
  zwr strm (fun z => { z with state := StateRef.ofDeflateState s })
  wr s (fun d => { d with
    strm := strm, status := INIT_STATE, wrap := 2,
    w_bits := 15, w_size := 32768, w_mask := 32767,
    hash_bits := 15, hash_size := 32768, hash_mask := 32767, hash_shift := 5 })
  let window ← ZALLOC_bytes strm 32768 2
  wr s (fun d => { d with window })
  let prev ← ZALLOC_words strm 32768
  wr s (fun d => { d with prev })
  let head ← ZALLOC_words strm 32768
  wr s (fun d => { d with head })
  wr s (fun d => { d with high_water := 0, lit_bufsize := 16384 })
  let pending_buf ← ZALLOC_bytes strm 16384 4
  wr s (fun d => { d with pending_buf, pending_buf_size := 65536 })
  if window == .null || prev == .null || head == .null || pending_buf == .null then
    wr s (fun d => { d with status := FINISH_STATE })
    let m ← ERR_MSG Z_MEM_ERROR
    zwr strm (fun z => { z with msg := m })
    let _ ← deflateEnd strm
    return Z_MEM_ERROR
  let sym_buf ← padd pending_buf 16384
  wr s (fun d => { d with sym_buf, sym_end := 49149 })
  wr s (fun d => { d with level, strategy := 0, «method» := 8 })
  deflateReset strm

/-- Exact statement-ordered specialization of the actual Init2 gzip call.
All arbitrary-level refusals and all five allocation/cleanup branches remain. -/
theorem gzip_init_source_eq (strm : ZStreamPtr) (level : Int32) (version : BPtr) (size : Int32) :
    deflateInit2_ strm level 8 31 8 0 version size = (do
      if version == .null then return Z_VERSION_ERROR
      if (← load8 version) != 49 || size != sizeof_z_stream then return Z_VERSION_ERROR
      if strm == none then return Z_STREAM_ERROR
      zwr strm (fun z => { z with msg := .null })
      if (← zrd strm (·.zalloc)) == FnPtr.null then
        zwr strm (fun z => { z with zalloc := FnPtr.fn "zcalloc", «opaque» := .null })
      if (← zrd strm (·.zfree)) == FnPtr.null then
        zwr strm (fun z => { z with zfree := FnPtr.fn "zcfree" })
      if levelValue level < 0 || levelValue level > 9 then return Z_STREAM_ERROR
      allocate strm (levelValue level)) := by
  by_cases hd : level = Z_DEFAULT_COMPRESSION
  all_goals unfold deflateInit2_ allocate levelValue
  all_goals simp [hd, Z_DEFLATED, MAX_WBITS, DEF_MEM_LEVEL, Z_DEFAULT_STRATEGY, MAX_MEM_LEVEL,
    Z_FIXED, MIN_MATCH_u, iadd, isub, ishl, chk32, M_bind_assoc, M_pure_bind]
  all_goals rfl


end Zlib.Deflate.Proofs.DefaultGzipInit
