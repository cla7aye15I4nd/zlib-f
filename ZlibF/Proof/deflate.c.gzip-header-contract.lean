import ZlibF.Proof.«deflate.c.gzip-header-facts»

namespace Zlib.Deflate.Engine.Proofs.DefaultGzipProofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Engine.Proofs
set_option autoImplicit false

/-- Same-run no-custom-header producer before the first pending publication.
The exact ten bytes, physical frame, unchanged object/allocation ledger and
borrowed-string receipt accompany the real writer run. Caller input/output cursors and counters are unchanged. -/
theorem gzip_default_header_before_flush_contract {h : Heap} {r : ZStreamRef} {ds pb : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8}
    (hz : r.get h = some z) (hd : h.dstates ds = some d)
    (status : d.status = GZIP_STATE) (wrap : d.wrap = 2) (header : d.gzhead = none)
    (level : d.level = 6) (strategy : d.strategy = 0) (pending : d.pending = 0)
    (pointer : d.pending_buf = .ref (.blk pb) 0) (get : h.bytes pb = some buf)
    (writable : h.ro pb = false) (room : 10 ≤ buf.size) :
    ∃ after,
      gzipDefaultHeaderWrite (some r) (some (.tab ds)) h = .ok ((),after) ∧
      after = gzipHeaderReady h r ds pb z d buf ∧
      r.get after = some {z with adler := 0} ∧
      after.dstates ds = some (gzipHeaderState d) ∧
      Bytes after (.ref (.blk pb) 0) 10 [31,139,8,0,0,0,0,0,0,OS_CODE.toUInt32.toUInt8] ∧
      StreamAccounting z {z with adler := 0} 0 0 ∧ Shape h after ∧
      Frame h after (fun b => StreamRoot r b ∨ b = ds ∨ b = pb) ∧
      (∀ b, after.live b ↔ h.live b) ∧
      after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk ∧
      after.allocOk = h.allocOk ∧ after.garbage = h.garbage ∧ after.static = h.static ∧
      after.libcErrorBorrow = h.libcErrorBorrow := by
  obtain ⟨streamA,stateA,_bytesA,bytesA,countA,nextA,oracleA,garbageA,staticA,borrowA⟩ :=
    gzip_header_ready_fields (ds := ds) (pb := pb) (d := d) hz room
  have shape := gzip_header_ready_shape hz hd get
  refine ⟨_,gzip_default_header_before_flush hz hd status wrap header level strategy pending pointer get writable room,
    rfl,streamA,stateA,bytesA,?_,shape,gzip_header_ready_frame h r ds pb z d buf,shape.live,
    countA,nextA,oracleA,garbageA,staticA,borrowA⟩
  simp [StreamAccounting, advance_zero]

end Zlib.Deflate.Engine.Proofs.DefaultGzipProofs
