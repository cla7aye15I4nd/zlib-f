import ZlibF.Proof.«deflate.c.gzip-header-run»

namespace Zlib.Deflate.Engine.Proofs.DefaultGzipProofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Engine.Proofs
set_option autoImplicit false

theorem gzip_header_bytes_size (buf : Array UInt8) : (gzipHeaderBytes buf).size = buf.size := by
  simp [gzipHeaderBytes]

theorem gzip_header_bytes_prefix (buf : Array UInt8) (room : 10 ≤ buf.size) :
    (gzipHeaderBytes buf).toList.take 10 = [31,139,8,0,0,0,0,0,0,OS_CODE.toUInt32.toUInt8] := by
  apply List.ext_getElem
  · simp [gzip_header_bytes_size, Nat.min_eq_left room]
  · intro i hi hj
    have less : i < 10 := by simpa using hj
    have choices : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 := by omega
    rcases choices with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp_all [gzipHeaderBytes]

/-- Concrete header bytes and exact metadata/stream fields in the returned heap. -/
theorem gzip_header_ready_fields {h : Heap} {r : ZStreamRef} {ds pb : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8}
    (get : r.get h = some z) (room : 10 ≤ buf.size) :
    let after := gzipHeaderReady h r ds pb z d buf
    r.get after = some {z with adler := 0} ∧
    after.dstates ds = some (gzipHeaderState d) ∧
    after.bytes pb = some (gzipHeaderBytes buf) ∧
    Bytes after (.ref (.blk pb) 0) 10 [31,139,8,0,0,0,0,0,0,OS_CODE.toUInt32.toUInt8] ∧
    after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk ∧
    after.allocOk = h.allocOk ∧ after.garbage = h.garbage ∧ after.static = h.static ∧
    after.libcErrorBorrow = h.libcErrorBorrow := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [gzipHeaderReady, ZStreamRef.get_setD, stream_get_bytes, ZStreamRef.get_put_same get]
  · simp [gzipHeaderReady]
  · simp [gzipHeaderReady]
  · right
    exact ⟨.blk pb,0,gzipHeaderBytes buf,rfl,by simp [Space.get,gzipHeaderReady],
      by simpa [gzip_header_bytes_size] using room,
      by simpa using (gzip_header_bytes_prefix buf room).symm⟩
  · simp [gzipHeaderReady]
  · simp [gzipHeaderReady]
  · simp [gzipHeaderReady]
  · simp [gzipHeaderReady]
  · simp [gzipHeaderReady]
  · simpa only [gzipHeaderReady, setD] using Zlib.Deflate.BorrowProofs.stream_put_borrow h r {z with adler := 0}

/-- Header writes touch existing storage only; no object is born or freed. -/
theorem gzip_header_ready_shape {h : Heap} {r : ZStreamRef} {ds pb : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8}
    (get : r.get h = some z) (state : h.dstates ds = some d) (bytes : h.bytes pb = some buf) :
    Shape h (gzipHeaderReady h r ds pb z d buf) := by
  let h0 := r.put h {z with adler := 0}
  have hp : Shape h h0 := shape_put get _
  have hb : h0.bytes pb = some buf := by simpa [h0] using bytes
  have hs : ({h0 with bytes := upd h0.bytes pb (some (gzipHeaderBytes buf))} : Heap).dstates ds = some d := by
    simpa [h0] using state
  exact hp.trans ((shape_setB hb (gzipHeaderBytes buf)).trans (shape_setD hs (gzipHeaderState d)))

/-- The exact heap update frames every object outside stream/state/pending storage. -/
theorem gzip_header_ready_frame (h : Heap) (r : ZStreamRef) (ds pb : Nat)
    (z : ZStream) (d : DeflateState) (buf : Array UInt8) :
    Frame h (gzipHeaderReady h r ds pb z d buf) (fun b => StreamRoot r b ∨ b = ds ∨ b = pb) := by
  refine ⟨by simp [gzipHeaderReady],by simp [gzipHeaderReady],by simp [gzipHeaderReady],
    by simp [gzipHeaderReady],by simp [gzipHeaderReady],?_⟩
  intro b _live outside
  have nr : ¬ StreamRoot r b := fun hi => outside (Or.inl hi)
  have nd : b ≠ ds := fun hi => outside (Or.inr (Or.inl hi))
  have nb : b ≠ pb := fun hi => outside (Or.inr (Or.inr hi))
  have old := Zlib.Deflate.Proofs.DefaultInit.slot_put_except h r {z with adler := 0} b nr
  simpa [Zlib.Deflate.Proofs.DefaultInit.SlotSame,gzipHeaderReady,setD,upd_ne _ _ _ _ nd,upd_ne _ _ _ _ nb] using old

end Zlib.Deflate.Engine.Proofs.DefaultGzipProofs
