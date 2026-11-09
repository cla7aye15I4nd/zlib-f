import ZlibF.Proof.«deflate.c.engine.common-header»
import ZlibF.Proof.«deflate.c.engine.common-header-encoding»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- The real private header writes factor before pending publication.
No caller output representation is restricted by this source equality. -/
theorem generic_zlib_header_prepare_source {h : Heap} {r : ZStreamRef} {ds pb : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8}
    (hz : r.get h = some z) (hd : h.dstates ds = some d)
    (status : d.status = INIT_STATE) (wrap : d.wrap = 1) (strategy : d.strategy = 0)
    (window : d.w_bits = 15) (start : d.strstart = 0) (pending : d.pending = 0)
    (pendingPtr : d.pending_buf = .ref (.blk pb) 0)
    (get : h.bytes pb = some buf) (room : 2 ≤ buf.size) (rw : h.ro pb = false)
    (next : M Int32) :
    publicZlibHeader (some r) (some (.tab ds)) next h =
      (do
        flush_pending (some r)
        if (← rd (some (.tab ds)) (·.pending)) != 0 then
          wr (some (.tab ds)) (fun d => { d with last_flush := -1 })
          return Z_OK
        else next) (levelHeaderReady h r ds pb z d buf) := by
  let h1 := setD { h with bytes := upd h.bytes pb (some (levelHeaderBytes d.level buf)) } ds { d with pending := 2 }
  let ready := levelHeaderReady h r ds pb z d buf
  have put : putShortMSB (some (.tab ds)) (levelHeaderWord d.level) h = .ok ((), h1) := by
    simpa only [pending, show ((0 : UInt64).toNat) = 0 from rfl, Nat.zero_add, UInt64.zero_add,
      levelHeaderBytes, h1, setD] using
      putShortMSB_ok (levelHeaderWord d.level) hd pendingPtr get rw (by simp only [pending]; change 1 < buf.size; omega)
        (by rw [pending]; decide)
  have z1 : r.get h1 = some z := by
    simpa only [h1, ZStreamRef.get_setD, stream_get_bytes] using hz
  have d1 : h1.dstates ds = some { d with pending := 2 } := by simp [h1]
  have writeBusy : wr (some (.tab ds)) (fun d => { d with status := BUSY_STATE })
      (r.put h1 { z with adler := 1 }) = .ok ((), ready) := by
    simp only [wrD_eq, ZStreamRef.put_dstates, d1]
    simp only [ready, levelHeaderReady, h1, ZStreamRef.put_setD, setD_setD, levelHeaderState]
  unfold publicZlibHeader
  simp only [bind_app, pure_app, rdD_eq, hd, status, wrap]
  simp only [show (INIT_STATE == INIT_STATE) = true from rfl, show ((1 : Int32) == 0) = false from rfl,
    Bool.and_false, Bool.false_eq_true, ite_false, ite_true, bind_app, pure_app,
    rdD_eq, hd, status, ldDeflateState_tab hd, strategy, window, start]
  simp only [show ((0 : Int32) ≥ Z_HUFFMAN_ONLY) = False from by decide,
    decide_false, Bool.false_or, show ((0 : UInt32) != 0) = false from rfl,
    Bool.false_eq_true, ite_false, decide_eq_true_eq]
  unfold levelHeaderWord levelHeaderFlags at put
  rw [bind_app, put]
  simp only [bind_app, pure_app, rdD_eq, d1, start, show ((0 : UInt32) != 0) = false from rfl, Bool.false_eq_true, ite_false,
    Zlib.Adler32.Proofs.adler32_null_init, pure_app, zwr_eq, z1, writeBusy]
  rfl

end Zlib.Deflate.Engine.Proofs
#print axioms Zlib.Deflate.Engine.Proofs.generic_zlib_header_prepare_source
