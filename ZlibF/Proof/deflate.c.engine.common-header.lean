import ZlibF.Proof.«deflate.c.engine.public-header»

/-! # Actual zlib-header execution with the compression level retained -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
set_option autoImplicit false

/-- The level flags are computed by the translated standard-strategy header. -/
def levelHeaderFlags (level : Int32) : UInt32 :=
  if level < 2 then 0 else if level < 6 then 1 else if level == 6 then 2 else 3

/-- Actual header arithmetic at windowBits fifteen, without a dictionary. -/
def levelHeaderWord (level : Int32) : UInt32 :=
  let raw := (((8 : UInt32) + (((15 : UInt32) - 8) <<< 4)) <<< 8) ||| (levelHeaderFlags level <<< 6)
  raw + ((31 : UInt32) - raw % 31)

def levelHeaderBytes (level : Int32) (buf : Array UInt8) : Array UInt8 :=
  (buf.set! 0 ((levelHeaderWord level >>> 8).toUInt8)).set! 1 ((levelHeaderWord level &&& 0xff).toUInt8)

def levelHeaderState (d : DeflateState) : DeflateState :=
  { d with pending := 2, status := BUSY_STATE }

def levelHeaderReady (h : Heap) (r : ZStreamRef) (ds pb : Nat)
    (z : ZStream) (d : DeflateState) (buf : Array UInt8) : Heap :=
  setD (r.put { h with bytes := upd h.bytes pb (some (levelHeaderBytes d.level buf)) } { z with adler := 1 }) ds
    (levelHeaderState d)

def levelHeaderFlushed (h : Heap) (r : ZStreamRef) (ds pb ob oo : Nat)
    (z : ZStream) (d : DeflateState) (buf output : Array UInt8) : Heap :=
  let n := pendingLen 2 z.avail_out
  let ready := levelHeaderReady h r ds pb z d buf
  let copied := { ready with bytes := upd ready.bytes ob (some (copyRange output (levelHeaderBytes d.level buf) oo 0 n.toNat)) }
  setD (r.put copied (pendingStream { z with adler := 1 } (.ref (.blk ob) (oo + n.toNat)) n)) ds
    (pendingState (levelHeaderState d) (.ref (.blk pb) n.toNat) n)

/-- `int ZEXPORT deflate(z_streamp strm, int flush)` (zlib header fragment).
For the standard wrapper and strategy, actual source arithmetic retains
the caller-selected compression level. Positive output copies its prefix.
Raw output and pending storage are distinct. One output byte gives the
source's early Z_OK return; a full header reaches the given continuation.
This internal path does not restrict the public caller-buffer domain. -/
theorem public_common_header_run {h : Heap} {r : ZStreamRef} {ds pb ob oo : Nat}
    {z : ZStream} {d : DeflateState} {buf output : Array UInt8}
    (hz : r.get h = some z) (state : z.state = some (.deflate ds))
    (hd : h.dstates ds = some d) (status : d.status = INIT_STATE) (wrap : d.wrap = 1)
    (bits : d.bi_valid = 0) (strategy : d.strategy = 0)
    (window : d.w_bits = 15) (start : d.strstart = 0) (pending : d.pending = 0)
    (pendingPtr : d.pending_buf = .ref (.blk pb) 0) (cursor : d.pending_out = d.pending_buf)
    (get : h.bytes pb = some buf) (room : 2 ≤ buf.size) (rw : h.ro pb = false)
    (outPtr : z.next_out = .ref (.blk ob) oo) (outGet : h.bytes ob = some output)
    (outRw : h.ro ob = false) (separate : ob ≠ pb)
    (outBound : oo + z.avail_out.toNat ≤ output.size) (positive : z.avail_out ≠ 0)
    (next : M Int32) :
    let n := pendingLen 2 z.avail_out
    let after := levelHeaderFlushed h r ds pb ob oo z d buf output
    publicZlibHeader (some r) (some (.tab ds)) next h =
      if 2 - n.toUInt64 != 0 then
        .ok (Z_OK, setD after ds { pendingState (levelHeaderState d) (.ref (.blk pb) n.toNat) n with last_flush := -1 })
      else next after := by
  let n := pendingLen 2 z.avail_out
  let h1 := setD { h with bytes := upd h.bytes pb (some (levelHeaderBytes d.level buf)) } ds { d with pending := 2 }
  let ready := levelHeaderReady h r ds pb z d buf
  let after := levelHeaderFlushed h r ds pb ob oo z d buf output
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
  have zr : r.get ready = some { z with adler := 1 } := by
    simp only [ready, levelHeaderReady, ZStreamRef.get_setD]
    apply ZStreamRef.get_put_same
    simpa only [stream_get_bytes] using hz
  have dr : ready.dstates ds = some (levelHeaderState d) := by simp [ready, levelHeaderReady]
  have len : n.toNat = min 2 z.avail_out.toNat := pendingLen_value 2 z.avail_out
  have nz : n ≠ 0 := by
    intro zero
    have pos : 0 < z.avail_out.toNat := by
      have ne : z.avail_out.toNat ≠ 0 := by
        intro empty
        exact positive (UInt32.toNat_inj.mp empty)
      omega
    have count := congrArg UInt32.toNat zero
    change n.toNat = 0 at count
    omega
  have flush : flush_pending (some r) ready = .ok ((), after) := by
    simpa only [levelHeaderState, levelHeaderFlushed, levelHeaderReady, ready, after, n, Nat.zero_add,
      ZStreamRef.put_bytes, setD_bytes] using
      flush_pending_low_raw (pending := levelHeaderBytes d.level buf) (output := output) (po := 0) zr (by simpa using state) dr (by simp [levelHeaderState, bits])
        outPtr (by simpa [levelHeaderState, cursor] using pendingPtr)
        (by simpa [ready, levelHeaderReady, upd_ne _ _ _ _ separate] using outGet)
        (by simp [ready, levelHeaderReady]) (by simpa [ready, levelHeaderReady] using outRw) separate
        outBound (by simpa [levelHeaderBytes, levelHeaderState] using room) nz
  have da : after.dstates ds = some (pendingState (levelHeaderState d) (.ref (.blk pb) n.toNat) n) := by
    simp [after, levelHeaderFlushed, n]
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
    Zlib.Adler32.Proofs.adler32_null_init, pure_app, zwr_eq, z1, writeBusy, flush]
  simp only [bind_app, rdD_eq, da, pendingState, levelHeaderState]
  split
  · simp only [wrD_eq, da, bind_app, setD_setD]
    rfl
  · rfl

end Zlib.Deflate.Engine.Proofs
