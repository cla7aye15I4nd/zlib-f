import ZlibF.Proof.«deflate.c.gzip-header-source»

namespace Zlib.Deflate.Engine.Proofs.DefaultGzipProofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open Zlib.Deflate.Engine.Proofs
set_option autoImplicit false
set_option maxHeartbeats 1500000

def gzipHeaderBytes (buf : Array UInt8) : Array UInt8 :=
  ((((((((((buf.set! 0 31).set! 1 139).set! 2 8).set! 3 0).set! 4 0).set! 5 0).set! 6 0).set! 7 0).set! 8 0).set! 9 OS_CODE.toUInt32.toUInt8)

def gzipHeaderState (d : DeflateState) : DeflateState :=
  { d with pending := 10, status := BUSY_STATE }

def gzipHeaderReady (h : Heap) (r : ZStreamRef) (ds pb : Nat)
    (z : ZStream) (d : DeflateState) (buf : Array UInt8) : Heap :=
  let h0 := r.put h {z with adler := 0}
  setD {h0 with bytes := upd h0.bytes pb (some (gzipHeaderBytes buf))} ds (gzipHeaderState d)

/-- Actual default gzip header before flush_pending. The source factor keeps
GZIP_STATE/no-custom-header guards at their original public call site.
Ten actual put_byte calls write the exact header, set CRC0 and enter BUSY.
The ordinary pending allocation has room10; no caller output size is imposed. -/
theorem gzip_default_header_before_flush {h : Heap} {r : ZStreamRef} {ds pb : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8}
    (hz : r.get h = some z) (hd : h.dstates ds = some d)
    (status : d.status = GZIP_STATE) (wrap : d.wrap = 2) (header : d.gzhead = none)
    (level : d.level = 6) (strategy : d.strategy = 0) (pending : d.pending = 0)
    (pointer : d.pending_buf = .ref (.blk pb) 0) (get : h.bytes pb = some buf)
    (writable : h.ro pb = false) (room : 10 ≤ buf.size) :
    gzipDefaultHeaderWrite (some r) (some (.tab ds)) h =
      .ok ((), gzipHeaderReady h r ds pb z d buf) := by
  let h0 := r.put h {z with adler := 0}
  have hd0 : h0.dstates ds = some d := by simpa [h0] using hd
  have hb0 : h0.bytes pb = some buf := by simpa [h0] using get
  have ro0 : h0.ro pb = false := by simpa [h0] using writable
  let a1 := buf.set! 0 31
  let h1 := setD {h0 with bytes := upd h0.bytes pb (some a1)} ds {d with pending := 1}
  have hd1 : h1.dstates ds = some {d with pending := 1} := by simp [h1]
  have put0 : put_byte (some (.tab ds)) 31 h0 = .ok ((),h1) := by
    have run := put_byte_ok 31 hd0 pointer hb0 ro0 (by simpa [pending] using (show 0 < buf.size by omega))
    simpa [h1, a1, pending, setD] using run
  let a2 := a1.set! 1 139
  let h2 := setD {h0 with bytes := upd h0.bytes pb (some a2)} ds {d with pending := 2}
  have hd2 : h2.dstates ds = some {d with pending := 2} := by simp [h2]
  have put1 : put_byte (some (.tab ds)) 139 h1 = .ok ((),h2) := by
    have run := put_byte_ok 139 hd1 pointer
      (show h1.bytes pb = some a1 by simp [h1])
      (show h1.ro pb = false by simpa [h1] using ro0)
      (by simpa [a1] using (show 1 < buf.size by omega))
    simpa [h1, h2, a2, setD, upd_upd] using run
  let a3 := a2.set! 2 8
  let h3 := setD {h0 with bytes := upd h0.bytes pb (some a3)} ds {d with pending := 3}
  have hd3 : h3.dstates ds = some {d with pending := 3} := by simp [h3]
  have put2 : put_byte (some (.tab ds)) 8 h2 = .ok ((),h3) := by
    have run := put_byte_ok 8 hd2 pointer
      (show h2.bytes pb = some a2 by simp [h2])
      (show h2.ro pb = false by simpa [h2] using ro0)
      (by simpa [a1, a2] using (show 2 < buf.size by omega))
    simpa [h2, h3, a3, setD, upd_upd] using run
  let a4 := a3.set! 3 0
  let h4 := setD {h0 with bytes := upd h0.bytes pb (some a4)} ds {d with pending := 4}
  have hd4 : h4.dstates ds = some {d with pending := 4} := by simp [h4]
  have put3 : put_byte (some (.tab ds)) 0 h3 = .ok ((),h4) := by
    have run := put_byte_ok 0 hd3 pointer
      (show h3.bytes pb = some a3 by simp [h3])
      (show h3.ro pb = false by simpa [h3] using ro0)
      (by simpa [a1, a2, a3] using (show 3 < buf.size by omega))
    simpa [h3, h4, a4, setD, upd_upd] using run
  let a5 := a4.set! 4 0
  let h5 := setD {h0 with bytes := upd h0.bytes pb (some a5)} ds {d with pending := 5}
  have hd5 : h5.dstates ds = some {d with pending := 5} := by simp [h5]
  have put4 : put_byte (some (.tab ds)) 0 h4 = .ok ((),h5) := by
    have run := put_byte_ok 0 hd4 pointer
      (show h4.bytes pb = some a4 by simp [h4])
      (show h4.ro pb = false by simpa [h4] using ro0)
      (by simpa [a1, a2, a3, a4] using (show 4 < buf.size by omega))
    simpa [h4, h5, a5, setD, upd_upd] using run
  let a6 := a5.set! 5 0
  let h6 := setD {h0 with bytes := upd h0.bytes pb (some a6)} ds {d with pending := 6}
  have hd6 : h6.dstates ds = some {d with pending := 6} := by simp [h6]
  have put5 : put_byte (some (.tab ds)) 0 h5 = .ok ((),h6) := by
    have run := put_byte_ok 0 hd5 pointer
      (show h5.bytes pb = some a5 by simp [h5])
      (show h5.ro pb = false by simpa [h5] using ro0)
      (by simpa [a1, a2, a3, a4, a5] using (show 5 < buf.size by omega))
    simpa [h5, h6, a6, setD, upd_upd] using run
  let a7 := a6.set! 6 0
  let h7 := setD {h0 with bytes := upd h0.bytes pb (some a7)} ds {d with pending := 7}
  have hd7 : h7.dstates ds = some {d with pending := 7} := by simp [h7]
  have put6 : put_byte (some (.tab ds)) 0 h6 = .ok ((),h7) := by
    have run := put_byte_ok 0 hd6 pointer
      (show h6.bytes pb = some a6 by simp [h6])
      (show h6.ro pb = false by simpa [h6] using ro0)
      (by simpa [a1, a2, a3, a4, a5, a6] using (show 6 < buf.size by omega))
    simpa [h6, h7, a7, setD, upd_upd] using run
  let a8 := a7.set! 7 0
  let h8 := setD {h0 with bytes := upd h0.bytes pb (some a8)} ds {d with pending := 8}
  have hd8 : h8.dstates ds = some {d with pending := 8} := by simp [h8]
  have put7 : put_byte (some (.tab ds)) 0 h7 = .ok ((),h8) := by
    have run := put_byte_ok 0 hd7 pointer
      (show h7.bytes pb = some a7 by simp [h7])
      (show h7.ro pb = false by simpa [h7] using ro0)
      (by simpa [a1, a2, a3, a4, a5, a6, a7] using (show 7 < buf.size by omega))
    simpa [h7, h8, a8, setD, upd_upd] using run
  let a9 := a8.set! 8 0
  let h9 := setD {h0 with bytes := upd h0.bytes pb (some a9)} ds {d with pending := 9}
  have hd9 : h9.dstates ds = some {d with pending := 9} := by simp [h9]
  have put8 : put_byte (some (.tab ds)) 0 h8 = .ok ((),h9) := by
    have run := put_byte_ok 0 hd8 pointer
      (show h8.bytes pb = some a8 by simp [h8])
      (show h8.ro pb = false by simpa [h8] using ro0)
      (by simpa [a1, a2, a3, a4, a5, a6, a7, a8] using (show 8 < buf.size by omega))
    simpa [h8, h9, a9, setD, upd_upd] using run
  let a10 := a9.set! 9 OS_CODE.toUInt32.toUInt8
  let h10 := setD {h0 with bytes := upd h0.bytes pb (some a10)} ds {d with pending := 10}
  have hd10 : h10.dstates ds = some {d with pending := 10} := by simp [h10]
  have put9 : put_byte (some (.tab ds)) OS_CODE.toUInt32.toUInt8 h9 = .ok ((),h10) := by
    have run := put_byte_ok OS_CODE.toUInt32.toUInt8 hd9 pointer
      (show h9.bytes pb = some a9 by simp [h9])
      (show h9.ro pb = false by simpa [h9] using ro0)
      (by simpa [a1, a2, a3, a4, a5, a6, a7, a8, a9] using (show 9 < buf.size by omega))
    simpa [h9, h10, a10, setD, upd_upd] using run
  have front : gzipHeaderFront (some r) (some (.tab ds)) h = .ok ((),h3) := by
    unfold gzipHeaderFront
    rw [Zlib.Deflate.Proofs.crc32_null]
    simp only [M_pure_bind]
    rw [bind_app, zwr_eq, hz]
    change (do
      put_byte (some (.tab ds)) 31
      put_byte (some (.tab ds)) 139
      put_byte (some (.tab ds)) 8) h0 = _
    rw [bind_app, put0]
    dsimp only
    rw [bind_app, put1]
    dsimp only
    exact put2
  unfold gzipDefaultHeaderWrite
  rw [bind_app, front]
  simp only [bind_app, ldDeflateState_tab hd3, level, strategy]
  simp only [show ((6 : Int32) == 9) = false from rfl,
    show ((0 : Int32) ≥ Z_HUFFMAN_ONLY) = False from by decide,
    show ((6 : Int32) < 2) = False from by decide,
    decide_false, Bool.false_or, Bool.false_eq_true, ite_false]
  unfold gzipDefaultHeaderBack
  rw [bind_app, put3]
  dsimp only
  rw [bind_app, put4]
  dsimp only
  rw [bind_app, put5]
  dsimp only
  rw [bind_app, put6]
  dsimp only
  rw [bind_app, put7]
  dsimp only
  rw [bind_app, put8]
  dsimp only
  rw [bind_app, put9]
  dsimp only
  simp only [wrD_eq, hd10]
  simp only [h10, gzipHeaderReady, gzipHeaderState, gzipHeaderBytes, h0, a10, a9, a8, a7, a6, a5, a4, a3, a2, a1,
    setD_setD]

end Zlib.Deflate.Engine.Proofs.DefaultGzipProofs
