import ZlibF.Proof.«deflate.c.engine.read-zlib»
import ZlibF.Proof.«crc32.c.views»

/-! Actual read_buf transport on the gzip branch. No reachability,
global object uniqueness or called-function hypothesis is assumed. -/
namespace Zlib.Deflate.Engine.Proofs.DefaultGzipProofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Engine.Proofs
set_option autoImplicit false

/-- `local unsigned read_buf(z_streamp strm, Bytef *buf, unsigned size)`.
The actual wrapper-2 branch copies the selected bytes and updates CRC32.
The input may use any represented byte view and the stream may be embedded.
All seeds, non-overlapping readable input and writable destination slices are retained. -/
theorem read_buf_gzip {h : Heap} {r : ZStreamRef} {ds w io bo : Nat}
    {z : ZStream} {d : DeflateState} {ref : BRef} {ia wa : Array UInt8}
    (hz : r.get h = some z) (hs : z.state = some (.deflate ds)) (hd : h.dstates ds = some d)
    (wrap : d.wrap = 2) (globals : Zlib.Crc32.Proofs.StaticsOK h) (pointer : z.next_in = .ref ref io)
    (input : Space.get h ref = some ia) (window : h.bytes w = some wa) (writable : h.ro w = false)
    (size : UInt32) (nonzero : rbLen z.avail_in size ≠ 0)
    (inputBound : io + (rbLen z.avail_in size).toNat ≤ ia.size)
    (windowBound : bo + (rbLen z.avail_in size).toNat ≤ wa.size)
    (separate : BRef.blk w ≠ ref ∨ bo + (rbLen z.avail_in size).toNat ≤ io ∨
      io + (rbLen z.avail_in size).toNat ≤ bo) :
    let n := rbLen z.avail_in size
    let a := (ZlibF.Spec.crc32Update z.adler.toUInt32 ((ia.toList.drop io).take n.toNat)).toUInt64
    read_buf (some r) (.ref (.blk w) bo) size h = .ok (n,
      r.put { h with bytes := upd h.bytes w (some (copyRange wa ia bo io n.toNat)) }
        (readStream z n ref io a)) := by
  let n := rbLen z.avail_in size
  let z1 := rbDec n z
  let h1 := r.put h z1
  let wa' := copyRange wa ia bo io n.toNat
  let h2 := { h1 with bytes := upd h1.bytes w (some wa') }
  let a := (ZlibF.Spec.crc32Update z.adler.toUInt32 ((ia.toList.drop io).take n.toNat)).toUInt64
  let z2 := { z1 with adler := a }
  let h3 := r.put h2 z2
  have hz1 : r.get h1 = some z1 := ZStreamRef.get_put_same hz _
  have hz2 : r.get h2 = some z1 := by simpa [h2, stream_get_bytes] using hz1
  have hz3 : r.get h3 = some z2 := ZStreamRef.get_put_same hz2 _
  have getW : h1.bytes w = some wa := by simpa [h1] using window
  have getI : Space.get h1 ref = some ia := by simpa [h1, byte_get_stream_put] using input
  have ro : h1.ro w = false := by simpa [h1] using writable
  have copy : memcpyB (.ref (.blk w) bo) (.ref ref io) n.toNat h1 = .ok ((), h2) := by
    exact Ptr.memcpy_ok getW getI ro windowBound inputBound separate
  have getW2 : h2.bytes w = some wa' := by simp [h2]
  have hd2 : h2.dstates ds = some d := by simpa [h2, h1] using hd
  have slices : (wa'.toList.drop bo).take n.toNat = (ia.toList.drop io).take n.toNat := by
    rw [← seg_eq_take_drop wa' bo n.toNat (by simpa [wa', size_copyRange] using windowBound),
      ← seg_eq_take_drop ia io n.toNat inputBound]
    exact seg_copyRange wa ia bo io n.toNat windowBound
  have checksum : Zlib.Crc32.crc32 z.adler (.ref (.blk w) bo) n h2 = .ok (a, h2) := by
    have static2 : Zlib.Crc32.Proofs.StaticsOK h2 := by
      simpa only [Zlib.Crc32.Proofs.StaticsOK, h2, h1, ZStreamRef.put_static] using globals
    have run := Zlib.Crc32.Proofs.crc32_all_byte_views h2 static2 z.adler (.blk w) bo wa' getW2 n
      (by simpa [wa', size_copyRange] using windowBound)
    simpa only [C.run, slices] using run
  obtain ⟨input', getI2, inputSize⟩ := byte_view_write_size getI getW (size_copyRange _ _ _ _ _)
  have getI3 : Space.get h3 ref = some input' := by
    simpa only [h3, byte_get_stream_put] using getI2
  have advance : padd (.ref ref io : BPtr) n.toNat h3 = .ok (.ref ref (io + n.toNat), h3) := by
    simpa only [OkOn, padd] using Ptr.add_nat_ok getI3
      (by rw [inputSize]; exact inputBound : io + n.toNat ≤ input'.size)
  have endHeap : r.put h3 (rbAdvF (.ref ref (io + n.toNat)) n z2) =
      r.put { h with bytes := upd h.bytes w (some wa') } (readStream z n ref io a) := by
    have h2eq : h2 = r.put { h with bytes := upd h.bytes w (some wa') } z1 := by
      dsimp only [h2, h1]
      rw [ZStreamRef.put_bytes]
      exact (stream_put_bytes h r z1 (upd h.bytes w (some wa'))).symm
    dsimp only [h3]
    rw [ZStreamRef.put_put, h2eq, ZStreamRef.put_put]
    rfl
  have dec : zwr (some r) (rbDec n) h = .ok ((), h1) := by simp [zwr_eq, hz, h1, z1]
  have read : zrd (some r) (·.next_in) h1 = .ok (.ref ref io, h1) := by
    simp [zrd_eq, hz1, z1, rbDec, pointer]
  have state : zrd (some r) (·.state) h2 = .ok (some (.deflate ds), h2) := by
    simp [zrd_eq, hz2, z1, rbDec, hs]
  have wrapper : rd (some (.tab ds)) (·.wrap) h2 = .ok (2, h2) := by simp [rdD_eq, hd2, wrap]
  have seed : zrd (some r) (·.adler) h2 = .ok (z.adler, h2) := by simp [zrd_eq, hz2, z1, rbDec]
  have setAdler : zwr (some r) (rbSetAd a) h2 = .ok ((), h3) := by
    simp [zwr_eq, hz2, h3, z2, rbSetAd]
  have readNext : zrd (some r) (·.next_in) h3 = .ok (.ref ref io, h3) := by
    simp [zrd_eq, hz3, z2, z1, rbDec, pointer]
  have writeNext : zwr (some r) (rbAdvF (.ref ref (io + n.toNat)) n) h3 =
      .ok ((), r.put { h with bytes := upd h.bytes w (some wa') } (readStream z n ref io a)) := by
    simp only [zwr_eq, hz3, endHeap]
  rw [read_buf_ref_eq hz]
  change rbCore (some r) (.ref (.blk w) bo) n h = _
  have nz : (n == 0) = false := by simp [n, nonzero]
  simp only [rbCore, nz, Bool.false_eq_true, if_false, bind_app, dec, read, copy, state,
    show ((2 : Int32) == 1) = false from rfl, if_false,
    show ((2 : Int32) == 2) = true from rfl, if_true,
    castDeflateState_ok, wrapper, seed, checksum, setAdler, readNext, advance, writeNext, pure_app]
  rfl

end Zlib.Deflate.Engine.Proofs.DefaultGzipProofs
