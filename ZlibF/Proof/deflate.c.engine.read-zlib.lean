import ZlibF.Proof.«deflate.c.borrow-stable-base»
import ZlibF.Proof.«deflate.c.engine.readbuf»
import ZlibF.Proof.«deflate.c.engine.initial»
import ZlibF.Proof.«public-adler-update»

/-! # read_buf on the default zlib path

Both stream representations and all readable byte references are included.
The checksum result uses the already proved actual Adler entry, including
its single-byte behavior for arbitrary seeds.
-/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

theorem byte_get_stream_put (h : Heap) (r : ZStreamRef) (z : ZStream) (ref : BRef) :
    Space.get (r.put h z) ref = (Space.get h ref : Option (Array UInt8)) := by
  cases ref with
  | str i =>
      exact C.LibcBorrow.str_view_stable (Or.inr (Zlib.Deflate.BorrowProofs.stream_put_borrow h r z))
  | blk _ | dstate_depth _ | st_dist_code | st_length_code =>
      cases r <;> simp only [Space.get, ZStreamRef.put] <;>
        first | rfl | split <;> rfl

theorem stream_get_bytes (h : Heap) (r : ZStreamRef) (bytes : Tbl (Option (Array UInt8))) :
    r.get { h with bytes } = r.get h := by cases r <;> rfl

theorem stream_put_bytes (h : Heap) (r : ZStreamRef) (z : ZStream)
    (bytes : Tbl (Option (Array UInt8))) :
    r.put { h with bytes } z = { r.put h z with bytes } := by
  cases r <;> simp only [ZStreamRef.put] <;> split <;> rfl

theorem byte_view_write_size {h : Heap} {ref : BRef} {w : Nat} {input old new : Array UInt8}
    (get : Space.get h ref = some input) (window : h.bytes w = some old)
    (size : new.size = old.size) :
    ∃ input', Space.get { h with bytes := upd h.bytes w (some new) } ref = some input' ∧
      input'.size = input.size := by
  cases ref with
  | blk b =>
    by_cases same : b = w
    · subst b
      have eq : input = old := Option.some.inj (get.symm.trans window)
      exact ⟨new, by simp [Space.get], by simpa [eq] using size⟩
    · exact ⟨input, by simpa [Space.get, upd_ne _ _ _ _ same] using get, rfl⟩
  | str _ | dstate_depth _ | st_dist_code | st_length_code =>
    exact ⟨input, get, rfl⟩

theorem read_buf_ref_eq {h : Heap} {r : ZStreamRef} {z : ZStream}
    (hz : r.get h = some z) (buf : BPtr) (size : UInt32) :
    read_buf (some r) buf size h = rbCore (some r) buf (rbLen z.avail_in size) h := by
  unfold read_buf rbCore rbLen
  simp only [zrd_eq, hz, bind_app, pure_app]
  by_cases big : z.avail_in > size <;> simp only [big, if_true, if_false]
  all_goals rfl

def readStream (z : ZStream) (n : UInt32) (ref : BRef) (off : Nat) (a : UInt64) : ZStream :=
  { z with
    avail_in := z.avail_in - n
    next_in := .ref ref (off + n.toNat)
    total_in := z.total_in + n.toUInt64
    adler := a }

/-- `local unsigned read_buf(z_streamp strm, Bytef *buf, unsigned size)`.
On the zlib-wrapper branch, every stream view and input byte reference is
supported. The output describes the actual copy, cursors and checksum.
This is the wrapper-1 branch needed by default compression. -/
theorem read_buf_zlib {h : Heap} {r : ZStreamRef} {ds w io bo : Nat}
    {z : ZStream} {d : DeflateState} {ref : BRef} {ia wa : Array UInt8}
    (hz : r.get h = some z) (hs : z.state = some (.deflate ds)) (hd : h.dstates ds = some d)
    (wrap : d.wrap = 1) (pointer : z.next_in = .ref ref io)
    (input : Space.get h ref = some ia) (window : h.bytes w = some wa) (writable : h.ro w = false)
    (size : UInt32) (nonzero : rbLen z.avail_in size ≠ 0)
    (inputBound : io + (rbLen z.avail_in size).toNat ≤ ia.size)
    (windowBound : bo + (rbLen z.avail_in size).toNat ≤ wa.size)
    (separate : BRef.blk w ≠ ref ∨ bo + (rbLen z.avail_in size).toNat ≤ io ∨
      io + (rbLen z.avail_in size).toNat ≤ bo) :
    let n := rbLen z.avail_in size
    let a := adlerValue z.adler ((ia.toList.drop io).take n.toNat)
    read_buf (some r) (.ref (.blk w) bo) size h = .ok (n,
      r.put { h with bytes := upd h.bytes w (some (copyRange wa ia bo io n.toNat)) }
        (readStream z n ref io a)) := by
  let n := rbLen z.avail_in size
  let z1 := rbDec n z
  let h1 := r.put h z1
  let wa' := copyRange wa ia bo io n.toNat
  let h2 := { h1 with bytes := upd h1.bytes w (some wa') }
  let a := adlerValue z.adler ((ia.toList.drop io).take n.toNat)
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
  have checksum : Zlib.Adler32.adler32 z.adler (.ref (.blk w) bo) n h2 = .ok (a, h2) := by
    have run := ZlibF.Spec.Public.AdlerUpdateProof.adler_z_any_public
      (h := h2) (ref := .blk w) getW2 z.adler bo n.toUInt64 (by simpa [wa', size_copyRange] using windowBound)
    simpa only [C.run, Zlib.Adler32.adler32, UInt32.toNat_toUInt64, slices] using run
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
  have wrapper : rd (some (.tab ds)) (·.wrap) h2 = .ok (1, h2) := by simp [rdD_eq, hd2, wrap]
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
    show ((1 : Int32) == 1) = true from rfl, if_true,
    castDeflateState_ok, wrapper, seed, checksum, setAdler, readNext, advance, writeNext, pure_app]
  rfl

end Zlib.Deflate.Engine.Proofs
