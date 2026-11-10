import ZlibF.Proof.«deflate.c.gzip-fill-first»

/-! Exact CRC2 read fields and the zero-count split. These internal source
endpoints do not assert a full window invariant or an initialized CRC ledger. -/
namespace Zlib.Deflate.Engine.Proofs.DefaultGzipProofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Engine.Proofs
set_option autoImplicit false

/-- The actual source split: zero count leaves the entire heap and full 64-bit
seed alone; positive count copies first and computes CRC from the low32 seed.
The represented input may be foreign, and the stream reference may be embedded. -/
theorem read_buf_gzip_all_lengths {h : Heap} {r : ZStreamRef} {ds w io bo : Nat}
    {z : ZStream} {d : DeflateState} {ref : BRef} {ia wa : Array UInt8}
    (hz : r.get h = some z) (hs : z.state = some (.deflate ds)) (hd : h.dstates ds = some d)
    (wrap : d.wrap = 2) (globals : LibraryGlobals h) (pointer : z.next_in = .ref ref io)
    (input : Space.get h ref = some ia) (window : h.bytes w = some wa) (writable : h.ro w = false)
    (size : UInt32)
    (inputBound : io + (rbLen z.avail_in size).toNat ≤ ia.size)
    (windowBound : bo + (rbLen z.avail_in size).toNat ≤ wa.size)
    (separate : BRef.blk w ≠ ref ∨ bo + (rbLen z.avail_in size).toNat ≤ io ∨
      io + (rbLen z.avail_in size).toNat ≤ bo) :
    let n := rbLen z.avail_in size
    read_buf (some r) (.ref (.blk w) bo) size h = .ok (n,
      if n = 0 then h else
        r.put {h with bytes := upd h.bytes w (some (copyRange wa ia bo io n.toNat))}
          (readStream z n ref io (gzipReadValue z n ia io))) := by
  dsimp only
  by_cases zero : rbLen z.avail_in size = 0
  · simp only [zero, ↓reduceIte]
    exact read_buf_any_stream_zero hz _ _ zero
  · simp only [ite_eq_right zero]
    exact read_buf_gzip hz hs hd wrap (crc_statics_of_library_globals globals) pointer
      input window writable size zero inputBound windowBound separate

/-- Exact observations on the heap returned by `fill_body_resume_read_gzip`.
The checksum is an arbitrary-seed CRC update, not an assumed accepted-input ledger. -/
theorem resume_read_gzip_fields {h : Heap} {r : ZStreamRef} {ds w io : Nat}
    {z : ZStream} {d : DeflateState} {ref : BRef} {ia wa : Array UInt8}
    (hz : r.get h = some z) :
    let n := rbLen z.avail_in (fillMore d)
    let copied := copyRange wa ia (fillEnd d) io n.toNat
    let after := resumeReadGzipHeap h r ds w z d ref io ia wa
    r.get after = some (readStream z n ref io (gzipReadValue z n ia io)) ∧
    after.dstates ds = some (resumeReadState d n copied) ∧
    after.bytes w = some copied ∧
    after.static = h.static ∧ after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk ∧
    after.allocOk = h.allocOk ∧ after.garbage = h.garbage ∧
    after.libcErrorBorrow = h.libcErrorBorrow := by
  dsimp only
  simp [resumeReadGzipHeap, ZStreamRef.get_setD, stream_get_bytes, hz]
  cases r <;> simp only [resumeReadGzipHeap, setD, ZStreamRef.put] <;> split <;> rfl

/-- Hash priming only changes the hash key and the source-updated lookahead. -/
theorem resume_read_gzip_state_fields (d : DeflateState) (n : UInt32) (copied : Array UInt8) :
    (resumeReadState d n copied).wrap = d.wrap ∧
    (resumeReadState d n copied).strstart = d.strstart ∧
    (resumeReadState d n copied).lookahead = d.lookahead + n ∧
    (resumeReadState d n copied).insert = d.insert := by
  obtain ⟨key,record⟩ := resume_read_record d n copied
  rw [record]
  exact ⟨rfl,rfl,rfl,rfl⟩

/-- Exact observations on the heap returned by `fill_body_first_read_gzip`. -/
theorem first_read_gzip_fields {h : Heap} {r : ZStreamRef} {ds w io : Nat}
    {z : ZStream} {d : DeflateState} {ref : BRef} {ia wa : Array UInt8}
    (hz : r.get h = some z) :
    let n := rbLen z.avail_in 65536
    let copied := copyRange wa ia 0 io n.toNat
    let after := firstReadGzipHeap h r ds w z d ref io ia wa
    r.get after = some (readStream z n ref io (gzipReadValue z n ia io)) ∧
    after.dstates ds = some (primeState {d with lookahead := n} copied) ∧
    after.bytes w = some copied ∧
    after.static = h.static ∧ after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk ∧
    after.allocOk = h.allocOk ∧ after.garbage = h.garbage ∧
    after.libcErrorBorrow = h.libcErrorBorrow := by
  dsimp only
  simp [firstReadGzipHeap, ZStreamRef.get_setD, stream_get_bytes, hz]
  cases r <;> simp only [firstReadGzipHeap, setD, ZStreamRef.put] <;> split <;> rfl

end Zlib.Deflate.Engine.Proofs.DefaultGzipProofs
