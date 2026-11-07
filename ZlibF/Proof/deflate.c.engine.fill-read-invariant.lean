import ZlibF.Proof.«deflate.c.engine.fill-read-resume»

/-! # Representation and chains on the exact resumed-read result -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

theorem copy_range_prefix (destination source : Array UInt8) (offset sourceOffset count : Nat)
    (fit : offset + count ≤ destination.size) (i : Nat) (before : i < offset) :
    bfn (copyRange destination source offset sourceOffset count) i = bfn destination i := by
  unfold bfn
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?,
    getElem?_copyRange destination source offset sourceOffset count i fit]
  simp [show ¬ offset ≤ i ∧ i < offset + count by omega]

theorem resume_read_good {h : Heap} {r : ZStreamRef} {ds w io : Nat}
    {z : ZStream} {d : DeflateState} {ref : BRef} {ia wa : Array UInt8}
    (good : DGood h r ds z d) (get : h.bytes w = some wa) :
    let n := rbLen z.avail_in (fillMore d)
    let copied := copyRange wa ia (fillEnd d) io n.toNat
    let z' := readStream z n ref io (adlerValue z.adler ((ia.toList.drop io).take n.toNat))
    DGood (resumeReadHeap h r ds w z d ref io ia wa) r ds z' (resumeReadState d n copied) := by
  let n := rbLen z.avail_in (fillMore d)
  let copied := copyRange wa ia (fillEnd d) io n.toNat
  let hb := { h with bytes := upd h.bytes w (some copied) }
  have bytesGood : DGood hb r ds z d := good.bytes_set w copied wa get (size_copyRange _ _ _ _ _)
  obtain ⟨key, record⟩ := resume_prime_record { d with lookahead := d.lookahead + n } copied
  change resumeReadState d n copied = _ at record
  have inv : DStInv hb ds (resumeReadState d n copied) := by
    rw [record]
    exact { bytesGood.inv with blocks := bytesGood.inv.blocks_keys rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl }
  have keep : TrKeep d (resumeReadState d n copied) := by rw [record]; trkeep
  have back : (resumeReadState d n copied).strm = d.strm := by rw [record]
  have status : GoodStatus (resumeReadState d n copied).status := by rw [record]; exact good.live.status
  exact bytesGood.setZD rfl good.live.zalloc good.live.zfree back status inv keep

theorem resume_read_chains {h : Heap} {r : ZStreamRef} {ds w io top : Nat}
    {z : ZStream} {d : DeflateState} {ref : BRef} {ia wa : Array UInt8}
    (good : DGood h r ds z d) (chains : HeapChains h d top)
    (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa)
    (range : fillEnd d ≤ d.window_size.toNat) :
    let n := rbLen z.avail_in (fillMore d)
    let copied := copyRange wa ia (fillEnd d) io n.toNat
    HeapChains (resumeReadHeap h r ds w z d ref io ia wa) (resumeReadState d n copied) top := by
  let n := rbLen z.avail_in (fillMore d)
  let copied := copyRange wa ia (fillEnd d) io n.toNat
  have count := resume_read_counts good win get range
  have extent := window_extent good win get
  have fit : fillEnd d + n.toNat ≤ wa.size := by
    have more : (fillMore d).toNat = d.window_size.toNat - fillEnd d := fill_more_nat good win get range
    have nBound := rbLen_nat z.avail_in (fillMore d)
    change n.toNat = min z.avail_in.toNat (fillMore d).toNat at nBound
    omega
  have wrote := heap_chains_window_write (wa' := copied) chains win get
    (fun i hi => copy_range_prefix wa ia (fillEnd d) io n.toNat fit i hi)
  obtain ⟨wb, pb, qb, bytes, prev, head, hw, hp, hq, hbytes, hprev, hhead, H⟩ := wrote
  obtain ⟨key, record⟩ := resume_prime_record { d with lookahead := d.lookahead + n } copied
  change resumeReadState d n copied = _ at record
  refine ⟨wb, pb, qb, bytes, prev, head, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [record]; exact hw
  · rw [record]; exact hp
  · rw [record]; exact hq
  · simpa only [resumeReadHeap, setD_bytes, ZStreamRef.put_bytes] using hbytes
  · simpa only [resumeReadHeap, setD_words, ZStreamRef.put_words] using hprev
  · simpa only [resumeReadHeap, setD_words, ZStreamRef.put_words] using hhead
  · rw [record]
    apply chains_mono H (Nat.le_refl top)
    change fillEnd d ≤ d.strstart.toNat + (d.lookahead + n).toNat
    rw [count.2.1]
    dsimp only [fillEnd]
    omega

end Zlib.Deflate.Engine.Proofs
