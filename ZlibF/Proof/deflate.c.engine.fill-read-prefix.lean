import ZlibF.Proof.«deflate.c.engine.fill-slide-call»
import ZlibF.Proof.«deflate.c.engine.fill-prime-pending»

/-! # The real input-read prefix before deferred insertion -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

def pendingReadState (d : DeflateState) (n : UInt32) : DeflateState :=
  { d with lookahead := d.lookahead + n }

def pendingReadHeap (h : Heap) (r : ZStreamRef) (ds w : Nat) (z : ZStream) (d : DeflateState)
    (ref : BRef) (io : Nat) (ia wa : Array UInt8) : Heap :=
  let n := rbLen z.avail_in (fillMore d)
  let copied := copyRange wa ia (fillEnd d) io n.toNat
  let z' := readStream z n ref io (adlerValue z.adler ((ia.toList.drop io).take n.toNat))
  setD (r.put { h with bytes := upd h.bytes w (some copied) } z') ds (pendingReadState d n)

set_option maxHeartbeats 1200000 in
/-- The actual nonempty read reaches fillPrime with the real insert count
unchanged. Both pointers, checksum and caller cursors follow the source.
No fillPrime execution contract is a premise.
-/
theorem fill_after_slide_read_prefix {h : Heap} {r : ZStreamRef} {ds w io : Nat}
    {z : ZStream} {d : DeflateState} {ref : BRef} {ia wa : Array UInt8}
    (good : DGood h r ds z d) (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa)
    (range : fillEnd d ≤ d.window_size.toNat) (short : d.lookahead.toNat < 262)
    (noSlide : ¬ d.strstart ≥ d.w_size + (d.w_size - MIN_LOOKAHEAD_u)) (wrap : d.wrap = 1)
    (pointer : z.next_in = .ref ref io) (input : Space.get h ref = some ia)
    (inputBound : io + z.avail_in.toNat ≤ ia.size) (nonempty : z.avail_in ≠ 0)
    (separate : BRef.blk w ≠ ref) :
    fillAfterSlide (some (.tab ds)) (fillMore d) h =
      (do fillPrime (some (.tab ds)); pure false) (pendingReadHeap h r ds w z d ref io ia wa) := by
  let n := rbLen z.avail_in (fillMore d)
  let copied := copyRange wa ia (fillEnd d) io n.toNat
  let z' := readStream z n ref io (adlerValue z.adler ((ia.toList.drop io).take n.toNat))
  let hr := r.put { h with bytes := upd h.bytes w (some copied) } z'
  let hl := pendingReadHeap h r ds w z d ref io ia wa
  have counts := resume_read_counts good win get range
  have room := fill_room_no_slide good win get range short noSlide
  have extent := window_extent good win get
  have availPositive : 0 < z.avail_in.toNat := by
    have ne : z.avail_in.toNat ≠ 0 := by intro eq; exact nonempty (UInt32.toNat_inj.mp eq)
    omega
  have count : n.toNat = min z.avail_in.toNat (fillMore d).toNat := rbLen_nat _ _
  have nonzero : n ≠ 0 := by
    intro zero
    have value : n.toNat = 0 := by rw [zero]; rfl
    omega
  have windowBound : fillEnd d + n.toNat ≤ wa.size := by
    have more : (fillMore d).toNat = d.window_size.toNat - fillEnd d := fill_more_nat good win get range
    omega
  have read := read_buf_zlib (bo := fillEnd d) good.live.hz good.live.zst good.live.hs wrap pointer input
    get (window_writable good win) (fillMore d) nonzero (by omega) windowBound (Or.inl separate)
  have first : padd d.window d.strstart.toNat h = .ok (.ref (.blk w) d.strstart.toNat, h) := by
    rw [win]
    simpa only [OkOn, padd, Nat.zero_add] using Ptr.add_nat_ok (off := 0) (n := d.strstart.toNat)
      (show Space.get h (BRef.blk w) = some wa from get) (by dsimp only [fillEnd] at range; omega)
  have second : padd (.ref (.blk w) d.strstart.toNat : BPtr) d.lookahead.toNat h =
      .ok (.ref (.blk w) (fillEnd d), h) := by
    simpa only [OkOn, padd, fillEnd] using Ptr.add_nat_ok (off := d.strstart.toNat) (n := d.lookahead.toNat)
      (show Space.get h (BRef.blk w) = some wa from get) (by omega : fillEnd d ≤ wa.size)
  have stateR : hr.dstates ds = some d := by simpa [hr] using good.live.hs
  have update : wr (some (.tab ds)) (fun state => { state with lookahead := state.lookahead + n }) hr =
      .ok ((), hl) := by simp [wrD_eq, stateR, hl, pendingReadHeap, hr, pendingReadState, n, copied, z', good.live.hs]
  unfold fillAfterSlide
  simp only [bind_app, rdD_eq, good.live.hs, good.live.back, zrd_eq, good.live.hz,
    beq_eq_false_iff_ne.mpr nonempty, Bool.false_eq_true, if_false, ldDeflateState_tab good.live.hs,
    first, second]
  rw [read]
  change (do
    wr (some (.tab ds)) (fun state => { state with lookahead := state.lookahead + n })
    fillPrime (some (.tab ds))
    pure false) hr = _
  rw [bind_app, update]
  rfl

theorem pending_read_good {h : Heap} {r : ZStreamRef} {ds w io : Nat}
    {z : ZStream} {d : DeflateState} {ref : BRef} {ia wa : Array UInt8}
    (good : DGood h r ds z d) (get : h.bytes w = some wa) :
    let n := rbLen z.avail_in (fillMore d)
    let z' := readStream z n ref io (adlerValue z.adler ((ia.toList.drop io).take n.toNat))
    DGood (pendingReadHeap h r ds w z d ref io ia wa) r ds z' (pendingReadState d n) := by
  let n := rbLen z.avail_in (fillMore d)
  let copied := copyRange wa ia (fillEnd d) io n.toNat
  let hb := { h with bytes := upd h.bytes w (some copied) }
  have bytesGood : DGood hb r ds z d := good.bytes_set w copied wa get (size_copyRange _ _ _ _ _)
  have inv : DStInv hb ds (pendingReadState d n) :=
    { bytesGood.inv with blocks := bytesGood.inv.blocks_keys rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl }
  exact bytesGood.setZD rfl good.live.zalloc good.live.zfree rfl good.live.status inv (by trkeep)

theorem pending_read_chains {h : Heap} {r : ZStreamRef} {ds w io top : Nat}
    {z : ZStream} {d : DeflateState} {ref : BRef} {ia wa : Array UInt8}
    (good : DGood h r ds z d) (chains : HeapChains h d top)
    (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa) (range : fillEnd d ≤ d.window_size.toNat) :
    let n := rbLen z.avail_in (fillMore d)
    HeapChains (pendingReadHeap h r ds w z d ref io ia wa) (pendingReadState d n) top := by
  let n := rbLen z.avail_in (fillMore d)
  let copied := copyRange wa ia (fillEnd d) io n.toNat
  have counts := resume_read_counts good win get range
  have extent := window_extent good win get
  have fit : fillEnd d + n.toNat ≤ wa.size := by
    have more : (fillMore d).toNat = d.window_size.toNat - fillEnd d := fill_more_nat good win get range
    have nCount : n.toNat = min z.avail_in.toNat (fillMore d).toNat := rbLen_nat _ _
    omega
  have wrote := heap_chains_window_write (wa' := copied) chains win get
    (fun i hi => copy_range_prefix wa ia (fillEnd d) io n.toNat fit i hi)
  obtain ⟨wb, pb, qb, bytes, prev, head, hw, hp, hq, hbytes, hprev, hhead, H⟩ := wrote
  refine ⟨wb, pb, qb, bytes, prev, head, hw, hp, hq, ?_, ?_, ?_, ?_⟩
  · simpa only [pendingReadHeap, setD_bytes, ZStreamRef.put_bytes] using hbytes
  · simpa only [pendingReadHeap, setD_words, ZStreamRef.put_words] using hprev
  · simpa only [pendingReadHeap, setD_words, ZStreamRef.put_words] using hhead
  · apply chains_mono H (Nat.le_refl top)
    change fillEnd d ≤ d.strstart.toNat + (d.lookahead + n).toNat
    rw [counts.2.1]
    dsimp only [fillEnd]
    omega

end Zlib.Deflate.Engine.Proofs
