import ZlibF.Proof.«deflate.c.engine.read-zlib»
import ZlibF.Proof.«public-crc-updates»
import ZlibF.Proof.«deflate.c.engine.fill-full-storage»
import ZlibF.Proof.«deflate.c.engine.fill-caller-storage»
import ZlibF.Proof.«deflate.c.universal-invariant»
import ZlibF.Proof.«deflate.c.engine.short-search»

/-!
# deflate.c, universal engine: `read_buf` and `fill_window` for every parameter tuple

Batch B of the deflate skeleton (`docs/progress.md`, Core proof skeletons). The default-family
lemmas (`deflate.c.engine.fill-*`) fix `wrap = 1`. This module removes that restriction: the
checksum of `read_buf` is the Adler-32 for `wrap = 1`, the CRC-32 for `wrap = 2` (the CRC tables
are the library globals), and no update otherwise.
-/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Proofs.DefaultInit
set_option autoImplicit false

/-- The checksum `read_buf` stores after copying `bytes`, for the wrapper `wrap`. -/
def checksumValue (wrap : Int32) (seed : UInt64) (bytes : List UInt8) : UInt64 :=
  if wrap = 1 then adlerValue seed bytes
  else if wrap = 2 then (ZlibF.Spec.crc32Update seed.toUInt32 bytes).toUInt64
  else seed

/-- `local unsigned read_buf(z_streamp strm, Bytef *buf, unsigned size)`, every wrapper.
The copy, the cursors and the checksum of the copied bytes; nothing else changes. -/
theorem read_buf_any {h : Heap} {r : ZStreamRef} {ds w io bo : Nat}
    {z : ZStream} {d : DeflateState} {ref : BRef} {ia wa : Array UInt8}
    (hz : r.get h = some z) (hs : z.state = some (.deflate ds)) (hd : h.dstates ds = some d)
    (globals : d.wrap = 2 → CrcGlobals h) (pointer : z.next_in = .ref ref io)
    (input : Space.get h ref = some ia) (window : h.bytes w = some wa) (writable : h.ro w = false)
    (size : UInt32) (nonzero : rbLen z.avail_in size ≠ 0)
    (inputBound : io + (rbLen z.avail_in size).toNat ≤ ia.size)
    (windowBound : bo + (rbLen z.avail_in size).toNat ≤ wa.size)
    (separate : BRef.blk w ≠ ref ∨ bo + (rbLen z.avail_in size).toNat ≤ io ∨
      io + (rbLen z.avail_in size).toNat ≤ bo) :
    let n := rbLen z.avail_in size
    let a := checksumValue d.wrap z.adler ((ia.toList.drop io).take n.toNat)
    read_buf (some r) (.ref (.blk w) bo) size h = .ok (n,
      r.put { h with bytes := upd h.bytes w (some (copyRange wa ia bo io n.toNat)) }
        (readStream z n ref io a)) := by
  let n := rbLen z.avail_in size
  let z1 := rbDec n z
  let h1 := r.put h z1
  let wa' := copyRange wa ia bo io n.toNat
  let h2 := { h1 with bytes := upd h1.bytes w (some wa') }
  let a := checksumValue d.wrap z.adler ((ia.toList.drop io).take n.toNat)
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
  have wrapper : rd (some (.tab ds)) (·.wrap) h2 = .ok (d.wrap, h2) := by simp [rdD_eq, hd2]
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
  by_cases one : d.wrap = 1
  · have checksum : Zlib.Adler32.adler32 z.adler (.ref (.blk w) bo) n h2 = .ok (a, h2) := by
      have run := ZlibF.Spec.Public.AdlerUpdateProof.adler_z_any_public
        (h := h2) (ref := .blk w) getW2 z.adler bo n.toUInt64 (by simpa [wa', size_copyRange] using windowBound)
      simpa only [C.run, Zlib.Adler32.adler32, UInt32.toNat_toUInt64, slices, a, checksumValue,
        if_pos one] using run
    simp only [rbCore, nz, Bool.false_eq_true, ite_false, bind_app, dec, read, copy, state,
      castDeflateState_ok, wrapper, (show (d.wrap == 1) = true by simp [one]), ite_true,
      seed, checksum, setAdler, readNext, advance, writeNext, pure_app]
    rfl
  · by_cases two : d.wrap = 2
    · have checksum : Zlib.Crc32.crc32 z.adler (.ref (.blk w) bo) n h2 = .ok (a, h2) := by
        have g2 : CrcGlobals h2 := by
          obtain ⟨t1, t2⟩ := globals two
          exact ⟨by simpa [h2, h1] using t1, by simpa [h2, h1] using t2⟩
        have run := ZlibF.Spec.Public.Proofs.crc32 h2 z.adler (.ref (.blk w) bo) n
          ((wa'.toList.drop bo).take n.toNat) g2
          (Or.inr ⟨.blk w, bo, wa', rfl, getW2, by simpa [wa', size_copyRange] using windowBound, rfl⟩)
        simpa only [C.run, reduceCtorEq, ite_false, slices, a, checksumValue, if_neg one,
          if_pos two] using run
      simp only [rbCore, nz, Bool.false_eq_true, ite_false, bind_app, dec, read, copy, state,
        castDeflateState_ok, wrapper, (show (d.wrap == 1) = false by simpa using one),
        (show (d.wrap == 2) = true by simp [two]), ite_true,
        seed, checksum, setAdler, readNext, advance, writeNext, pure_app]
      rfl
    · have same : a = z.adler := by simp [a, checksumValue, one, two]
      have keep : h3 = h2 := by
        dsimp only [h3]
        have : z2 = z1 := by simp [z2, same, z1, rbDec]
        rw [this]
        exact ZStreamRef.put_self hz2
      have n1 : (d.wrap == 1) = false := by simpa using one
      have n2 : (d.wrap == 2) = false := by simpa using two
      simp only [keep] at readNext advance writeNext
      simp only [rbCore, nz, Bool.false_eq_true, ite_false, bind_app, dec, read, copy, state,
        castDeflateState_ok, wrapper, n1, n2, readNext, advance, writeNext, pure_app]
      rfl


def pendingReadHeapAny (h : Heap) (r : ZStreamRef) (ds w : Nat) (z : ZStream) (d : DeflateState)
    (ref : BRef) (io : Nat) (ia wa : Array UInt8) : Heap :=
  let n := rbLen z.avail_in (fillMore d)
  let copied := copyRange wa ia (fillEnd d) io n.toNat
  let z' := readStream z n ref io (checksumValue d.wrap z.adler ((ia.toList.drop io).take n.toNat))
  setD (r.put { h with bytes := upd h.bytes w (some copied) } z') ds (pendingReadState d n)

set_option maxHeartbeats 1200000 in
/-- The actual nonempty read reaches fillPrime with the real insert count
unchanged. Both pointers, checksum and caller cursors follow the source.
No fillPrime execution contract is a premise.
-/
theorem fill_after_slide_read_prefix_any {h : Heap} {r : ZStreamRef} {ds w io : Nat}
    {z : ZStream} {d : DeflateState} {ref : BRef} {ia wa : Array UInt8}
    (good : DGood h r ds z d) (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa)
    (range : fillEnd d ≤ d.window_size.toNat) (short : d.lookahead.toNat < 262)
    (noSlide : ¬ d.strstart ≥ d.w_size + (d.w_size - MIN_LOOKAHEAD_u)) (globals : d.wrap = 2 → CrcGlobals h)
    (pointer : z.next_in = .ref ref io) (input : Space.get h ref = some ia)
    (inputBound : io + z.avail_in.toNat ≤ ia.size) (nonempty : z.avail_in ≠ 0)
    (separate : BRef.blk w ≠ ref) :
    fillAfterSlide (some (.tab ds)) (fillMore d) h =
      (do fillPrime (some (.tab ds)); pure false) (pendingReadHeapAny h r ds w z d ref io ia wa) := by
  let n := rbLen z.avail_in (fillMore d)
  let copied := copyRange wa ia (fillEnd d) io n.toNat
  let z' := readStream z n ref io (checksumValue d.wrap z.adler ((ia.toList.drop io).take n.toNat))
  let hr := r.put { h with bytes := upd h.bytes w (some copied) } z'
  let hl := pendingReadHeapAny h r ds w z d ref io ia wa
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
  have read := read_buf_any (bo := fillEnd d) good.live.hz good.live.zst good.live.hs globals pointer input
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
      .ok ((), hl) := by simp [wrD_eq, stateR, hl, pendingReadHeapAny, hr, pendingReadState, n, copied, z', good.live.hs]
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

theorem pending_read_good_any {h : Heap} {r : ZStreamRef} {ds w io : Nat}
    {z : ZStream} {d : DeflateState} {ref : BRef} {ia wa : Array UInt8}
    (good : DGood h r ds z d) (get : h.bytes w = some wa) :
    let n := rbLen z.avail_in (fillMore d)
    let z' := readStream z n ref io (checksumValue d.wrap z.adler ((ia.toList.drop io).take n.toNat))
    DGood (pendingReadHeapAny h r ds w z d ref io ia wa) r ds z' (pendingReadState d n) := by
  let n := rbLen z.avail_in (fillMore d)
  let copied := copyRange wa ia (fillEnd d) io n.toNat
  let hb := { h with bytes := upd h.bytes w (some copied) }
  have bytesGood : DGood hb r ds z d := good.bytes_set w copied wa get (size_copyRange _ _ _ _ _)
  have inv : DStInv hb ds (pendingReadState d n) :=
    { bytesGood.inv with blocks := bytesGood.inv.blocks_keys rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl }
  exact bytesGood.setZD rfl good.live.zalloc good.live.zfree rfl good.live.status inv (by trkeep)

theorem pending_read_chains_any {h : Heap} {r : ZStreamRef} {ds w io top : Nat}
    {z : ZStream} {d : DeflateState} {ref : BRef} {ia wa : Array UInt8}
    (good : DGood h r ds z d) (chains : HeapChains h d top)
    (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa) (range : fillEnd d ≤ d.window_size.toNat) :
    let n := rbLen z.avail_in (fillMore d)
    HeapChains (pendingReadHeapAny h r ds w z d ref io ia wa) (pendingReadState d n) top := by
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
  · simpa only [pendingReadHeapAny, setD_bytes, ZStreamRef.put_bytes] using hbytes
  · simpa only [pendingReadHeapAny, setD_words, ZStreamRef.put_words] using hprev
  · simpa only [pendingReadHeapAny, setD_words, ZStreamRef.put_words] using hhead
  · apply chains_mono H (Nat.le_refl top)
    change fillEnd d ≤ d.strstart.toNat + (d.lookahead + n).toNat
    rw [counts.2.1]
    dsimp only [fillEnd]
    omega

theorem pending_read_storage_frame_any (h : Heap) (r : ZStreamRef) (ds w : Nat) (z : ZStream) (d : DeflateState)
    (ref : BRef) (io : Nat) (ia wa : Array UInt8)
    (changed : Nat → Prop) (stateWrite : changed ds) (windowWrite : changed w) :
    ByteFrame h (pendingReadHeapAny h r ds w z d ref io ia wa) changed := by
  refine ⟨by simp [pendingReadHeapAny], ?_, ?_, fun _ _ => by simp [pendingReadHeapAny]⟩
  · intro i outside
    have different : i ≠ w := by intro equal; subst i; exact outside windowWrite
    simp [pendingReadHeapAny, upd_ne _ _ _ _ different]
  · intro i outside
    have different : i ≠ ds := by intro equal; subst i; exact outside stateWrite
    simp [pendingReadHeapAny, setD, upd_ne _ _ _ _ different]

theorem pending_read_heap_full_storage_any {h : Heap} {r : ZStreamRef} {ds w : Nat}
    {z : ZStream} {d : DeflateState} {ref : BRef} {io : Nat} {ia wa : Array UInt8}
    (good : DGood h r ds z d) (window : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa) :
    Shape h (pendingReadHeapAny h r ds w z d ref io ia wa) ∧
      Frame h (pendingReadHeapAny h r ds w z d ref io ia wa) (fun b => StreamRoot r b ∨ DeflateOwned ds d b) ∧
      LiveChange h (pendingReadHeapAny h r ds w z d ref io ia wa) (fun _ => False) (fun _ => False) ∧
      (pendingReadHeapAny h r ds w z d ref io ia wa).nalloc = h.nalloc ∧
      (pendingReadHeapAny h r ds w z d ref io ia wa).nextBlk = h.nextBlk := by
  let n := rbLen z.avail_in (fillMore d)
  let data := copyRange wa ia (fillEnd d) io n.toNat
  let copied := Zlib.Trees.Proofs.Out.setB h w data
  let stream := readStream z n ref io (checksumValue d.wrap z.adler ((ia.toList.drop io).take n.toNat))
  let updated := r.put copied stream
  have copyShape : Shape h copied := shape_setB get data
  have getter : r.get copied = some z := by simpa only [copied, Zlib.Trees.Proofs.Out.setB, stream_get_bytes] using good.live.hz
  have streamShape : Shape copied updated := shape_put getter stream
  have stateGet : updated.dstates ds = some d := by simpa only [updated, copied, Zlib.Trees.Proofs.Out.setB, ZStreamRef.put_dstates] using good.live.hs
  have stateShape := shape_setD stateGet (pendingReadState d n)
  have shape : Shape h (pendingReadHeapAny h r ds w z d ref io ia wa) := (copyShape.trans streamShape).trans stateShape
  have copyFrame : Frame h copied (fun b => StreamRoot r b ∨ DeflateOwned ds d b) := by
    apply full_frame_weaken (byte_store_full_frame h w data)
    intro b same
    subst b
    exact Or.inr (Or.inr (Or.inl window))
  have streamFrame : Frame copied updated (fun b => StreamRoot r b ∨ DeflateOwned ds d b) :=
    full_frame_weaken (stream_store_full_frame copied r stream) (fun _ root => Or.inl root)
  have stateFrame : Frame updated (setD updated ds (pendingReadState d n)) (fun b => StreamRoot r b ∨ DeflateOwned ds d b) :=
    full_frame_weaken (state_store_full_frame updated ds (pendingReadState d n)) (fun _ same => Or.inr (Or.inl same))
  have frame := full_frame_trans_shape (full_frame_trans_shape copyFrame streamFrame copyShape) stateFrame (copyShape.trans streamShape)
  exact ⟨shape, frame, full_shape_live_change shape, by simp [pendingReadHeapAny], by simp [pendingReadHeapAny]⟩

set_option maxHeartbeats 3000000 in
/-- The actual non-sliding refill combines the complete source read,
pending hash insertion and padding with the full object/allocation frame. -/
theorem fill_window_pending_complete_full_storage_any {h : Heap} {r : ZStreamRef} {ds w io : Nat}
    {z : ZStream} {d : DeflateState} {ref : BRef} {ia wa : Array UInt8}
    (good : DGood h r ds z d) (chains : HeapChains h d (d.strstart.toNat - d.insert.toNat))
    (pending : d.insert.toNat ≤ d.strstart.toNat)
    (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa)
    (range : fillEnd d ≤ d.window_size.toNat) (short : d.lookahead.toNat < 262)
    (noSlide : ¬ d.strstart ≥ d.w_size + (d.w_size - MIN_LOOKAHEAD_u)) (globals : d.wrap = 2 → CrcGlobals h)
    (pointer : z.next_in = .ref ref io) (input : Space.get h ref = some ia)
    (inputBound : io + z.avail_in.toNat ≤ ia.size) (nonempty : z.avail_in ≠ 0)
    (separate : BRef.blk w ≠ ref) :
    let n := rbLen z.avail_in (fillMore d)
    let copied := copyRange wa ia (fillEnd d) io n.toNat
    let z' := readStream z n ref io (checksumValue d.wrap z.adler ((ia.toList.drop io).take n.toNat))
    ∃ after result output,
      fill_window (some (.tab ds)) h = .ok ((), after) ∧ DGood after r ds z' result ∧
      HeapChains after result (result.strstart.toNat - result.insert.toNat) ∧
      result.window = .ref (.blk w) 0 ∧ after.bytes w = some output ∧
      fillEnd result ≤ result.window_size.toNat ∧
      min (fillEnd result + 258) result.window_size.toNat ≤ result.high_water.toNat ∧
      (3 ≤ result.lookahead.toNat → result.insert = 0 ∧
        InsHForm result.hash_shift result.hash_mask (bfn output) result.strstart.toNat result.ins_h) ∧
      result = { d with
        lookahead := d.lookahead + n, ins_h := result.ins_h, insert := result.insert, high_water := result.high_water } ∧
      result.insert.toNat = min d.insert.toNat (2 - result.lookahead.toNat) ∧
      (∀ b, b ≠ w → after.bytes b = h.bytes b) ∧
      (∀ i, i < fillEnd result → bfn output i = bfn copied i) ∧
      (262 ≤ result.lookahead.toNat ∨ z'.avail_in = 0) ∧ ByteFrame h after (DeflateOwned ds d) ∧
      Shape h after ∧ Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  let n := rbLen z.avail_in (fillMore d)
  let copied := copyRange wa ia (fillEnd d) io n.toNat
  let z' := readStream z n ref io (checksumValue d.wrap z.adler ((ia.toList.drop io).take n.toNat))
  let hr := pendingReadHeapAny h r ds w z d ref io ia wa
  let dr := pendingReadState d n
  have goodR : DGood hr r ds z' dr := pending_read_good_any good get
  have chainsR : HeapChains hr dr (dr.strstart.toNat - dr.insert.toNat) :=
    pending_read_chains_any good chains win get range
  have counts := resume_read_counts good win get range
  have rangeR : fillEnd dr ≤ dr.window_size.toNat := counts.2.2
  have getR : hr.bytes w = some copied := by simp [hr, pendingReadHeapAny, n, copied]
  have winR : dr.window = .ref (.blk w) 0 := win
  obtain ⟨hp, dp, primeRun, goodP, chainsP, bytesP, frameP, countP, formP, storageP, shapeP, fullP, allocP, nextP⟩ :=
    fill_prime_pending_full_storage goodR chainsR winR getR rangeR pending
  change fillPrime (some (.tab ds)) (pendingReadHeapAny h r ds w z d ref io ia wa) = .ok ((), hp) at primeRun
  have fields : dp = { d with lookahead := d.lookahead + n, ins_h := dp.ins_h, insert := dp.insert } := by
    unfold PendingInsertFrame at frameP
    rw [frameP]
    rfl
  have lookP : dp.lookahead.toNat = d.lookahead.toNat + n.toNat := by rw [fields]; exact counts.2.1
  have rangeP : fillEnd dp ≤ dp.window_size.toNat := by rw [fields]; exact counts.2.2
  have winP : dp.window = .ref (.blk w) 0 := by rw [fields]; exact win
  have getP : hp.bytes w = some copied := by rw [bytesP]; exact getR
  have capacity := fill_room_no_slide good win get range short noSlide
  have inputCount : n.toNat = min z.avail_in.toNat (fillMore d).toNat := rbLen_nat _ _
  have exhausted : dp.lookahead < MIN_LOOKAHEAD_u → z'.avail_in = 0 := by
    intro small
    have less : dp.lookahead.toNat < 262 := UInt32.lt_iff_toNat_lt.mp small
    have all : n = z.avail_in := UInt32.toNat_inj.mp (by omega)
    simp only [z', readStream, all, UInt32.sub_self]
  have condition : fillCond (some (.tab ds)) false hp = .ok ((false, false), hp) := by
    unfold fillCond
    simp only [bind_app, ldDeflateState_tab goodP.live.hs, Bool.false_eq_true, ite_false, goodP.live.back]
    by_cases small : dp.lookahead < MIN_LOOKAHEAD_u
    · simp only [small, ite_true, bind_app, zrd_eq, goodP.live.hz, exhausted small]
      rfl
    · simp only [small, ite_false]
      rfl
  have body : fillBody (some (.tab ds)) d.w_size false h = .ok (false, hp) := by
    rw [fill_body_slide_source]
    simp only [bind_app, ldDeflateState_tab good.live.hs, noSlide, ite_false]
    rw [fill_after_slide_read_prefix_any good win get range short noSlide globals pointer input inputBound nonempty separate]
    simp only [bind_app, primeRun, pure_app]
  have loop := do_once body condition
  have pad := fill_high_water_complete goodP winP getP (window_writable goodP winP) rangeP
  let after := paddedHeap hp ds w dp copied
  let result := paddedState dp
  let output := fillRange copied (paddingStart dp) (paddingCount dp) 0
  have run : fill_window (some (.tab ds)) h = .ok ((), after) := by
    rw [fill_window_source]
    simp only [bind_app, rdD_eq, good.live.hs, loop]
    exact pad
  have readFrame : ByteFrame h hr (DeflateOwned ds d) :=
    pending_read_storage_frame_any h r ds w z d ref io ia wa _ (Or.inl rfl) (Or.inr (Or.inl win))
  have primeFrame : ByteFrame hr hp (DeflateOwned ds d) :=
    storageP.weaken (fun i equal => Or.inl equal)
  have wholeFrame : ByteFrame h after (DeflateOwned ds d) :=
    (readFrame.trans primeFrame).trans
      (padded_storage_frame hp ds w dp copied _ (Or.inl rfl) (Or.inr (Or.inl win)))
  obtain ⟨shapeR, fullR, _liveR, allocR, nextR⟩ := pending_read_heap_full_storage_any good win get
  obtain ⟨shapePad, fullPad, _livePad, allocPad, nextPad⟩ := padded_heap_full_storage goodP winP getP
  have ownedP : DeflateOwned ds dp = DeflateOwned ds d := by rw [fields]; rfl
  have fullPad' : Frame hp after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) := by
    rw [← ownedP]
    exact fullPad
  have shape := (shapeR.trans shapeP).trans shapePad
  have full := full_frame_trans_shape (full_frame_trans_shape fullR fullP shapeR) fullPad' (shapeR.trans shapeP)
  refine ⟨after, result, output, run, padded_good goodP winP getP rangeP,
    padded_chains goodP chainsP winP getP rangeP, winP, ?_, rangeP,
    padded_initialized goodP winP getP rangeP, ?_, ?_, ?_, ?_, ?_, ?_, wholeFrame, shape, full, full_shape_live_change shape,
    allocPad.trans (allocP.trans allocR), nextPad.trans (nextP.trans nextR)⟩
  · simp [after, output, paddedHeap]
  · intro large
    obtain ⟨zero, form⟩ := formP large
    exact ⟨zero, padded_form goodP winP getP rangeP large form⟩
  · dsimp only [result, paddedState]
    rw [fields]
  · change dp.insert.toNat = min d.insert.toNat (2 - dp.lookahead.toNat)
    have look : dp.lookahead = dr.lookahead := congrArg (·.lookahead) frameP
    rw [look]
    exact countP
  · intro b different
    change (paddedHeap hp ds w dp copied).bytes b = _
    simp only [paddedHeap, setD_bytes, bytesP,
      hr, pendingReadHeapAny, setD_bytes, ZStreamRef.put_bytes, upd_ne _ _ _ _ different]
  · exact padded_prefix goodP winP getP rangeP
  · by_cases enough : 262 ≤ dp.lookahead.toNat
    · exact Or.inl enough
    · right
      exact exhausted (UInt32.lt_iff_toNat_lt.mpr (by change dp.lookahead.toNat < 262; omega))


set_option maxHeartbeats 1200000 in
/-- `fill_slide_run` with the signed subtraction as a premise instead of the default symbol ledger. -/
theorem fill_slide_run_any {h : Heap} {r : ZStreamRef} {ds w p q : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8} {pa qa : Array UInt16}
    (good : DGood h r ds z d) (env : HashEnv h d w q p wa qa pa)
    (signed : lsub d.block_start d.w_size.toUInt64.toInt64 =
      pure (Int64.ofInt (d.block_start.toInt - (d.w_size.toNat : Int))))
    (range : fillEnd d ≤ d.window_size.toNat)
    (taken : d.strstart ≥ d.w_size + (d.w_size - MIN_LOOKAHEAD_u)) :
    ∃ qa' pa', fillSlide (some (.tab ds)) d d.w_size (fillMore d) h =
      .ok ((), slideHeap h ds w p q d wa pa' qa') ∧
      qa'.size = qa.size ∧ pa'.size = pa.size ∧
      (∀ i, wfn qa' i = if i < d.hash_size.toNat then slideVal d.w_size (wfn qa i) else wfn qa i) ∧
      (∀ i, wfn pa' i = if i < d.w_size.toNat then slideVal d.w_size (wfn pa i) else wfn pa i) := by
  have geometry := fill_slide_counts good env.win env.wbytes range taken
  let copied := slideWindow d wa
  let hc := { h with bytes := upd h.bytes w (some copied) }
  let hp := setD hc ds (slideBeforeHash d)
  have add : padd d.window d.w_size.toNat h = .ok (.ref (.blk w) d.w_size.toNat, h) := by
    rw [env.win]
    simpa only [OkOn, padd, Nat.zero_add] using Ptr.add_nat_ok (off := 0) (n := d.w_size.toNat)
      (show Space.get h (BRef.blk w) = some wa from env.wbytes) (by omega)
  have copy : memcpyB d.window (.ref (.blk w) d.w_size.toNat) (d.w_size - fillMore d).toNat h =
      .ok ((), hc) := by
    rw [env.win]
    exact Ptr.memcpy_ok (od := 0) (os := d.w_size.toNat)
      (show Space.get h (BRef.blk w) = some wa from env.wbytes) env.wbytes env.wro
      (by omega) geometry.2.2.2.1 (Or.inr (Or.inl (by omega)))
  have getH : hp.words q = some qa := env.hwords
  have getP : hp.words p = some pa := env.pwords
  have bounds := slide_window_sizes good
  have hashPositive : 1 ≤ d.hash_size.toNat := by
    obtain ⟨bits, _, _, size, _, _⟩ := env.params.bits
    rw [size]
    exact Nat.two_pow_pos _
  obtain ⟨qa', pa', hash, sizeH, sizeP, viewH, viewP⟩ := slide_hash_ok (h := hp) (sr := ds)
    (d := slideBeforeHash d) (by simp [hp]) env.headp env.prevp getH getP env.hne
    env.hsize env.wsize hashPositive (by change 1 ≤ d.w_size.toNat; omega)
  refine ⟨qa', pa', ?_, sizeH, sizeP, viewH, viewP⟩
  have dsCopy : hc.dstates ds = some d := good.live.hs
  unfold fillSlide
  simp only [bind_app, add, copy, wrD_eq, rdD_eq, dsCopy, setD_dstates_same, setD_setD, signed, pure_app]
  simpa only [hp, hc, copied, slideBeforeHash, slideState, slideHeap, setD, setW, upd_upd] using hash


/-- The checked `long` subtraction of a slide, from a lower bound on `block_start`. -/
theorem block_start_slide_signed {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (good : DGood h r ds z d) (low : -(2 : Int) ^ 62 ≤ d.block_start.toInt) :
    lsub d.block_start d.w_size.toUInt64.toInt64 =
      pure (Int64.ofInt (d.block_start.toInt - (d.w_size.toNat : Int))) := by
  have ws : d.w_size.toNat ≤ 32768 := (slide_window_sizes good).2
  have cast : d.w_size.toUInt64.toInt64.toInt = (d.w_size.toNat : Int) := by
    rw [Int64.toInt, UInt64.toBitVec_toInt64, BitVec.toInt_eq_toNat_of_lt]
    · simp
    · simp
      omega
  have valueLo : -9223372036854775808 ≤ d.block_start.toInt - (d.w_size.toNat : Int) := by
    have : (2 : Int) ^ 62 = 4611686018427387904 := rfl
    omega
  have valueHi : d.block_start.toInt - (d.w_size.toNat : Int) ≤ 9223372036854775807 := by
    have := Int64.toInt_lt d.block_start
    have : (2 : Int) ^ 63 = 9223372036854775808 := rfl
    omega
  unfold lsub chk64
  rw [cast]
  simp only [valueLo, valueHi, and_self, if_true]


/-! ## The complete `fill_window` for every parameter tuple -/

variable {roll : Prop}

/-- What `fill_window` needs of the state it is called on (a call-boundary or loop state of a
strategy). Every field is a representation fact; none is a callee contract. -/
structure FillPre (roll : Prop) (h : Heap) (r : ZStreamRef) (ds : Nat) (z : ZStream) (d : DeflateState) : Prop where
  good : DGood h r ds z d
  chains : HeapChains h d (d.strstart.toNat - d.insert.toNat)
  pending : d.insert.toNat ≤ d.strstart.toNat
  range : fillEnd d ≤ d.window_size.toNat
  form : 3 ≤ d.lookahead.toNat → d.insert = 0 ∧ (roll → ∃ w wa, d.window = .ref (.blk w) 0 ∧
    h.bytes w = some wa ∧ InsHForm d.hash_shift d.hash_mask (bfn wa) d.strstart.toNat d.ins_h)
  globals : d.wrap = 2 → CrcGlobals h

/-- `base` with the four fields `fill_window` sets after its slide taken from `result`. -/
def fillResult (base result : DeflateState) : DeflateState :=
  { base with
    lookahead := result.lookahead
    ins_h := result.ins_h
    insert := result.insert
    high_water := result.high_water }

/-- What `fill_window` establishes. `base` is the state before the read: `d`, or `d` slid by one
window. Only `lookahead`, `ins_h`, `insert` and `high_water` change after that. -/
structure FillPost (roll : Prop) (h after : Heap) (r : ZStreamRef) (ds : Nat) (z z' : ZStream) (d result : DeflateState) : Prop where
  good : DGood after r ds z' result
  chains : HeapChains after result (result.strstart.toNat - result.insert.toNat)
  pending : result.insert.toNat ≤ result.strstart.toNat
  range : fillEnd result ≤ result.window_size.toNat
  form : 3 ≤ result.lookahead.toNat → result.insert = 0 ∧ (roll → ∃ w wa, result.window = .ref (.blk w) 0 ∧
    after.bytes w = some wa ∧ InsHForm result.hash_shift result.hash_mask (bfn wa) result.strstart.toNat result.ins_h)
  stopped : 262 ≤ result.lookahead.toNat ∨ z'.avail_in = 0
  noSlide : ¬ result.strstart ≥ result.w_size + (result.w_size - MIN_LOOKAHEAD_u)
  fields : ∃ base, (base = d ∨ (d.strstart ≥ d.w_size + (d.w_size - MIN_LOOKAHEAD_u) ∧ base = slideState d)) ∧
    result = fillResult base result
  consumed : z'.avail_in.toNat + result.lookahead.toNat = z.avail_in.toNat + d.lookahead.toNat
  stream : z' = z ∨ ∃ n ref io ia, z.next_in = .ref ref io ∧ Space.get h ref = some ia ∧
    io + n.toNat ≤ ia.size ∧ n.toNat ≤ z.avail_in.toNat ∧
    z' = readStream z n ref io (checksumValue d.wrap z.adler ((ia.toList.drop io).take n.toNat))
  byteFrame : ByteFrame h after (DeflateOwned ds d)
  outside : ∀ w b, d.window = .ref (.blk w) 0 → b ≠ w → after.bytes b = h.bytes b
  shape : Shape h after
  frame : Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b)
  live : LiveChange h after (fun _ => False) (fun _ => False)
  nalloc : after.nalloc = h.nalloc
  nextBlk : after.nextBlk = h.nextBlk

theorem slide_state_owned (ds : Nat) (d : DeflateState) : DeflateOwned ds (slideState d) = DeflateOwned ds d := rfl

theorem padded_state_owned (ds : Nat) (d : DeflateState) : DeflateOwned ds (paddedState d) = DeflateOwned ds d := rfl

/-- The slide prefix from `FillPre`: the slid state satisfies `FillPre` again, with its frame. -/
theorem fill_slide_pre {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (pre : FillPre roll h r ds z d) (blockLow : -(2 : Int) ^ 62 ≤ d.block_start.toInt)
    (taken : d.strstart ≥ d.w_size + (d.w_size - MIN_LOOKAHEAD_u)) :
    ∃ w p q wa pa qa pa' qa', HashEnv h d w q p wa qa pa ∧ pa'.size = pa.size ∧ qa'.size = qa.size ∧
      fillSlide (some (.tab ds)) d d.w_size (fillMore d) h = .ok ((), slideHeap h ds w p q d wa pa' qa') ∧
      FillPre roll (slideHeap h ds w p q d wa pa' qa') r ds z (slideState d) := by
  obtain ⟨w, p, q, wa, pa, qa, env, chains⟩ := heap_chains_environment pre.good pre.chains
  obtain ⟨qa', pa', run, sizeH, sizeP, head, prev⟩ := fill_slide_run_any pre.good env
    (block_start_slide_signed pre.good blockLow) pre.range taken
  let hs := slideHeap h ds w p q d wa pa' qa'
  let slid := slideState d
  have goodS : DGood hs r ds z slid := slide_good pre.good env sizeP sizeH
  have geometry := fill_slide_counts pre.good env.win env.wbytes pre.range taken
  have insertCount : slid.insert.toNat = min d.insert.toNat slid.strstart.toNat := slide_insert_count d
  have frontierEq : slid.strstart.toNat - slid.insert.toNat =
      (d.strstart.toNat - d.insert.toNat) - d.w_size.toNat := by
    have start := geometry.2.2.2.2.1
    have pending := pre.pending
    change slid.strstart.toNat = _ at start
    omega
  have frontierS : HeapChains hs slid (slid.strstart.toNat - slid.insert.toNat) := by
    rw [frontierEq]
    exact slide_heap_chains pre.good env chains pre.range taken head prev
  have rangeS : fillEnd slid ≤ slid.window_size.toNat := by
    change fillEnd (slideState d) ≤ d.window_size.toNat
    have wsz := pre.good.inv.wsz
    omega
  refine ⟨w, p, q, wa, pa, qa, pa', qa', env, sizeP, sizeH, run, ⟨goodS, frontierS, ?_, rangeS, ?_, ?_⟩⟩
  · change slid.insert.toNat ≤ slid.strstart.toNat
    omega
  · intro large
    have large' : 3 ≤ d.lookahead.toNat := large
    obtain ⟨zero, rolled⟩ := pre.form large'
    refine ⟨?_, fun yes => ?_⟩
    · have small : ¬ d.insert > d.strstart - d.w_size := by
        simp [zero, UInt32.lt_iff_toNat_lt]
      simp [slid, slideState, slideBeforeHash, small, zero]
    · obtain ⟨w0, wa0, win0, get0, form⟩ := rolled yes
      have wid : w0 = w := by simpa only [env.win, Ptr.ref.injEq, BRef.blk.injEq, and_true] using win0.symm
      subst w0
      have aid : wa0 = wa := Option.some.inj (get0.symm.trans env.wbytes)
      subst wa0
      exact ⟨w, slideWindow d wa, env.win, by simp [slideHeap],
        slide_form pre.good env.win env.wbytes pre.range taken large' form⟩
  · intro two
    obtain ⟨t1, t2⟩ := pre.globals two
    exact ⟨by simpa [hs, slideHeap, setD, setW] using t1, by simpa [hs, slideHeap, setD, setW] using t2⟩


theorem fill_result_of_eq {d result : DeflateState} {L : UInt32}
    (e : result = { d with
      lookahead := L
      ins_h := result.ins_h
      insert := result.insert
      high_water := result.high_water }) : result = fillResult d result := by
  have hl : result.lookahead = L := by rw [e]
  calc result = { d with
        lookahead := L
        ins_h := result.ins_h
        insert := result.insert
        high_water := result.high_water } := e
    _ = fillResult d result := by simp only [fillResult, hl]

theorem fill_window_window {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (pre : FillPre roll h r ds z d) : ∃ w wa, d.window = .ref (.blk w) 0 ∧ h.bytes w = some wa := by
  obtain ⟨w, p, q, wa, pa, qa, env, _⟩ := heap_chains_environment pre.good pre.chains
  exact ⟨w, wa, env.win, env.wbytes⟩

/-- Empty caller input and no slide: only the high-water padding. -/
theorem fill_window_empty_post {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (pre : FillPre roll h r ds z d) (empty : z.avail_in = 0)
    (noSlide : ¬ d.strstart ≥ d.w_size + (d.w_size - MIN_LOOKAHEAD_u)) :
    ∃ after result, fill_window (some (.tab ds)) h = .ok ((), after) ∧ FillPost roll h after r ds z z d result := by
  obtain ⟨w, wa, win, get⟩ := fill_window_window pre
  obtain ⟨run, byteFrame⟩ := fill_window_empty_storage pre.good win get pre.range empty noSlide
  obtain ⟨shape, frame, live, alloc, next⟩ := padded_heap_full_storage pre.good win get
  refine ⟨_, paddedState d, run, ⟨padded_good pre.good win get pre.range,
    padded_chains pre.good pre.chains win get pre.range, pre.pending, pre.range, ?_, Or.inr empty, noSlide,
    ⟨d, Or.inl rfl, rfl⟩, rfl, Or.inl rfl, byteFrame, ?_, shape, frame, live, alloc, next⟩⟩
  · intro large
    obtain ⟨zero, rolled⟩ := pre.form large
    refine ⟨zero, fun yes => ?_⟩
    obtain ⟨w0, wa0, win0, get0, form⟩ := rolled yes
    have wid : w0 = w := by simpa only [win, Ptr.ref.injEq, BRef.blk.injEq, and_true] using win0.symm
    subst w0
    have aid : wa0 = wa := Option.some.inj (get0.symm.trans get)
    subst wa0
    exact ⟨w, _, win, by simp [paddedHeap], padded_form pre.good win get pre.range large form⟩
  · intro w0 b win0 other
    have wid : w0 = w := by simpa only [win, Ptr.ref.injEq, BRef.blk.injEq, and_true] using win0.symm
    subst w0
    simp [paddedHeap, upd_ne _ _ _ _ other]

set_option maxHeartbeats 1600000 in
/-- New caller input and no slide: the read, the pending insertions and the padding. -/
theorem fill_window_read_post {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    {ref : BRef} {io : Nat} {ia : Array UInt8}
    (pre : FillPre roll h r ds z d) (short : d.lookahead.toNat < 262)
    (nonempty : z.avail_in ≠ 0) (pointer : z.next_in = .ref ref io) (data : Space.get h ref = some ia)
    (inputBound : io + z.avail_in.toNat ≤ ia.size)
    (separated : ∀ w, d.window = .ref (.blk w) 0 → BRef.blk w ≠ ref)
    (noSlide : ¬ d.strstart ≥ d.w_size + (d.w_size - MIN_LOOKAHEAD_u)) :
    ∃ after z' result, fill_window (some (.tab ds)) h = .ok ((), after) ∧ FillPost roll h after r ds z z' d result := by
  obtain ⟨w, wa, win, get⟩ := fill_window_window pre
  have separate := separated w win
  obtain ⟨after, result, output, run, goodA, chainsA, winA, getA, rangeA, _initialized, formA, fields,
      countA, outside, _prefix, stopped, byteFrame, shape, frame, live, alloc, next⟩ :=
    fill_window_pending_complete_full_storage_any pre.good pre.chains pre.pending win get pre.range short noSlide
      pre.globals pointer data inputBound nonempty separate
  have counts := resume_read_counts pre.good win get pre.range
  have nCount : (rbLen z.avail_in (fillMore d)).toNat = min z.avail_in.toNat (fillMore d).toNat := rbLen_nat _ _
  have look : result.lookahead.toNat = d.lookahead.toNat + (rbLen z.avail_in (fillMore d)).toNat := by
    rw [fields]; exact counts.2.1
  have startEq : result.strstart = d.strstart := by rw [fields]
  have sizesEq : result.w_size = d.w_size := by rw [fields]
  refine ⟨after, _, result, run, ⟨goodA, chainsA, ?_, rangeA, ?_, stopped, ?_, ⟨d, Or.inl rfl,
    fill_result_of_eq fields⟩, ?_, Or.inr ⟨_, ref, io, ia, pointer, data, by omega, by omega, rfl⟩,
    byteFrame, ?_, shape, frame, live, alloc, next⟩⟩
  · rw [startEq]
    have := pre.pending
    omega
  · intro large
    obtain ⟨zero, form⟩ := formA large
    exact ⟨zero, fun _ => ⟨w, output, winA, getA, form⟩⟩
  · rw [startEq, sizesEq]; exact noSlide
  · change (z.avail_in - rbLen z.avail_in (fillMore d)).toNat + result.lookahead.toNat = _
    rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by omega)), look]
    omega
  · intro w0 b win0 other
    have wid : w0 = w := by simpa only [win, Ptr.ref.injEq, BRef.blk.injEq, and_true] using win0.symm
    subst w0
    exact outside b other

/-- A slide followed by a call that does not slide composes into the whole call. -/
theorem fill_post_after_slide {h hs after : Heap} {r : ZStreamRef} {ds w p q : Nat} {z z' : ZStream}
    {d result : DeflateState} {wa : Array UInt8} {pa qa pa' qa' : Array UInt16}
    (pre : FillPre roll h r ds z d) (env : HashEnv h d w q p wa qa pa)
    (taken : d.strstart ≥ d.w_size + (d.w_size - MIN_LOOKAHEAD_u))
    (heap : hs = slideHeap h ds w p q d wa pa' qa') (buffers : StreamBuffers h r)
    (post : FillPost roll hs after r ds z z' (slideState d) result) : FillPost roll h after r ds z z' d result := by
  subst hs
  have geometry := fill_slide_counts pre.good env.win env.wbytes pre.range taken
  obtain ⟨shapeS, frameS, _liveS, allocS, nextS⟩ :=
    slide_heap_full_storage pre.good env.win env.prevp env.headp env.wbytes env.pwords env.hwords pa' qa'
  have shape := shapeS.trans post.shape
  have slideFrame : ByteFrame h (slideHeap h ds w p q d wa pa' qa') (DeflateOwned ds d) :=
    slide_storage_frame h ds w p q d wa pa' qa' _ (Or.inl rfl) (Or.inr (Or.inl env.win))
  refine ⟨post.good, post.chains, post.pending, post.range, post.form, post.stopped, post.noSlide, ?_,
    post.consumed, ?_, slideFrame.trans post.byteFrame, ?_, shape, full_frame_trans_shape frameS post.frame shapeS, full_shape_live_change shape,
    post.nalloc.trans allocS, post.nextBlk.trans nextS⟩
  · obtain ⟨base, choice, eq⟩ := post.fields
    rcases choice with same | ⟨again, _⟩
    · exact ⟨base, Or.inr ⟨taken, same⟩, eq⟩
    · exact False.elim (geometry.2.2.2.2.2.2.2.2 again)
  · rcases post.stream with same | ⟨n, ref, io, ia, pointer, data, bound, count, value⟩
    · exact Or.inl same
    · have separate := caller_input_window_separate pre.good buffers env.win pointer
      refine Or.inr ⟨n, ref, io, ia, pointer, ?_, bound, count, value⟩
      rw [← slide_input_frame pre.good separate]
      exact data
  · intro w0 b win0 other
    have wid : w0 = w := by simpa only [env.win, Ptr.ref.injEq, BRef.blk.injEq, and_true] using win0.symm
    subst w0
    rw [post.outside w b env.win other]
    simp [slideHeap, setD, setW, upd_ne _ _ _ _ other]

/-- `fill_window` for every parameter tuple, every wrapper, both slide choices, empty or new
input, and every pending-insertion count. -/
theorem fill_window_any {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (pre : FillPre roll h r ds z d) (blockLow : -(2 : Int) ^ 62 ≤ d.block_start.toInt)
    (short : d.lookahead.toNat < 262) (buffers : StreamBuffers h r)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null) :
    ∃ after z' result, fill_window (some (.tab ds)) h = .ok ((), after) ∧ FillPost roll h after r ds z z' d result := by
  by_cases taken : d.strstart ≥ d.w_size + (d.w_size - MIN_LOOKAHEAD_u)
  · obtain ⟨w, p, q, wa, pa, qa, pa', qa', env, sizeP, sizeH, prefixRun, preS⟩ := fill_slide_pre pre blockLow taken
    have geometry := fill_slide_counts pre.good env.win env.wbytes pre.range taken
    have transfer := fill_window_slide_transfer pre.good env sizeP sizeH pre.range taken prefixRun
    have shortS : (slideState d).lookahead.toNat < 262 := short
    by_cases empty : z.avail_in = 0
    · obtain ⟨after, result, run, post⟩ := fill_window_empty_post preS empty geometry.2.2.2.2.2.2.2.2
      exact ⟨after, z, result, transfer.trans run, fill_post_after_slide pre env taken rfl buffers post⟩
    · obtain ⟨ref, io, pointer⟩ : ∃ ref io, z.next_in = .ref ref io := by
        cases pointer : z.next_in with
        | null => exact False.elim (inputValid empty pointer)
        | ref ref io => exact ⟨ref, io, rfl⟩
      obtain ⟨ia, data, inputBound⟩ := caller_input_array pre.good buffers pointer
      have separate := caller_input_window_separate pre.good buffers env.win pointer
      have dataS : Space.get (slideHeap h ds w p q d wa pa' qa') ref = some ia := by
        rw [slide_input_frame pre.good separate]; exact data
      obtain ⟨after, z', result, run, post⟩ := fill_window_read_post preS shortS empty pointer dataS inputBound
        (fun _ win => caller_input_window_separate pre.good buffers win pointer) geometry.2.2.2.2.2.2.2.2
      exact ⟨after, z', result, transfer.trans run, fill_post_after_slide pre env taken rfl buffers post⟩
  · by_cases empty : z.avail_in = 0
    · obtain ⟨after, result, run, post⟩ := fill_window_empty_post pre empty taken
      exact ⟨after, z, result, run, post⟩
    · obtain ⟨ref, io, pointer⟩ : ∃ ref io, z.next_in = .ref ref io := by
        cases pointer : z.next_in with
        | null => exact False.elim (inputValid empty pointer)
        | ref ref io => exact ⟨ref, io, rfl⟩
      obtain ⟨ia, data, inputBound⟩ := caller_input_array pre.good buffers pointer
      exact fill_window_read_post pre short empty pointer data inputBound
        (fun _ win => caller_input_window_separate pre.good buffers win pointer) taken


theorem stream_accounting_self (z : ZStream) : StreamAccounting z z 0 0 := by
  unfold StreamAccounting
  refine ⟨Nat.zero_le _, Nat.zero_le _, by omega, by omega, ?_, ?_, rfl, rfl, rfl, rfl, rfl⟩ <;>
    exact (advance_zero _).symm

/-- The input `fill_window` consumed, as stream accounting. -/
theorem FillPost.account {h after : Heap} {r : ZStreamRef} {ds : Nat} {z z' : ZStream} {d result : DeflateState}
    (post : FillPost roll h after r ds z z' d result) :
    ∃ used, StreamAccounting z z' used 0 ∧ result.lookahead.toNat = d.lookahead.toNat + used := by
  rcases post.stream with same | ⟨n, ref, io, ia, pointer, data, bound, count, value⟩
  · subst same
    exact ⟨0, stream_accounting_self z', by have := post.consumed; omega⟩
  · have account := read_stream_accounting z n ref io
      (checksumValue d.wrap z.adler ((ia.toList.drop io).take n.toNat)) pointer count
    rw [← value] at account
    exact ⟨n.toNat, account, by have := post.consumed; have := account.2.2.1; omega⟩

/-- The window, hash and pending blocks are those of the state before the call. -/
theorem FillPost.keys {h after : Heap} {r : ZStreamRef} {ds : Nat} {z z' : ZStream} {d result : DeflateState}
    (post : FillPost roll h after r ds z z' d result) :
    result.window = d.window ∧ result.prev = d.prev ∧ result.head = d.head ∧
      result.pending_buf = d.pending_buf := by
  obtain ⟨base, choice, eq⟩ := post.fields
  rcases choice with same | ⟨_, same⟩ <;> subst same <;> rw [eq] <;> exact ⟨rfl, rfl, rfl, rfl⟩

/-- The caller's buffers are available again after `fill_window`. -/
theorem fill_window_buffers {h after : Heap} {r : ZStreamRef} {ds : Nat} {z z' : ZStream} {d result : DeflateState}
    (pre : FillPre roll h r ds z d) (buffers : StreamBuffers h r)
    (run : fill_window (some (.tab ds)) h = .ok ((), after))
    (post : FillPost roll h after r ds z z' d result) : StreamBuffers after r := by
  obtain ⟨used, account⟩ := post.account
  obtain ⟨win, prev, head, pend⟩ := post.keys
  have owned := stream_owned_keys pre.good post.good win prev head pend
  exact stream_buffers_private_read pre.good.live.hz post.good.live.hz buffers post.byteFrame
    (fun b mine => (stream_owned_deflate pre.good b).mpr mine) owned account.1
    (Zlib.Deflate.BorrowProofs.stable_fill_window _ _ _ _ run)


set_option maxHeartbeats 4000000 in
/-- The fields `fill_window` leaves as they are. -/
theorem FillPost.same {h after : Heap} {r : ZStreamRef} {ds : Nat} {z z' : ZStream} {d result : DeflateState}
    (post : FillPost roll h after r ds z z' d result) :
    result.level = d.level ∧ result.strategy = d.strategy ∧ result.w_size = d.w_size ∧
    result.window_size = d.window_size ∧ result.match_length = d.match_length ∧
    result.match_available = d.match_available ∧ result.prev_length = d.prev_length ∧
    result.sym_next = d.sym_next ∧ result.sym_end = d.sym_end ∧ result.lit_bufsize = d.lit_bufsize ∧
    result.dyn_ltree = d.dyn_ltree ∧ result.dyn_dtree = d.dyn_dtree ∧ result.bl_tree = d.bl_tree ∧
    result.opt_len = d.opt_len ∧ result.static_len = d.static_len ∧ result.pending = d.pending ∧
    result.pending_out = d.pending_out ∧ result.pending_buf = d.pending_buf ∧
    result.last_flush = d.last_flush ∧ result.wrap = d.wrap ∧ result.status = d.status ∧
    result.bi_valid = d.bi_valid ∧ result.«matches» = d.«matches» := by
  obtain ⟨base, choice, eq⟩ := post.fields
  rcases choice with same | ⟨_, same⟩ <;> subst same <;>
    exact ⟨(congrArg DeflateState.level eq).trans rfl, (congrArg DeflateState.strategy eq).trans rfl, (congrArg DeflateState.w_size eq).trans rfl, (congrArg DeflateState.window_size eq).trans rfl, (congrArg DeflateState.match_length eq).trans rfl, (congrArg DeflateState.match_available eq).trans rfl, (congrArg DeflateState.prev_length eq).trans rfl, (congrArg DeflateState.sym_next eq).trans rfl, (congrArg DeflateState.sym_end eq).trans rfl, (congrArg DeflateState.lit_bufsize eq).trans rfl, (congrArg DeflateState.dyn_ltree eq).trans rfl, (congrArg DeflateState.dyn_dtree eq).trans rfl, (congrArg DeflateState.bl_tree eq).trans rfl, (congrArg DeflateState.opt_len eq).trans rfl, (congrArg DeflateState.static_len eq).trans rfl, (congrArg DeflateState.pending eq).trans rfl, (congrArg DeflateState.pending_out eq).trans rfl, (congrArg DeflateState.pending_buf eq).trans rfl, (congrArg DeflateState.last_flush eq).trans rfl, (congrArg DeflateState.wrap eq).trans rfl, (congrArg DeflateState.status eq).trans rfl, (congrArg DeflateState.bi_valid eq).trans rfl, (congrArg DeflateState.«matches» eq).trans rfl⟩

/-- The position fields: unchanged, or slid by one window. -/
theorem FillPost.position {h after : Heap} {r : ZStreamRef} {ds : Nat} {z z' : ZStream} {d result : DeflateState}
    (post : FillPost roll h after r ds z z' d result) :
    (result.strstart = d.strstart ∧ result.match_start = d.match_start ∧ result.block_start = d.block_start) ∨
    (d.strstart ≥ d.w_size + (d.w_size - MIN_LOOKAHEAD_u) ∧ result.strstart = d.strstart - d.w_size ∧
      result.match_start = d.match_start - d.w_size ∧
      result.block_start = Int64.ofInt (d.block_start.toInt - (d.w_size.toNat : Int))) := by
  obtain ⟨base, choice, eq⟩ := post.fields
  rcases choice with same | ⟨taken, same⟩ <;> subst same <;> rw [eq]
  · exact Or.inl ⟨rfl, rfl, rfl⟩
  · exact Or.inr ⟨taken, rfl, rfl, rfl⟩

end Zlib.Deflate.Engine.Proofs

namespace Zlib.Deflate.Universal
open C ZlibF.Spec ZlibF.Spec.Public Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Engine.Proofs
open Zlib.Deflate.Proofs
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

theorem crc_globals_of_library {h : Heap} (globals : LibraryGlobals h) : CrcGlobals h := by
  unfold LibraryGlobals at globals
  exact ⟨by rw [globals]; rfl, by rw [globals]; rfl⟩

/-- The block start is far above the `long` range at a nonzero level. -/
theorem block_start_low {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) (level : d.level ≠ 0) : -(2 : Int) ^ 62 ≤ d.block_start.toInt := by
  have span := inv.shape.blockSpan level
  have room := inv.shape.symRoom
  have endEq := inv.good.inv.sym.2.1
  have lit := inv.good.inv.lit
  have hsize := inv.good.inv.hsize
  have bits := inv.good.inv.hbits_hi
  have pow : 2 ^ d.hash_bits.toNat ≤ 2 ^ 16 := Nat.pow_le_pow_right (by decide) bits
  have avail : d.match_available.toInt ≤ 1 := by
    rcases inv.shape.matchAvailable with e | e <;> rw [e] <;> decide
  have : (2 : Int) ^ 62 = 4611686018427387904 := rfl
  have p16 : (2 : Nat) ^ 16 = 65536 := rfl
  omega

/-- The premise of `fill_window_any` from the invariant at a nonzero level. The rolling hash is
required where `Hashing.rolling` gives it. -/
theorem DInv.fillPre {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) (level : d.level ≠ 0) :
    FillPre (d.strategy.toInt ≠ 2 ∧ d.strategy.toInt ≠ 3) h r ds z d :=
  ⟨inv.good, inv.chains level, inv.shape.insert, inv.shape.room,
    fun large => ⟨inv.shape.insertDone large, fun roll => inv.hashing.rolling roll.1 roll.2 large⟩,
    fun _ => crc_globals_of_library inv.globals⟩

set_option maxHeartbeats 1600000 in
/-- **`fill_window` keeps the invariant** at a nonzero level (the strategies other than
`deflate_stored`), for every parameter tuple, wrapper, slide choice and input. -/
theorem fill_window_inv {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) (level : d.level ≠ 0) (buffers : StreamBuffers h r)
    (input : z.avail_in ≠ 0 → z.next_in ≠ .null) (short : d.lookahead.toNat < 262) :
    ∃ after z' d', C.run (Zlib.Deflate.fill_window (some (.tab ds))) h = .ok ((), after) ∧
      DInv after r ds z' d' ∧ StreamBuffers after r ∧
      FillPost (d.strategy.toInt ≠ 2 ∧ d.strategy.toInt ≠ 3) h after r ds z z' d d' := by
  have pre := inv.fillPre level
  obtain ⟨after, z', d', run, post⟩ := fill_window_any pre (block_start_low inv level) short buffers input
  have buffersA := fill_window_buffers pre buffers run post
  obtain ⟨used, account, look⟩ := post.account
  obtain ⟨sLevel, sStrategy, sWsize, sWindow, sMatchLength, sAvailable, sPrevLength, sSymNext, sSymEnd,
    sLit, sLtree, sDtree, sBl, sOpt, sStatic, sPending, sPendingOut, sPendingBuf, sLastFlush, sWrap,
    sStatus, sBiValid, sMatches⟩ := post.same
  have ws := slide_window_sizes inv.good
  have wsz := inv.good.inv.wsz
  have shape := inv.shape
  have position : (d'.strstart.toNat = d.strstart.toNat ∧ d'.block_start.toInt = d.block_start.toInt ∧
      d'.strstart - 1 - d'.match_start = d.strstart - 1 - d.match_start) ∨
      (d'.strstart.toNat = d.strstart.toNat - d.w_size.toNat ∧ d.w_size.toNat + 250 ≤ d.strstart.toNat ∧
        d'.block_start.toInt = d.block_start.toInt - d.w_size.toNat ∧
        d'.strstart - 1 - d'.match_start = d.strstart - 1 - d.match_start) := by
    rcases post.position with ⟨e1, e2, e3⟩ | ⟨taken, e1, e2, e3⟩
    · exact Or.inl ⟨by rw [e1], by rw [e3], by rw [e1, e2]⟩
    · have threshold := slide_threshold inv.good
      rw [GE.ge, UInt32.le_iff_toNat_le, threshold] at taken
      have low := block_start_low inv level
      have high := Int64.toInt_lt d.block_start
      refine Or.inr ⟨by rw [e1, UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by omega))],
        by omega, ?_, by rw [e1, e2]; grind⟩
      rw [e3, Int64.toInt_ofInt]
      have p62 : (2 : Int) ^ 62 = 4611686018427387904 := rfl
      have p63 : (2 : Int) ^ 63 = 9223372036854775808 := rfl
      exact Int.bmod_eq_of_le (by change -9223372036854775808 ≤ _; omega)
        (by change _ < 9223372036854775808; omega)
  have shapeA : Shape d' := by
    refine ⟨post.range, post.pending, fun large => (post.form large).1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [sPrevLength]; exact shape.prevLength
    · rw [sMatchLength]; exact shape.matchLength
    · rw [sAvailable]; exact shape.matchAvailable
    · have := shape.blockStart
      rcases position with ⟨e1, e2, _⟩ | ⟨e1, big, e2, _⟩ <;> rw [e2, e1] <;> omega
    · intro levelA
      have span := shape.blockSpan level
      rw [sSymNext, sAvailable]
      rcases position with ⟨e1, e2, _⟩ | ⟨e1, big, e2, _⟩ <;> rw [e2, e1] <;> omega
    · intro zero; rw [sLevel] at zero; exact absurd zero level
    · intro avail
      rw [sAvailable] at avail
      have := shape.available avail
      rcases position with ⟨e1, _, _⟩ | ⟨e1, big, _, _⟩ <;> rw [e1] <;> omega
    · intro large
      rw [sMatchLength] at large ⊢
      obtain ⟨a, b, c⟩ := shape.pendingMatch large
      have dist : d'.strstart - 1 - d'.match_start = d.strstart - 1 - d.match_start := by
        rcases position with ⟨_, _, e⟩ | ⟨_, _, _, e⟩ <;> exact e
      rw [dist, sWsize]
      exact ⟨a, b, by omega⟩
    · rw [sLevel, sStrategy, sMatchLength, sPrevLength]; exact shape.fastLazy
    · exact post.good.inv.hw
    · rw [sLastFlush]; exact shape.lastFlush
    · rw [sWrap, sStatus]; exact shape.trailer
    · rw [sBiValid]; exact shape.biValid
    · rw [sPending, sPendingOut, sPendingBuf]; exact shape.cursor
    · rw [sSymNext, sSymEnd]; exact shape.symRoom
    · rw [sMatches, sLevel]; exact shape.slides
  have zeroMatches : d.«matches» = 0 := shape.slides.2 level
  refine ⟨after, z', d', run, ⟨post.good, ?_, ?_, shapeA, ?_, ?_⟩, buffersA, post⟩
  · have z1 := account.2.2.2.2.2.2.2.1
    have z2 := account.2.2.2.2.2.2.2.2.1
    exact ⟨z1.trans inv.alloc.1, z2.trans inv.alloc.2⟩
  · unfold LibraryGlobals
    rw [post.byteFrame.static]
    exact inv.globals
  · refine ⟨fun _ => post.chains, fun one => ?_, fun s2 s3 large => ?_⟩
    · rw [sMatches, zeroMatches] at one; cases one
    · rw [sStrategy] at s2 s3
      exact (post.form large).2 ⟨s2, s3⟩
  · obtain ⟨xs, ⟨b, a, pbuf, get, ledger⟩, dist⟩ := inv.symbols.recorded
    obtain ⟨w, wa, win, _⟩ := fill_window_window pre
    have different : b ≠ w := by
      obtain ⟨w0, p0, q0, b0, blocks⟩ := inv.good.inv.blocks
      have we : w0 = w := by simpa only [win, Ptr.ref.injEq, BRef.blk.injEq, and_true] using blocks.win.symm
      have be : b0 = b := by simpa only [pbuf, Ptr.ref.injEq, BRef.blk.injEq, and_true] using blocks.pbuf.symm
      subst w0 b0
      exact blocks.wb.symm
    refine ⟨⟨xs, ⟨b, a, by rw [sPendingBuf]; exact pbuf, by rw [post.outside w b win different]; exact get,
      ledger.keep sSymNext sLit sLtree sDtree⟩, by rw [sWsize]; exact dist⟩, ?_, ?_⟩
    · have clear := inv.symbols.clear
      exact ⟨fun k hk => by rw [sBl]; exact clear.bl k hk, by rw [sOpt]; exact clear.opt,
        by rw [sStatic]; exact clear.fixed⟩
    · intro b0 off pout nonzero
      rw [sPendingOut] at pout
      rw [sSymNext] at nonzero
      rw [sPending, sLit]
      exact inv.symbols.below b0 off pout nonzero


/-- **`longest_match` inside the strategies** (the corrected `longest_match_spec`): right after
`INSERT_STRING` at `strstart` returned `cur` (`Inserted`), with a chain head the strategies pass
(`1 ≤ cur < strstart`, within `MAX_DIST`) and matcher room, the call does not fault and
terminates for every tuning value; only `match_start` changes; the result is
`min (best, lookahead)` with `prev_length ≤ best ≤ 258`, and an improved `best` is a real match. -/
theorem longest_match_inserted {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    {cur : UInt32} (good : DGood h r ds z d) (inserted : Inserted h d cur.toNat)
    (head : 1 ≤ cur.toNat) (below : cur.toNat < d.strstart.toNat)
    (near : d.strstart.toNat - cur.toNat ≤ d.w_size.toNat - 262)
    (range : d.strstart.toNat + d.lookahead.toNat ≤ d.window_size.toNat)
    (room : d.strstart.toNat + 262 ≤ d.window_size.toNat) (previous : d.prev_length.toNat ≤ 258) :
    ∃ (len ms : UInt32) (best : Nat),
      C.run (Zlib.Deflate.longest_match (some (.tab ds)) cur) h = .ok (len, hAt h ds d ms) ∧
      len = UInt32.ofNat (lmResult best d.lookahead.toNat) ∧
      d.prev_length.toNat ≤ best ∧ best ≤ 258 ∧
      (∃ wa, (∃ w, d.window = .ref (.blk w) 0 ∧ h.bytes w = some wa) ∧
        ((best = d.prev_length.toNat ∧ ms = d.match_start) ∨
          (d.prev_length.toNat < best ∧ GoodMatch wa d.strstart.toNat d.w_size.toNat ms.toNat best))) ∧
      DGood (hAt h ds d ms) r ds z { d with match_start := ms } ∧
      HeapChains (hAt h ds d ms) { d with match_start := ms } (d.strstart.toNat + 1) := by
  obtain ⟨heapChains, w, p, q, wa, pa, qa, win, prev, headp, hw, hp, hq, published, link⟩ := inserted
  obtain ⟨w0, p0, q0, wa0, pa0, qa0, win0, prev0, head0, hw0, hp0, hq0, H⟩ := heapChains
  have we : w0 = w := by simpa only [win, Ptr.ref.injEq, BRef.blk.injEq, and_true] using win0.symm
  have pe : p0 = p := by simpa only [prev, Ptr.ref.injEq, WRef.blk.injEq, and_true] using prev0.symm
  have qe : q0 = q := by simpa only [headp, Ptr.ref.injEq, WRef.blk.injEq, and_true] using head0.symm
  subst w0 p0 q0
  have ae : wa0 = wa := Option.some.inj (hw0.symm.trans hw)
  have pae : pa0 = pa := Option.some.inj (hp0.symm.trans hp)
  have qae : qa0 = qa := Option.some.inj (hq0.symm.trans hq)
  subst wa0 pa0 qa0
  have keyBound := hkey_lt (hash_parameters good.inv) (bfn wa) d.strstart.toNat
  obtain ⟨len, ms, best, run, result, lower, upper, matching, goodA, chainsA⟩ :=
    longest_match_chains_room good ⟨w, p, q, wa, pa, qa, win, prev, headp, hw, hp, hq, H⟩ win prev headp
      hw hp hq H rfl keyBound published link head below near range room previous
  exact ⟨len, ms, best, run, result, lower, upper, ⟨wa, ⟨w, win, hw⟩, matching⟩, goodA, chainsA⟩

end Zlib.Deflate.Universal

namespace Zlib.Deflate.Engine.Proofs
end Zlib.Deflate.Engine.Proofs
