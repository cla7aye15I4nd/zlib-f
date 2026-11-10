import ZlibF.Proof.«deflate.c.engine.fill-read-resume»
import ZlibF.Proof.«deflate.c.gzip-read-zero»

/-! Actual CRC2 resumed input read. This internal no-slide endpoint retains the
original window, source bounds and insert-zero premises. It is not a whole
fill_window contract or a canonical-seed gzip history theorem. -/
namespace Zlib.Deflate.Engine.Proofs.DefaultGzipProofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Engine.Proofs
set_option autoImplicit false

theorem crc_statics_of_library_globals {h : Heap} (globals : LibraryGlobals h) :
    Zlib.Crc32.Proofs.StaticsOK h := by
  unfold Zlib.Crc32.Proofs.StaticsOK
  rw [globals]
  exact ⟨rfl,rfl⟩

/-- Positive-count read value. Zero-count early return is handled separately;
this expression must not be substituted for an arbitrary 64-bit zero-count seed. -/
def gzipReadValue (z : ZStream) (n : UInt32) (ia : Array UInt8) (io : Nat) : UInt64 :=
  (ZlibF.Spec.crc32Update z.adler.toUInt32 ((ia.toList.drop io).take n.toNat)).toUInt64

def resumeReadGzipHeap (h : Heap) (r : ZStreamRef) (ds w : Nat) (z : ZStream) (d : DeflateState)
    (ref : BRef) (io : Nat) (ia wa : Array UInt8) : Heap :=
  let n := rbLen z.avail_in (fillMore d)
  let copied := copyRange wa ia (fillEnd d) io n.toNat
  let z' := readStream z n ref io (gzipReadValue z n ia io)
  setD (r.put { h with bytes := upd h.bytes w (some copied) } z') ds (resumeReadState d n copied)

set_option maxHeartbeats 1000000 in
/-- One actual fill body with old buffered data, new input and no slide.
The input count stays arbitrary and is clamped only by real window room.
The complete checksum/cursor update and source re-priming are executed.
-/
theorem fill_body_resume_read_gzip {h : Heap} {r : ZStreamRef} {ds w io : Nat}
    {z : ZStream} {d : DeflateState} {ref : BRef} {ia wa : Array UInt8}
    (good : DGood h r ds z d) (win : d.window = .ref (.blk w) 0)
    (get : h.bytes w = some wa) (writable : h.ro w = false)
    (range : fillEnd d ≤ d.window_size.toNat) (short : d.lookahead.toNat < 262)
    (noSlide : ¬ d.strstart ≥ d.w_size + (d.w_size - MIN_LOOKAHEAD_u))
    (insert : d.insert = 0) (wrap : d.wrap = 2) (globals : LibraryGlobals h)
    (pointer : z.next_in = .ref ref io) (input : Space.get h ref = some ia)
    (inputBound : io + z.avail_in.toNat ≤ ia.size) (nonempty : z.avail_in ≠ 0)
    (separate : BRef.blk w ≠ ref ∨ fillEnd d + (rbLen z.avail_in (fillMore d)).toNat ≤ io ∨
      io + (rbLen z.avail_in (fillMore d)).toNat ≤ fillEnd d) :
    fillBody (some (.tab ds)) d.w_size false h =
      .ok (false, resumeReadGzipHeap h r ds w z d ref io ia wa) := by
  let n := rbLen z.avail_in (fillMore d)
  let copied := copyRange wa ia (fillEnd d) io n.toNat
  let z' := readStream z n ref io (gzipReadValue z n ia io)
  let hr := r.put { h with bytes := upd h.bytes w (some copied) } z'
  let dr := { d with lookahead := d.lookahead + n }
  let hl := setD hr ds dr
  have counts := resume_read_counts good win get range
  have room := fill_room_no_slide good win get range short noSlide
  have extent := window_extent good win get
  have availPositive : 0 < z.avail_in.toNat := by
    have ne : z.avail_in.toNat ≠ 0 := by intro eq; exact nonempty (UInt32.toNat_inj.mp eq)
    omega
  have count : n.toNat = min z.avail_in.toNat (fillMore d).toNat := rbLen_nat _ _
  have nonzero : n ≠ 0 := by
    intro zero
    have num : n.toNat = 0 := by rw [zero]; rfl
    omega
  have windowBound : fillEnd d + n.toNat ≤ wa.size := by
    rw [extent.1]
    have more : (fillMore d).toNat = d.window_size.toNat - fillEnd d := fill_more_nat good win get range
    omega
  have read := read_buf_gzip (bo := fillEnd d) good.live.hz good.live.zst good.live.hs wrap (crc_statics_of_library_globals globals) pointer input
    get writable (fillMore d) nonzero (by omega) windowBound separate
  have first : padd d.window d.strstart.toNat h = .ok (.ref (.blk w) d.strstart.toNat, h) := by
    rw [win]
    simpa only [OkOn, padd, Nat.zero_add] using Ptr.add_nat_ok (off := 0) (n := d.strstart.toNat)
      (show Space.get h (BRef.blk w) = some wa from get) (by dsimp only [fillEnd] at range; omega)
  have second : padd (.ref (.blk w) d.strstart.toNat : BPtr) d.lookahead.toNat h =
      .ok (.ref (.blk w) (fillEnd d), h) := by
    simpa only [OkOn, padd, fillEnd] using Ptr.add_nat_ok (off := d.strstart.toNat) (n := d.lookahead.toNat)
      (show Space.get h (BRef.blk w) = some wa from get) (by omega : fillEnd d ≤ wa.size)
  have stateR : hr.dstates ds = some d := by simpa [hr] using good.live.hs
  have update : wr (some (.tab ds)) (fun d => { d with lookahead := d.lookahead + n }) hr =
      .ok ((), hl) := by simp [wrD_eq, stateR, hl, dr]
  have getL : hl.bytes w = some copied := by simp [hl, hr]
  have shift : d.hash_shift < 32 := by
    rw [UInt32.lt_iff_toNat_lt]
    exact (hash_parameters good.inv).hsh_lt
  have prime := fill_prime_resume (h := hl) (ds := ds) (w := w) (d := dr) (wa := copied)
    (by simp [hl]) win getL insert
    (by change d.strstart.toNat + (d.lookahead + n).toNat ≤ copied.size
        rw [size_copyRange, extent.1]
        exact counts.2.2)
    (by simpa [copied, size_copyRange, extent.1] using extent.2) shift
  unfold fillBody
  simp only [bind_app, ldDeflateState_tab good.live.hs, noSlide, if_false,
    rdD_eq, good.live.hs, good.live.back, zrd_eq, good.live.hz,
    beq_eq_false_iff_ne.mpr nonempty, Bool.false_eq_true]
  change (do
    let dst ← padd (← padd d.window d.strstart.toNat) d.lookahead.toNat
    let n ← read_buf (some r) dst (fillMore d)
    wr (some (.tab ds)) (fun d => { d with lookahead := d.lookahead + n })
    fillPrime (some (.tab ds))
    pure false) h = _
  simp only [bind_app, first, second]
  rw [read]
  change (do
    wr (some (.tab ds)) (fun d => { d with lookahead := d.lookahead + n })
    fillPrime (some (.tab ds))
    pure false) hr = _
  rw [bind_app, update]
  simp only []
  rw [bind_app, prime]
  simp only [pure_app, hl, setD_setD]
  rfl

end Zlib.Deflate.Engine.Proofs.DefaultGzipProofs
