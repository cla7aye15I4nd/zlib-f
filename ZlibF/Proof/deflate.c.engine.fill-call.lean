import ZlibF.Proof.«deflate.c.engine.fill-padding»
import ZlibF.Spec.Functional.Checksums

/-! # Complete first fill_window call with input

The first read consumes min(avail_in, 65536). If lookahead is still below
262, that read exhausted the input, so the source loop stops immediately.
The actual padding write and all hash priming statements are retained.
-/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

theorem setD_bytes_commute (h : Heap) (ds : Nat) (d : DeflateState)
    (bytes : Tbl (Option (Array UInt8))) :
    { setD h ds d with bytes } = setD { h with bytes } ds d := rfl

theorem primeState_fields (d : DeflateState) (a : Array UInt8) :
    (primeState d a).strm = d.strm ∧ (primeState d a).strstart = d.strstart ∧
    (primeState d a).lookahead = d.lookahead ∧ (primeState d a).high_water = d.high_water ∧
    (primeState d a).window_size = d.window_size ∧ (primeState d a).window = d.window := by
  unfold primeState
  split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

def firstFillState (d : DeflateState) (n : UInt32) (copied : Array UInt8) : DeflateState :=
  { primeState { d with lookahead := n } copied with
    high_water := n.toUInt64 + firstPadding n }

def firstFillHeap (h : Heap) (r : ZStreamRef) (ds w : Nat) (z : ZStream) (d : DeflateState)
    (ref : BRef) (io : Nat) (ia wa : Array UInt8) : Heap :=
  let n := rbLen z.avail_in 65536
  let copied := copyRange wa ia 0 io n.toNat
  let z' := readStream z n ref io (adlerValue z.adler ((ia.toList.drop io).take n.toNat))
  setD (r.put { h with
    bytes := upd h.bytes w (some (fillRange copied n.toNat (firstPadding n).toNat 0)) } z') ds
      (firstFillState d n copied)

/-- `local void fill_window(deflate_state *s)`.
The complete first nonempty call returns the exact copied and padded
window, checksum, cursors and primed state. Input size remains arbitrary.
The stream status may already be BUSY after wrapper header emission. -/
theorem fill_window_first_read {h : Heap} {r : ZStreamRef} {ds w io : Nat}
    {z : ZStream} {d : DeflateState} {ref : BRef} {ia wa : Array UInt8}
    (good : DGood h r ds z d) (win : d.window = .ref (.blk w) 0)
    (get : h.bytes w = some wa) (writable : h.ro w = false) (size : wa.size = 65536)
    (ss : d.strstart = 0) (la : d.lookahead = 0) (ins : d.insert = 0) (hw : d.high_water = 0)
    (ws : d.w_size = 32768) (wsz : d.window_size = 65536) (wrap : d.wrap = 1)
    (pointer : z.next_in = .ref ref io) (input : Space.get h ref = some ia)
    (inputBound : io + z.avail_in.toNat ≤ ia.size) (nonempty : z.avail_in ≠ 0)
    (separate : BRef.blk w ≠ ref ∨ (rbLen z.avail_in 65536).toNat ≤ io ∨
      io + (rbLen z.avail_in 65536).toNat ≤ 0) :
    fill_window (some (.tab ds)) h =
      .ok ((), firstFillHeap h r ds w z d ref io ia wa) := by
  let n := rbLen z.avail_in 65536
  let copied := copyRange wa ia 0 io n.toNat
  let z' := readStream z n ref io (adlerValue z.adler ((ia.toList.drop io).take n.toNat))
  let dr := primeState { d with lookahead := n } copied
  let hr := firstRead h r ds w z d ref io ia wa
  have fields := primeState_fields { d with lookahead := n } copied
  have look : dr.lookahead = n := fields.2.2.1
  have state : hr.dstates ds = some dr := by simp [hr, firstRead, dr, n, copied]
  have stream : r.get hr = some z' := by
    simp only [hr, firstRead, ZStreamRef.get_setD]
    exact ZStreamRef.get_put_same (by simpa [stream_get_bytes] using good.live.hz) _
  have next : fillCond (some (.tab ds)) false hr = .ok ((false, false), hr) := by
    have back : dr.strm = some r := fields.1.trans good.live.back
    have exhausted : n < MIN_LOOKAHEAD_u → z'.avail_in = 0 := by
      intro small
      have smallNat : n.toNat < 262 := by simpa [UInt32.lt_iff_toNat_lt, MIN_LOOKAHEAD_u] using small
      have count : n.toNat = min z.avail_in.toNat 65536 := by simpa [n] using rbLen_nat z.avail_in 65536
      have eq : n = z.avail_in := UInt32.toNat_inj.mp (by omega)
      simp [z', readStream, eq]
    unfold fillCond
    simp only [bind_app, ldDeflateState_tab state, Bool.false_eq_true, if_false, look, back]
    by_cases small : n < MIN_LOOKAHEAD_u
    · simp [small, zrd_eq, stream, exhausted small]
    · simp [small]
  have body := fill_body_first_read good win get writable size ss la ins ws wsz wrap pointer input
    inputBound nonempty separate
  have loop := do_once body next
  have count : n.toNat = min z.avail_in.toNat 65536 := by simpa [n] using rbLen_nat z.avail_in 65536
  have bound : n.toNat ≤ 65536 := by omega
  have nz : n ≠ 0 := by
    intro zero
    have zeroNat : n.toNat = 0 := by rw [zero]; rfl
    have ai : z.avail_in.toNat = 0 := by omega
    exact nonempty (UInt32.toNat_inj.mp ai)
  have bytes : hr.bytes w = some copied := by simp [hr, firstRead, n, copied]
  have ro : hr.ro w = false := by simpa [hr, firstRead] using writable
  have pad := fill_high_water_first state
    (fields.2.2.2.2.2.trans win) bytes ro (by simpa [copied, size_copyRange] using size)
    (fields.2.1.trans ss) (fields.2.2.2.1.trans hw) (fields.2.2.2.2.1.trans wsz)
    (by simpa only [look] using nz) (by simpa only [look] using bound)
  rw [fill_window_source]
  simp only [bind_app, rdD_eq, good.live.hs, ws, loop]
  rw [pad]
  simp only [look]
  simp only [hr, firstRead, setD_bytes, ZStreamRef.put_bytes, setD_bytes_commute,
    setD_setD, ← stream_put_bytes, upd_upd, firstFillHeap, firstFillState]
  dsimp only [dr, primeState]
  split <;> rfl

end Zlib.Deflate.Engine.Proofs
