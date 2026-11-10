import ZlibF.Proof.«deflate.c.gzip-fill-resume»

/-! Actual first CRC2 fill body, with source-selected room and real hash priming.
This internal first-read endpoint retains the original empty-window premises. -/
namespace Zlib.Deflate.Engine.Proofs.DefaultGzipProofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Engine.Proofs
set_option autoImplicit false

def firstReadGzipHeap (h : Heap) (r : ZStreamRef) (ds w : Nat) (z : ZStream) (d : DeflateState)
    (ref : BRef) (io : Nat) (ia wa : Array UInt8) : Heap :=
  let n := rbLen z.avail_in 65536
  let copied := copyRange wa ia 0 io n.toNat
  let z' := readStream z n ref io (gzipReadValue z n ia io)
  setD (r.put { h with bytes := upd h.bytes w (some copied) } z') ds
    (primeState { d with lookahead := n } copied)

/-- The complete source body on the first nonempty fill: actual read_buf,
lookahead write, two-byte hash priming and the zero-iteration insert loop.
No input-length cap is imposed; the source's 65536-byte room limits it. -/
theorem fill_body_first_read_gzip {h : Heap} {r : ZStreamRef} {ds w io : Nat}
    {z : ZStream} {d : DeflateState} {ref : BRef} {ia wa : Array UInt8}
    (good : DGood h r ds z d) (win : d.window = .ref (.blk w) 0)
    (get : h.bytes w = some wa) (writable : h.ro w = false) (size : wa.size = 65536)
    (ss : d.strstart = 0) (la : d.lookahead = 0) (ins : d.insert = 0)
    (ws : d.w_size = 32768) (wsz : d.window_size = 65536) (wrap : d.wrap = 2) (globals : LibraryGlobals h)
    (pointer : z.next_in = .ref ref io) (input : Space.get h ref = some ia)
    (inputBound : io + z.avail_in.toNat ≤ ia.size) (nonempty : z.avail_in ≠ 0)
    (separate : BRef.blk w ≠ ref ∨ (rbLen z.avail_in 65536).toNat ≤ io ∨
      io + (rbLen z.avail_in 65536).toNat ≤ 0) :
    fillBody (some (.tab ds)) 32768 false h =
      .ok (false, firstReadGzipHeap h r ds w z d ref io ia wa) := by
  let n := rbLen z.avail_in 65536
  let copied := copyRange wa ia 0 io n.toNat
  let z' := readStream z n ref io (gzipReadValue z n ia io)
  let hr := r.put { h with bytes := upd h.bytes w (some copied) } z'
  let dr := { d with lookahead := n }
  let hl := setD hr ds dr
  have count : n.toNat = min z.avail_in.toNat 65536 := by simpa [n] using rbLen_nat z.avail_in 65536
  have npos : n ≠ 0 := by
    intro zero
    have pos : 0 < z.avail_in.toNat := by
      have ne : z.avail_in.toNat ≠ 0 := by intro eq; apply nonempty; exact UInt32.toNat_inj.mp eq
      omega
    have nz := UInt32.toNat_inj.mpr zero
    simp only [UInt32.toNat_zero] at nz
    omega
  have nle : n.toNat ≤ 65536 := by omega
  have nle' : (rbLen z.avail_in 65536).toNat ≤ 65536 := nle
  have bound : io + n.toNat ≤ ia.size := by omega
  have read := read_buf_gzip (bo := 0) good.live.hz good.live.zst good.live.hs wrap (crc_statics_of_library_globals globals) pointer input get writable
    65536 npos bound (by simpa [size] using nle') (by simpa only [Nat.zero_add] using separate)
  have add : padd d.window 0 h = .ok (d.window, h) := by
    rw [win]
    simpa only [OkOn, padd, Nat.zero_add] using Ptr.add_nat_ok
      (show Space.get h (BRef.blk w) = some wa from get) (by omega : 0 + 0 ≤ wa.size)
  have add' : padd (.ref (.blk w) 0 : BPtr) 0 h = .ok (.ref (.blk w) 0, h) := by
    simpa only [win] using add
  have hrState : hr.dstates ds = some d := by simpa [hr] using good.live.hs
  have update : wr (some (.tab ds)) (fun d => { d with lookahead := d.lookahead + n }) hr =
      .ok ((), hl) := by simp [wrD_eq, hrState, la, hl, dr]
  have headGet : hl.bytes w = some copied := by simp [hl, hr]
  have shift : d.hash_shift < 32 := by
    rw [UInt32.lt_iff_toNat_lt]
    exact (hash_parameters good.inv).hsh_lt
  have prime := fill_prime_initial (h := hl) (ds := ds) (w := w) (d := dr) (wa := copied)
    (by simp [hl]) (by simpa [dr] using win) headGet (by simpa [dr] using ss)
    (by simpa [dr] using ins) (by simpa [dr, copied, size_copyRange, size] using nle) shift
  unfold fillBody
  simp only [bind_app, ldDeflateState_tab good.live.hs]
  simp only [ss, ws, MIN_LOOKAHEAD_u, la, wsz]
  simp only [show ¬ ((0 : UInt32) ≥ 32768 + (32768 - 262)) from by decide, if_false]
  simp only [rdD_eq, good.live.hs, bind_app, good.live.back, zrd_eq, good.live.hz]
  simp only [beq_eq_false_iff_ne.mpr nonempty, Bool.false_eq_true, if_false]
  simp only [show ((65536 : UInt64) - (0 : UInt32).toUInt64 - (0 : UInt32).toUInt64).toUInt32 = 65536 from rfl,
    show (0 : UInt32).toNat = 0 from rfl, bind_app, ldDeflateState_tab good.live.hs,
    ss, la, win, add', read, update]
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
