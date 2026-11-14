import ZlibF.Proof.«deflate.c.engine.fill-preserve»
import ZlibF.Spec.Functional.Checksums

/-! # The default slow strategy's first streaming return

Short input under NO_FLUSH is retained for later matching. This is one
complete strategy-call path; positive-length matching and block emission
remain required for the complete compressor.
-/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
set_option autoImplicit false

theorem while_once {α : Type} {cond : α → M (Bool × α)} {body : α → M α}
    {h h1 h2 h3 : Heap} {a b c e : α}
    (begin : cond a h = .ok ((true, b), h1)) (step : body b h1 = .ok (c, h2))
    (stop : cond c h2 = .ok ((false, e), h3)) : cwhile cond body a h = .ok (e, h3) := by
  unfold cwhile
  change cwhile.go cond body (18446744073709551614 + 2) a h = _
  rw [cwhile.go, bind_app, begin]
  simp only [if_true]
  rw [bind_app, step]
  simp only []
  rw [cwhile.go, bind_app, stop]
  rfl

/-- The actual slow body returns need_more once its first fill has fewer
than MIN_LOOKAHEAD bytes, as prescribed by NO_FLUSH. -/
theorem slow_first_body {h after : Heap} {ds : Nat} {d df : DeflateState} (st : LoopS)
    (state : h.dstates ds = some d) (empty : d.lookahead = 0)
    (fill : fill_window (some (.tab ds)) h = .ok ((), after))
    (result : after.dstates ds = some df) (short : df.lookahead < MIN_LOOKAHEAD_u) :
    deflate_slow_body (some (.tab ds)) Z_NO_FLUSH st h =
      .ok ({ st with ret := some need_more }, after) := by
  unfold deflate_slow_body
  simp only [bind_app, rdD_eq, state, empty]
  simp only [show (0 : UInt32) < MIN_LOOKAHEAD_u from by decide, if_true]
  simp only [bind_app, fill, rdD_eq, result, short, Z_NO_FLUSH, Bool.true_and,
    show ((0 : Int32) == 0) = true from rfl, if_true]
  rfl

/-- `local block_state deflate_slow(deflate_state *s, int flush)`.
This complete first-call path retains short input under NO_FLUSH. The
fill execution is proved for the actual source by fill_window_first_read.
-/
theorem slow_first_short_run {h after : Heap} {ds : Nat} {d df : DeflateState}
    (state : h.dstates ds = some d) (empty : d.lookahead = 0)
    (fill : fill_window (some (.tab ds)) h = .ok ((), after))
    (result : after.dstates ds = some df) (short : df.lookahead < MIN_LOOKAHEAD_u) :
    deflate_slow (some (.tab ds)) Z_NO_FLUSH h = .ok (need_more, after) := by
  have loop := while_once (cond := forever) (body := deflate_slow_body (some (.tab ds)) Z_NO_FLUSH)
    (a := {}) (b := {}) (c := { ret := some need_more }) (e := { ret := some need_more })
    (h := h) (h1 := h) (h2 := after) (h3 := after) rfl
    (slow_first_body {} state empty fill result short) rfl
  unfold deflate_slow
  rw [bind_app, loop]
  rfl

/-- `local block_state deflate_slow(deflate_state *s, int flush)`.
The complete first nonempty NO_FLUSH call for fewer than 262 input bytes.
The actual fill is composed here; no callee contract is a premise.
Representation, chains and the window range hold on its exact result. -/
theorem slow_first_short {h : Heap} {r : ZStreamRef} {ds w io : Nat}
    {z : ZStream} {d : DeflateState} {ref : BRef} {ia wa : Array UInt8}
    (good : DGood h r ds z d) (chains : HeapChains h d 0)
    (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa)
    (writable : h.ro w = false) (size : wa.size = 65536)
    (ss : d.strstart = 0) (la : d.lookahead = 0) (ins : d.insert = 0) (hw : d.high_water = 0)
    (ws : d.w_size = 32768) (wsz : d.window_size = 65536) (wrap : d.wrap = 1)
    (pointer : z.next_in = .ref ref io) (input : Space.get h ref = some ia)
    (inputBound : io + z.avail_in.toNat ≤ ia.size) (nonempty : z.avail_in ≠ 0)
    (short : z.avail_in.toNat < 262)
    (separate : BRef.blk w ≠ ref ∨ (rbLen z.avail_in 65536).toNat ≤ io ∨
      io + (rbLen z.avail_in 65536).toNat ≤ 0) :
    let n := rbLen z.avail_in 65536
    let copied := copyRange wa ia 0 io n.toNat
    let z' := readStream z n ref io
      (ZlibF.Spec.Public.adlerValue z.adler ((ia.toList.drop io).take n.toNat))
    let after := firstFillHeap h r ds w z d ref io ia wa
    let df := firstFillState d n copied
    deflate_slow (some (.tab ds)) Z_NO_FLUSH h = .ok (need_more, after) ∧
      DGood after r ds z' df ∧ HeapChains after df 0 ∧
      df.strstart.toNat + df.lookahead.toNat ≤ df.window_size.toNat := by
  obtain ⟨run, goodAfter, chainsAfter, range, _⟩ := fill_window_first_complete good chains win get
    writable size ss la ins hw ws wsz wrap pointer input inputBound nonempty separate
  refine ⟨slow_first_short_run good.live.hs la run goodAfter.live.hs ?_, goodAfter, chainsAfter, range⟩
  have fields := firstFillState_keep d (rbLen z.avail_in 65536)
    (copyRange wa ia 0 io (rbLen z.avail_in 65536).toNat)
  rw [fields.2.2.2.1, UInt32.lt_iff_toNat_lt]
  have count := rbLen_nat z.avail_in 65536
  change (rbLen z.avail_in 65536).toNat < 262
  omega

end Zlib.Deflate.Engine.Proofs
