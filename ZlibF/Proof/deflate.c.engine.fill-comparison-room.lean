import ZlibF.Proof.«deflate.c.engine.strategy-refill»

/-! # Actual refill provides comparison room even at EOF -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- The no-slide guard reserves physical comparison room independently
of how many caller bytes are still available. -/
theorem no_slide_comparison_room {h : Heap} {r : ZStreamRef} {ds w : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8}
    (good : DGood h r ds z d) (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa)
    (range : fillEnd d ≤ d.window_size.toNat) (short : d.lookahead.toNat < 262)
    (noSlide : ¬ d.strstart ≥ d.w_size + (d.w_size - MIN_LOOKAHEAD_u)) :
    d.strstart.toNat + 262 ≤ d.window_size.toNat := by
  have room := fill_room_no_slide good win get range short noSlide
  have more := fill_more_nat good win get range
  dsimp only [fillEnd] at range
  omega

/-- The slid position fits a complete comparison even when lookahead
is zero. The actual subtraction's non-wrapping value is proved separately
by the source slide theorem. -/
theorem slid_comparison_room {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState}
    (good : DGood h r ds z d) (range : fillEnd d ≤ d.window_size.toNat) :
    d.strstart.toNat - d.w_size.toNat + 262 ≤ d.window_size.toNat := by
  have lower : 512 ≤ d.w_size.toNat := by
    rw [good.inv.wsize]
    exact Nat.pow_le_pow_right (n := 2) (by decide) good.inv.wbits_lo
  have extent := good.inv.wsz
  dsimp only [fillEnd] at range
  omega

/-- `local void fill_window(deflate_state *s)`.
Both sides of the source slide test, with input and at EOF, leave physical
room for longest_match's full comparison. No minimum returned lookahead
is assumed and no callee contract is an input premise. -/
theorem fill_comparison_room_execution {h : Heap} {r : ZStreamRef} {ds origin : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {xs : List Symbol}
    (boundary : PendingBoundary h r ds z d input origin xs)
    (short : d.lookahead.toNat < 262) (wrap : d.wrap = 1) (buffers : StreamBuffers h r)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null) :
    ∃ after z' result,
      fill_window (some (.tab ds)) h = .ok ((), after) ∧ DGood after r ds z' result ∧
      result.strstart.toNat + 262 ≤ result.window_size.toNat := by
  obtain ⟨w, wa, win, get, _view, _form⟩ := boundary.data
  by_cases empty : z.avail_in = 0
  · by_cases taken : d.strstart ≥ d.w_size + (d.w_size - MIN_LOOKAHEAD_u)
    · obtain ⟨after, run, state⟩ := fill_window_slide_empty_pending_boundary boundary empty taken
      have geometry := fill_slide_counts boundary.good win get boundary.range taken
      refine ⟨after, z, paddedState (slideState d), run, state.good, ?_⟩
      change (slideState d).strstart.toNat + 262 ≤ d.window_size.toNat
      rw [geometry.2.2.2.2.1]
      exact slid_comparison_room boundary.good boundary.range
    · obtain ⟨after, run, state⟩ := fill_window_empty_pending_boundary boundary empty taken
      exact ⟨after, z, paddedState d, run, state.good,
        no_slide_comparison_room (d := d) boundary.good win get boundary.range short taken⟩
  · obtain ⟨ref, io, pointer⟩ : ∃ ref io, z.next_in = .ref ref io := by
      cases pointer : z.next_in with
      | null => exact False.elim (inputValid empty pointer)
      | ref ref io => exact ⟨ref, io, rfl⟩
    by_cases taken : d.strstart ≥ d.w_size + (d.w_size - MIN_LOOKAHEAD_u)
    · obtain ⟨_used, after, z', result, _extended, run, state, _account, start,
        _look, _insert, _wrapA, _agrees, _stopped, fields⟩ :=
        fill_window_slide_pending_boundary boundary short taken wrap buffers pointer empty
      refine ⟨after, z', result, run, state.good, ?_⟩
      have size : result.window_size = d.window_size := by rw [fields]; rfl
      rw [start, size]
      exact slid_comparison_room boundary.good boundary.range
    · obtain ⟨_used, after, z', result, _extended, run, state, _account, start,
        _look, _insert, _wrapA, _agrees, _stopped, fields⟩ :=
        fill_window_pending_boundary boundary short taken wrap buffers pointer empty
      refine ⟨after, z', result, run, state.good, ?_⟩
      have size : result.window_size = d.window_size := by rw [fields]
      rw [start, size]
      exact no_slide_comparison_room boundary.good win get boundary.range short taken

/-- The physical bound belongs to the exact state returned by an actual
refill, rather than to a separately chosen reachable-state witness. -/
theorem fill_window_run_comparison_room {h after : Heap} {r : ZStreamRef} {ds origin : Nat}
    {z : ZStream} {d result : DeflateState} {input : Nat → UInt8} {xs : List Symbol}
    (boundary : PendingBoundary h r ds z d input origin xs)
    (short : d.lookahead.toNat < 262) (wrap : d.wrap = 1) (buffers : StreamBuffers h r)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (run : fill_window (some (.tab ds)) h = .ok ((), after)) (live : after.dstates ds = some result) :
    result.strstart.toNat + 262 ≤ result.window_size.toNat := by
  obtain ⟨otherHeap, _otherZ, otherD, otherRun, otherGood, room⟩ :=
    fill_comparison_room_execution boundary short wrap buffers inputValid
  have heapEq : otherHeap = after := (Prod.mk.inj (Except.ok.inj (otherRun.symm.trans run))).2
  rw [heapEq] at otherGood
  have stateEq : otherD = result := Option.some.inj (otherGood.live.hs.symm.trans live)
  rw [← stateEq]
  exact room

end Zlib.Deflate.Engine.Proofs
