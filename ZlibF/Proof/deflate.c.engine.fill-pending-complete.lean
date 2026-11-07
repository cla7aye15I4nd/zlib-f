import ZlibF.Proof.«deflate.c.engine.fill-slide-pending»

/-! # Full refill preservation from the initialized pending boundary -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- An internal call after the public null-input refusal. Empty input,
pending insertions and both sides of the slide test are covered. The
caller supplies public buffer storage, not an intermediate heap contract.
-/
theorem fill_window_pending_boundary_all {h : Heap} {r : ZStreamRef} {ds origin : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {xs : List ZlibF.Math.DeflateSymbols.Symbol}
    (boundary : PendingBoundary h r ds z d input origin xs)
    (short : d.lookahead.toNat < 262) (wrap : d.wrap = 1) (buffers : StreamBuffers h r)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null) :
    ∃ used after z' result extended nextOrigin,
      fill_window (some (.tab ds)) h = .ok ((), after) ∧
      PendingBoundary after r ds z' result extended nextOrigin xs ∧ StreamAccounting z z' used 0 ∧
      nextOrigin + result.strstart.toNat = origin + d.strstart.toNat ∧
      result.lookahead.toNat = d.lookahead.toNat + used ∧ result.wrap = 1 ∧
      (nextOrigin = origin ∨ nextOrigin = origin + d.w_size.toNat) ∧
      (∀ i, i < origin + fillEnd d → extended i = input i) ∧
      (262 ≤ result.lookahead.toNat ∨ z'.avail_in = 0) := by
  obtain ⟨w, wa, win, get, _, _⟩ := boundary.data
  have accounting : StreamAccounting z z 0 0 := by
    refine ⟨by omega, by omega, by omega, by omega, ?_, ?_, rfl, rfl, rfl, rfl, rfl⟩
    · cases z.next_in <;> rfl
    · cases z.next_out <;> rfl
  by_cases empty : z.avail_in = 0
  · by_cases taken : d.strstart ≥ d.w_size + (d.w_size - MIN_LOOKAHEAD_u)
    · obtain ⟨after, run, boundaryA⟩ := fill_window_slide_empty_pending_boundary boundary empty taken
      have geometry := fill_slide_counts boundary.good win get boundary.range taken
      refine ⟨0, after, z, paddedState (slideState d), input, origin + d.w_size.toNat,
        run, boundaryA, accounting, ?_, by simp [paddedState, slideState, slideBeforeHash], wrap,
        Or.inr rfl, fun _ _ => rfl, Or.inr empty⟩
      change origin + d.w_size.toNat + (slideState d).strstart.toNat = _
      rw [geometry.2.2.2.2.1]
      have start := geometry.1
      omega
    · obtain ⟨after, run, boundaryA⟩ := fill_window_empty_pending_boundary boundary empty taken
      exact ⟨0, after, z, paddedState d, input, origin, run, boundaryA, accounting, rfl,
        by simp [paddedState], wrap, Or.inl rfl, fun _ _ => rfl, Or.inr empty⟩
  · obtain ⟨ref, io, pointer⟩ : ∃ ref io, z.next_in = .ref ref io := by
      cases pointer : z.next_in with
      | null => exact False.elim (inputValid empty pointer)
      | ref ref io => exact ⟨ref, io, rfl⟩
    by_cases taken : d.strstart ≥ d.w_size + (d.w_size - MIN_LOOKAHEAD_u)
    · obtain ⟨used, after, z', result, extended, run, boundaryA, account, start, look, _, wrapA, prefixA, stop, _⟩ :=
        fill_window_slide_pending_boundary boundary short taken wrap buffers pointer empty
      have geometry := fill_slide_counts boundary.good win get boundary.range taken
      refine ⟨used, after, z', result, extended, origin + d.w_size.toNat, run, boundaryA, account,
        ?_, look, wrapA, Or.inr rfl, prefixA, stop⟩
      rw [start]
      have before := geometry.1
      omega
    · obtain ⟨used, after, z', result, extended, run, boundaryA, account, start, look, _, wrapA, prefixA, stop, _⟩ :=
        fill_window_pending_boundary boundary short taken wrap buffers pointer empty
      exact ⟨used, after, z', result, extended, origin, run, boundaryA, account,
        by rw [start], look, wrapA, Or.inl rfl, prefixA, stop⟩

end Zlib.Deflate.Engine.Proofs
