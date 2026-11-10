import ZlibF.Proof.«deflate.c.engine.checksum-input»
import ZlibF.Proof.«deflate.c.engine.fill-pending-complete»

/-! # Every actual refill preserves checksum meaning for its logical input -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Actual fill_window, including both slide branches and pending hash
insertions, retains the checksum of the same accepted logical input used
by the compression boundary. The incoming checksum fact is explicit and
is preserved, rather than an assumed execution contract. -/
theorem fill_window_pending_logical_adler {h : Heap} {r : ZStreamRef} {ds origin : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {xs : List Symbol}
    (boundary : PendingBoundary h r ds z d input origin xs)
    (short : d.lookahead.toNat < 262) (wrap : d.wrap = 1) (buffers : StreamBuffers h r)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (checksum : z.adler = (ZlibF.Spec.adler32 (inputPrefix input (origin + fillEnd d))).toUInt64) :
    ∃ used after z' result extended nextOrigin,
      fill_window (some (.tab ds)) h = .ok ((), after) ∧
      PendingBoundary after r ds z' result extended nextOrigin xs ∧ StreamAccounting z z' used 0 ∧
      nextOrigin + result.strstart.toNat = origin + d.strstart.toNat ∧
      result.lookahead.toNat = d.lookahead.toNat + used ∧ result.wrap = 1 ∧
      (nextOrigin = origin ∨ nextOrigin = origin + d.w_size.toNat) ∧
      (∀ i, i < origin + fillEnd d → extended i = input i) ∧
      (262 ≤ result.lookahead.toNat ∨ z'.avail_in = 0) ∧ FillRecordFrame d result ∧
      z'.adler = (ZlibF.Spec.adler32 (inputPrefix extended (nextOrigin + fillEnd result))).toUInt64 := by
  obtain ⟨w, window, win, get, _view, _form⟩ := boundary.data
  have accounting : StreamAccounting z z 0 0 := stream_accounting_zero z
  by_cases empty : z.avail_in = 0
  · by_cases taken : d.strstart ≥ d.w_size + (d.w_size - MIN_LOOKAHEAD_u)
    · obtain ⟨after, run, boundaryA⟩ := fill_window_slide_empty_pending_boundary boundary empty taken
      have geometry := fill_slide_counts boundary.good win get boundary.range taken
      have endpoint : origin + d.w_size.toNat + fillEnd (paddedState (slideState d)) = origin + fillEnd d := by
        change origin + d.w_size.toNat + fillEnd (slideState d) = _
        rw [geometry.2.2.2.2.2.1]
        have start := geometry.1
        dsimp only [fillEnd] at *
        omega
      refine ⟨0, after, z, paddedState (slideState d), input, origin + d.w_size.toNat,
        run, boundaryA, accounting, ?_, by simp [paddedState, slideState, slideBeforeHash], wrap,
        Or.inr rfl, fun _ _ => rfl, Or.inr empty, rfl, ?_⟩
      · change origin + d.w_size.toNat + (slideState d).strstart.toNat = _
        rw [geometry.2.2.2.2.1]
        have start := geometry.1
        omega
      · rw [endpoint]
        exact checksum
    · obtain ⟨after, run, boundaryA⟩ := fill_window_empty_pending_boundary boundary empty taken
      exact ⟨0, after, z, paddedState d, input, origin, run, boundaryA, accounting, rfl,
        by simp [paddedState], wrap, Or.inl rfl, fun _ _ => rfl, Or.inr empty, rfl, checksum⟩
  · obtain ⟨ref, io, pointer⟩ : ∃ ref io, z.next_in = .ref ref io := by
      cases pointer : z.next_in with
      | null => exact False.elim (inputValid empty pointer)
      | ref ref io => exact ⟨ref, io, rfl⟩
    obtain ⟨incoming, getInput, inputBound⟩ := caller_input_array boundary.good buffers pointer
    by_cases taken : d.strstart ≥ d.w_size + (d.w_size - MIN_LOOKAHEAD_u)
    · obtain ⟨wS, p, q, windowS, pa, qa, pa', qa', env, sizeP, sizeH, prefixRun, boundaryS⟩ :=
        slide_pending_boundary boundary taken
      have geometry := fill_slide_counts boundary.good env.win env.wbytes boundary.range taken
      let hs := slideHeap h ds wS p q d windowS pa' qa'
      have separate := caller_input_window_separate boundary.good buffers env.win pointer
      have getInputS : Space.get hs ref = some incoming := by
        rw [slide_input_frame boundary.good separate]
        exact getInput
      have frame := slide_storage_frame h ds wS p q d windowS pa' qa' (DeflateOwned ds d)
        (Or.inl rfl) (Or.inr (Or.inl env.win))
      have owned := stream_owned_keys boundary.good boundaryS.good rfl rfl rfl rfl
      have buffersS : StreamBuffers hs r := stream_buffers_private_read boundary.good.live.hz
        boundaryS.good.live.hz buffers frame (fun b key => (stream_owned_deflate boundary.good b).mpr key)
        owned (stream_accounting_zero z)
      have endpoint : origin + d.w_size.toNat + fillEnd (slideState d) = origin + fillEnd d := by
        rw [geometry.2.2.2.2.2.1]
        have start := geometry.1
        dsimp only [fillEnd] at *
        omega
      have checksumS : z.adler = (ZlibF.Spec.adler32
          (inputPrefix input (origin + d.w_size.toNat + fillEnd (slideState d)))).toUInt64 := by
        rw [endpoint]
        exact checksum
      obtain ⟨used, after, z', result, extended, run, boundaryA, account, startA, lookA,
          _insertA, wrapA, prefixA, stoppedA, fields⟩ :=
        fill_window_pending_boundary boundaryS short geometry.2.2.2.2.2.2.2.2 wrap buffersS pointer empty
      have checksumA := fill_window_no_slide_logical_adler boundaryS short geometry.2.2.2.2.2.2.2.2
        wrap buffersS pointer getInputS inputBound empty checksumS run boundaryA account prefixA
      refine ⟨used, after, z', result, extended, origin + d.w_size.toNat,
        (fill_window_slide_transfer boundary.good env sizeP sizeH boundary.range taken prefixRun).trans run,
        boundaryA, account, ?_, lookA, wrapA, Or.inr rfl, ?_, stoppedA, by rw [fields]; rfl, checksumA⟩
      · rw [startA, geometry.2.2.2.2.1]
        have start := geometry.1
        omega
      · intro i before
        apply prefixA i
        rw [endpoint]
        exact before
    · obtain ⟨used, after, z', result, extended, run, boundaryA, account, startA, lookA,
          _insertA, wrapA, prefixA, stoppedA, fields⟩ :=
        fill_window_pending_boundary boundary short taken wrap buffers pointer empty
      have checksumA := fill_window_no_slide_logical_adler boundary short taken wrap buffers pointer
        getInput inputBound empty checksum run boundaryA account prefixA
      exact ⟨used, after, z', result, extended, origin, run, boundaryA, account,
        by rw [startA], lookA, wrapA, Or.inl rfl, prefixA, stoppedA, by rw [fields]; rfl, checksumA⟩

/-- Checksum refinement applies to any presentation of the same actual
returned refill heap and logical compression boundary. Earlier input
agreement and the source's position accounting identify the entire prefix;
no choice of ghost input can change the checksum meaning. -/
theorem fill_window_run_logical_adler {h after : Heap} {r : ZStreamRef}
    {ds origin nextOrigin used : Nat} {z z' : ZStream} {d result : DeflateState}
    {input extended : Nat → UInt8} {xs : List Symbol}
    (boundary : PendingBoundary h r ds z d input origin xs)
    (short : d.lookahead.toNat < 262) (wrap : d.wrap = 1) (buffers : StreamBuffers h r)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (checksum : z.adler = (ZlibF.Spec.adler32 (inputPrefix input (origin + fillEnd d))).toUInt64)
    (run : fill_window (some (.tab ds)) h = .ok ((), after))
    (stateA : PendingBoundary after r ds z' result extended nextOrigin xs)
    (account : StreamAccounting z z' used 0)
    (start : nextOrigin + result.strstart.toNat = origin + d.strstart.toNat)
    (agree : ∀ i, i < origin + fillEnd d → extended i = input i) :
    z'.adler = (ZlibF.Spec.adler32 (inputPrefix extended (nextOrigin + fillEnd result))).toUInt64 := by
  obtain ⟨_used, other, otherZ, otherD, otherInput, otherOrigin, otherRun,
      otherState, _otherAccount, otherStart, _look, _wrap, _origin, otherAgree,
      _stopped, _frame, otherChecksum⟩ :=
    fill_window_pending_logical_adler boundary short wrap buffers inputValid checksum
  have heaps : other = after := (Prod.mk.inj (Except.ok.inj (otherRun.symm.trans run))).2
  subst other
  have streams : otherZ = z' := Option.some.inj (otherState.good.live.hz.symm.trans stateA.good.live.hz)
  have states : otherD = result := Option.some.inj (otherState.good.live.hs.symm.trans stateA.good.live.hs)
  subst otherZ otherD
  have origins : otherOrigin = nextOrigin := by omega
  subst otherOrigin
  have covered : nextOrigin ≤ origin + fillEnd d := by dsimp only [fillEnd]; omega
  have sameInput := pending_boundary_input_prefix_unique otherState stateA covered
    (fun i before => (otherAgree i before).trans (agree i before).symm)
  rw [sameInput] at otherChecksum
  exact otherChecksum

end Zlib.Deflate.Engine.Proofs
