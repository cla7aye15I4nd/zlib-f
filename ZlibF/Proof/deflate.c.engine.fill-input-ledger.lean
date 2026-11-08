import ZlibF.Proof.«deflate.c.engine.fill-checksum-boundary»
import ZlibF.Proof.«deflate.c.engine.body-checksum»

/-! # Actual refill joins exactly its consumed caller bytes to the logical input -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- All actual refill branches append exactly their consumed original
caller slice to the logical input used by raw encoding. This is a byte
equality independent of checksum equality. Empty input, sliding, pending
hash insertions and padding are included. -/
theorem fill_window_pending_input_ledger {h : Heap} {r : ZStreamRef} {ds origin : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {xs : List Symbol}
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
      (262 ≤ result.lookahead.toNat ∨ z'.avail_in = 0) ∧ FillRecordFrame d result ∧
      ∃ copied, Bytes h z.next_in used copied ∧ copied.length = used ∧
        inputPrefix extended (nextOrigin + fillEnd result) =
          inputPrefix input (origin + fillEnd d) ++ copied := by
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
        Or.inr rfl, fun _ _ => rfl, Or.inr empty, rfl,
        [], caller_input_zero_slice boundary.good buffers, rfl, ?_⟩
      · change origin + d.w_size.toNat + (slideState d).strstart.toNat = _
        rw [geometry.2.2.2.2.1]
        have start := geometry.1
        omega
      · rw [endpoint, List.append_nil]
    · obtain ⟨after, run, boundaryA⟩ := fill_window_empty_pending_boundary boundary empty taken
      exact ⟨0, after, z, paddedState d, input, origin, run, boundaryA, accounting, rfl,
        by simp [paddedState], wrap, Or.inl rfl, fun _ _ => rfl, Or.inr empty, rfl,
        [], caller_input_zero_slice boundary.good buffers, rfl, by simp only [List.append_nil]; rfl⟩
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
      obtain ⟨used, after, z', result, extended, run, boundaryA, account, startA, lookA,
          _insertA, wrapA, prefixA, stoppedA, fields⟩ :=
        fill_window_pending_boundary boundaryS short geometry.2.2.2.2.2.2.2.2 wrap buffersS pointer empty
      have inputEq := fill_window_no_slide_input_prefix boundaryS short geometry.2.2.2.2.2.2.2.2
        wrap buffersS pointer getInputS inputBound empty run boundaryA account prefixA
      rw [endpoint] at inputEq
      have slice : Bytes h z.next_in used ((incoming.toList.drop io).take used) :=
        Or.inr ⟨ref, io, incoming, pointer, getInput, by have count := account.1; omega, rfl⟩
      have length : ((incoming.toList.drop io).take used).length = used := by
        simp only [List.length_take, List.length_drop, Array.length_toList]
        have count := account.1
        omega
      refine ⟨used, after, z', result, extended, origin + d.w_size.toNat,
        (fill_window_slide_transfer boundary.good env sizeP sizeH boundary.range taken prefixRun).trans run,
        boundaryA, account, ?_, lookA, wrapA, Or.inr rfl, ?_, stoppedA, by rw [fields]; rfl,
        _, slice, length, inputEq⟩
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
      have inputEq := fill_window_no_slide_input_prefix boundary short taken wrap buffers pointer
        getInput inputBound empty run boundaryA account prefixA
      have slice : Bytes h z.next_in used ((incoming.toList.drop io).take used) :=
        Or.inr ⟨ref, io, incoming, pointer, getInput, by have count := account.1; omega, rfl⟩
      have length : ((incoming.toList.drop io).take used).length = used := by
        simp only [List.length_take, List.length_drop, Array.length_toList]
        have count := account.1
        omega
      exact ⟨used, after, z', result, extended, origin, run, boundaryA, account,
        by rw [startA], lookA, wrapA, Or.inl rfl, prefixA, stoppedA, by rw [fields]; rfl,
        _, slice, length, inputEq⟩

/-- The exact byte ledger is unchanged by the presentation of a proved
actual refill result. This connects existing raw-encoding call witnesses
to the same original caller bytes, including after sliding. -/
theorem fill_window_run_input_ledger {h after : Heap} {r : ZStreamRef}
    {ds origin nextOrigin used : Nat} {z z' : ZStream} {d result : DeflateState}
    {input extended : Nat → UInt8} {xs : List Symbol}
    (boundary : PendingBoundary h r ds z d input origin xs)
    (short : d.lookahead.toNat < 262) (wrap : d.wrap = 1) (buffers : StreamBuffers h r)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (run : fill_window (some (.tab ds)) h = .ok ((), after))
    (stateA : PendingBoundary after r ds z' result extended nextOrigin xs)
    (account : StreamAccounting z z' used 0)
    (start : nextOrigin + result.strstart.toNat = origin + d.strstart.toNat)
    (agree : ∀ i, i < origin + fillEnd d → extended i = input i) :
    ∃ copied, Bytes h z.next_in used copied ∧ copied.length = used ∧
      inputPrefix extended (nextOrigin + fillEnd result) = inputPrefix input (origin + fillEnd d) ++ copied := by
  obtain ⟨accepted, other, otherZ, otherD, otherInput, otherOrigin, otherRun,
      otherState, otherAccount, otherStart, _look, _wrap, _origin, otherAgree,
      _stopped, _frame, copied, slice, length, inputEq⟩ :=
    fill_window_pending_input_ledger boundary short wrap buffers inputValid
  have heaps : other = after := (Prod.mk.inj (Except.ok.inj (otherRun.symm.trans run))).2
  subst other
  have streams : otherZ = z' := Option.some.inj (otherState.good.live.hz.symm.trans stateA.good.live.hz)
  have states : otherD = result := Option.some.inj (otherState.good.live.hs.symm.trans stateA.good.live.hs)
  subst otherZ otherD
  have origins : otherOrigin = nextOrigin := by omega
  subst otherOrigin
  have counts := (stream_accounting_counts_unique otherAccount account).1
  have covered : nextOrigin ≤ origin + fillEnd d := by dsimp only [fillEnd]; omega
  have sameInput := pending_boundary_input_prefix_unique otherState stateA covered
    (fun i before => (otherAgree i before).trans (agree i before).symm)
  refine ⟨copied, ?_, length.trans counts, ?_⟩
  · simpa only [counts] using slice
  · rw [← sameInput]
    exact inputEq

end Zlib.Deflate.Engine.Proofs
