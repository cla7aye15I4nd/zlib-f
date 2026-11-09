import ZlibF.Proof.«deflate.c.borrow-stable-base»
import ZlibF.Proof.«deflate.c.engine.content-boundary»

/-! # Complete refill retains the next iteration's caller buffers -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- Empty input exits before priming and only performs the actual
high-water padding. The wrapper and insertion counter are unrestricted. -/
theorem fill_window_empty_storage {h : Heap} {r : ZStreamRef} {ds w : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8}
    (good : DGood h r ds z d) (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa)
    (range : fillEnd d ≤ d.window_size.toNat) (empty : z.avail_in = 0)
    (noSlide : ¬ d.strstart ≥ d.w_size + (d.w_size - MIN_LOOKAHEAD_u)) :
    fill_window (some (.tab ds)) h = .ok ((), paddedHeap h ds w d wa) ∧
      ByteFrame h (paddedHeap h ds w d wa) (DeflateOwned ds d) := by
  have loop := do_once (fill_body_no_input good empty noSlide) (fill_cond_break (some (.tab ds)) h)
  have pad := fill_high_water_complete good win get (window_writable good win) range
  refine ⟨?_, padded_storage_frame h ds w d wa _ (Or.inl rfl) (Or.inr (Or.inl win))⟩
  rw [fill_window_source]
  simp only [bind_app, rdD_eq, good.live.hs, loop]
  exact pad

set_option maxHeartbeats 2500000 in
/-- Every real refill branch writes byte-addressable storage only in its
private state and window. Insertion loops and both slide branches are
included. No returned-heap frame is assumed by the caller. -/
theorem fill_window_private_storage {h : Heap} {r : ZStreamRef} {ds origin : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {xs : List ZlibF.Math.DeflateSymbols.Symbol}
    (boundary : PendingBoundary h r ds z d input origin xs)
    (short : d.lookahead.toNat < 262) (wrap : d.wrap = 1) (buffers : StreamBuffers h r)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null) :
    ∃ after, fill_window (some (.tab ds)) h = .ok ((), after) ∧ ByteFrame h after (DeflateOwned ds d) := by
  by_cases empty : z.avail_in = 0
  · by_cases taken : d.strstart ≥ d.w_size + (d.w_size - MIN_LOOKAHEAD_u)
    · obtain ⟨w, p, q, wa, pa, qa, pa', qa', env, sizeP, sizeH, prefixRun, boundaryS⟩ :=
        slide_pending_boundary boundary taken
      have geometry := fill_slide_counts boundary.good env.win env.wbytes boundary.range taken
      let hs := slideHeap h ds w p q d wa pa' qa'
      have getS : hs.bytes w = some (slideWindow d wa) := by simp [hs, slideHeap]
      have run := (fill_window_empty_storage boundaryS.good env.win getS boundaryS.range empty
        geometry.2.2.2.2.2.2.2.2).1
      have first : ByteFrame h hs (DeflateOwned ds d) :=
        slide_storage_frame h ds w p q d wa pa' qa' _ (Or.inl rfl) (Or.inr (Or.inl env.win))
      have second : ByteFrame hs (paddedHeap hs ds w (slideState d) (slideWindow d wa)) (DeflateOwned ds d) :=
        padded_storage_frame hs ds w (slideState d) (slideWindow d wa) _ (Or.inl rfl) (Or.inr (Or.inl env.win))
      exact ⟨_, (fill_window_slide_transfer boundary.good env sizeP sizeH boundary.range taken prefixRun).trans run,
        first.trans second⟩
    · obtain ⟨w, wa, win, get, _, _⟩ := boundary.data
      exact ⟨_, fill_window_empty_storage boundary.good win get boundary.range empty taken⟩
  · obtain ⟨ref, io, pointer⟩ : ∃ ref io, z.next_in = .ref ref io := by
      cases pointer : z.next_in with
      | null => exact False.elim (inputValid empty pointer)
      | ref ref io => exact ⟨ref, io, rfl⟩
    obtain ⟨ia, data, inputBound⟩ := caller_input_array boundary.good buffers pointer
    by_cases taken : d.strstart ≥ d.w_size + (d.w_size - MIN_LOOKAHEAD_u)
    · obtain ⟨w, p, q, wa, pa, qa, pa', qa', env, sizeP, sizeH, prefixRun, boundaryS⟩ :=
        slide_pending_boundary boundary taken
      have geometry := fill_slide_counts boundary.good env.win env.wbytes boundary.range taken
      let hs := slideHeap h ds w p q d wa pa' qa'
      have separate := caller_input_window_separate boundary.good buffers env.win pointer
      have dataS : Space.get hs ref = some ia := by rw [slide_input_frame boundary.good separate]; exact data
      have getS : hs.bytes w = some (slideWindow d wa) := by simp [hs, slideHeap]
      obtain ⟨after, _, _, run, _, _, _, _, _, _, _, _, _, _, _, _, second⟩ :=
        fill_window_pending_complete_storage boundaryS.good boundaryS.frontier boundaryS.insert_le
          env.win getS boundaryS.range short geometry.2.2.2.2.2.2.2.2 wrap pointer dataS inputBound empty separate
      change ByteFrame hs after (DeflateOwned ds d) at second
      have first : ByteFrame h hs (DeflateOwned ds d) :=
        slide_storage_frame h ds w p q d wa pa' qa' _ (Or.inl rfl) (Or.inr (Or.inl env.win))
      exact ⟨after, (fill_window_slide_transfer boundary.good env sizeP sizeH boundary.range taken prefixRun).trans run,
        first.trans second⟩
    · obtain ⟨w, wa, win, get, _, _⟩ := boundary.data
      have separate := caller_input_window_separate boundary.good buffers win pointer
      obtain ⟨after, _, _, run, _, _, _, _, _, _, _, _, _, _, _, _, frame⟩ :=
        fill_window_pending_complete_storage boundary.good boundary.frontier boundary.insert_le win get boundary.range
          short taken wrap pointer data inputBound empty separate
      exact ⟨after, run, frame⟩

/-- The same actual full refill now supplies the next iteration's public
buffers together with decoded content, accounting and the exact state
frame. This includes every insertion count admitted by the boundary. -/
theorem fill_window_content_buffers {h : Heap} {r : ZStreamRef} {ds origin base : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {xs : List ZlibF.Math.DeflateSymbols.Symbol}
    (boundary : ContentBoundary h r ds z d input origin base xs)
    (short : d.lookahead.toNat < 262) (wrap : d.wrap = 1) (buffers : StreamBuffers h r)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null) :
    ∃ used after z' result extended nextOrigin,
      fill_window (some (.tab ds)) h = .ok ((), after) ∧
      ContentBoundary after r ds z' result extended nextOrigin base xs ∧ StreamAccounting z z' used 0 ∧
      StreamBuffers after r ∧ ByteFrame h after (DeflateOwned ds d) ∧
      nextOrigin + result.strstart.toNat = origin + d.strstart.toNat ∧
      result.lookahead.toNat = d.lookahead.toNat + used ∧ result.wrap = 1 ∧
      (nextOrigin = origin ∨ nextOrigin = origin + d.w_size.toNat) ∧
      (∀ i, i < origin + fillEnd d → extended i = input i) ∧
      (262 ≤ result.lookahead.toNat ∨ z'.avail_in = 0) ∧ FillRecordFrame d result := by
  obtain ⟨used, after, z', result, extended, nextOrigin, run, boundaryA, account,
      start, look, wrapA, originA, agrees, stopped, fields⟩ :=
    fill_window_content_boundary boundary short wrap buffers inputValid
  obtain ⟨other, run0, frame0⟩ := fill_window_private_storage boundary.toPendingBoundary short wrap buffers inputValid
  have same : other = after := congrArg Prod.snd (Except.ok.inj (run0.symm.trans run))
  subst other
  have owned := stream_owned_keys boundary.good boundaryA.good
    (congrArg (·.window) fields) (congrArg (·.prev) fields) (congrArg (·.head) fields) (congrArg (·.pending_buf) fields)
  have buffersA := stream_buffers_private_read boundary.good.live.hz boundaryA.good.live.hz buffers frame0
    (fun b mine => (stream_owned_deflate boundary.good b).mpr mine) owned account
    (Zlib.Deflate.BorrowProofs.stable_fill_window _ _ _ _ run)
  exact ⟨used, after, z', result, extended, nextOrigin, run, boundaryA, account, buffersA, frame0,
    start, look, wrapA, originA, agrees, stopped, fields⟩

end Zlib.Deflate.Engine.Proofs
