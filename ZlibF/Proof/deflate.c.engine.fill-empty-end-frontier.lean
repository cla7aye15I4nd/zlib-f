import ZlibF.Proof.«deflate.c.engine.short-strategy-step»

/-! # Real refill with no caller input preserves the earlier EOF frontier -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- The no-slide empty-input path only pads beyond real valid data. -/
theorem fill_empty_no_slide_end_frontier {h : Heap} {r : ZStreamRef} {ds w : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8}
    (good : DGood h r ds z d) (frontier : EndFrontier h d)
    (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa)
    (range : fillEnd d ≤ d.window_size.toNat) (empty : z.avail_in = 0)
    (noSlide : ¬ d.strstart ≥ d.w_size + (d.w_size - MIN_LOOKAHEAD_u)) :
    fill_window (some (.tab ds)) h = .ok ((), paddedHeap h ds w d wa) ∧
      EndFrontier (paddedHeap h ds w d wa) (paddedState d) := by
  exact ⟨(fill_window_empty_storage good win get range empty noSlide).1,
    padded_chains good frontier win get range⟩

/-- Both real slide choices preserve the earlier frontier at empty input.
The generic slide theorem transports the original lower frontier, rather
than trying to recover it from the current-position frontier. -/
theorem fill_empty_end_frontier_execution {h : Heap} {r : ZStreamRef} {ds origin : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8}
    (boundary : PendingBoundary h r ds z d input origin xs) (frontier : EndFrontier h d)
    (empty : z.avail_in = 0) :
    ∃ after result, fill_window (some (.tab ds)) h = .ok ((), after) ∧
      DGood after r ds z result ∧ EndFrontier after result := by
  obtain ⟨w, wa, win, get, view, form⟩ := boundary.data
  by_cases taken : d.strstart ≥ d.w_size + (d.w_size - MIN_LOOKAHEAD_u)
  · obtain ⟨wb, p, q, bytes, pa, qa, env, chains⟩ := heap_chains_environment boundary.good frontier
    have winEq : wb = w := by simpa only [win, Ptr.ref.injEq, BRef.blk.injEq, and_true] using env.win.symm
    subst wb
    have arrayEq : bytes = wa := Option.some.inj (env.wbytes.symm.trans get)
    subst bytes
    obtain ⟨b, buf, trees, ledger, balance⟩ := boundary.symbols
    have credit := deferred_credit_bounds d
    obtain ⟨after, result, output, run, goodA, chainsA, _winA, _bytesA, startA, lookA, _rest⟩ :=
      fill_window_slide_empty boundary.good env chains trees.base ledger balance credit.1 credit.2
        boundary.range taken empty boundary.history view form
    have topEq : min result.strstart.toNat (fillEnd result - 2) =
        min d.strstart.toNat (fillEnd d - 2) - d.w_size.toNat := by
      have lookNat : result.lookahead.toNat = d.lookahead.toNat := by rw [lookA]
      dsimp only [fillEnd]
      rw [startA, lookNat]
      omega
    refine ⟨after, result, run, goodA, ?_⟩
    unfold EndFrontier
    rw [topEq]
    exact chainsA
  · have run := fill_empty_no_slide_end_frontier boundary.good frontier win get boundary.range empty taken
    exact ⟨paddedHeap h ds w d wa, paddedState d, run.1,
      padded_good boundary.good win get boundary.range, run.2⟩

/-- The stronger frontier belongs to the same actual returned state used
by the existing complete refill/content theorem. -/
theorem fill_empty_run_end_frontier {h after : Heap} {r : ZStreamRef} {ds origin : Nat}
    {z : ZStream} {d result : DeflateState} {xs : List Symbol} {input : Nat → UInt8}
    (boundary : PendingBoundary h r ds z d input origin xs) (frontier : EndFrontier h d)
    (empty : z.avail_in = 0) (run : fill_window (some (.tab ds)) h = .ok ((), after))
    (live : after.dstates ds = some result) : EndFrontier after result := by
  obtain ⟨other, otherD, otherRun, otherGood, otherEnd⟩ :=
    fill_empty_end_frontier_execution boundary frontier empty
  have heaps : other = after := (Prod.mk.inj (Except.ok.inj (otherRun.symm.trans run))).2
  rw [heaps] at otherGood otherEnd
  have stateEq : otherD = result := Option.some.inj (otherGood.live.hs.symm.trans live)
  rw [← stateEq]
  exact otherEnd

end Zlib.Deflate.Engine.Proofs
