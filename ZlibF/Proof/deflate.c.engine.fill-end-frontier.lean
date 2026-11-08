import ZlibF.Proof.«deflate.c.engine.fill-read-end-frontier»

/-! # Complete real refill retains the frontier needed by the EOF tail -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- The actual slide carries the earlier frontier through window copying
and hash-table rebasing. -/
theorem slide_end_frontier_execution {h : Heap} {r : ZStreamRef} {ds origin : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8}
    (boundary : PendingBoundary h r ds z d input origin xs) (frontier : EndFrontier h d)
    (taken : d.strstart ≥ d.w_size + (d.w_size - MIN_LOOKAHEAD_u)) :
    ∃ after, fillSlide (some (.tab ds)) d d.w_size (fillMore d) h = .ok ((), after) ∧
      DGood after r ds z (slideState d) ∧ EndFrontier after (slideState d) := by
  obtain ⟨w, p, q, wa, pa, qa, env, chains⟩ := heap_chains_environment boundary.good frontier
  obtain ⟨b, buf, trees, ledger, balance⟩ := boundary.symbols
  have credit := deferred_credit_bounds d
  obtain ⟨qa', pa', run, sizeH, sizeP, head, prev⟩ := fill_slide_run boundary.good env trees.base ledger
    boundary.good.inv.sym.2.2.1 balance credit.1 credit.2 boundary.range taken
  have chainsS := slide_heap_chains boundary.good env chains boundary.range taken head prev
  have geometry := fill_slide_counts boundary.good env.win env.wbytes boundary.range taken
  have topEq : min (slideState d).strstart.toNat (fillEnd (slideState d) - 2) =
      min d.strstart.toNat (fillEnd d - 2) - d.w_size.toNat := by
    dsimp only [fillEnd]
    rw [geometry.2.2.2.2.1]
    change min (d.strstart.toNat - d.w_size.toNat) (d.strstart.toNat - d.w_size.toNat + d.lookahead.toNat - 2) = _
    omega
  refine ⟨slideHeap h ds w p q d wa pa' qa', run, slide_good boundary.good env sizeP sizeH, ?_⟩
  unfold EndFrontier
  rw [topEq]
  exact chainsS

/-- The slide frontier belongs to the same prefix heap as the established
complete refill proof. -/
theorem slide_run_end_frontier {h after : Heap} {r : ZStreamRef} {ds origin : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8}
    (boundary : PendingBoundary h r ds z d input origin xs) (frontier : EndFrontier h d)
    (taken : d.strstart ≥ d.w_size + (d.w_size - MIN_LOOKAHEAD_u))
    (run : fillSlide (some (.tab ds)) d d.w_size (fillMore d) h = .ok ((), after)) :
    EndFrontier after (slideState d) := by
  obtain ⟨other, otherRun, _good, endA⟩ := slide_end_frontier_execution boundary frontier taken
  have heaps : other = after := (Prod.mk.inj (Except.ok.inj (otherRun.symm.trans run))).2
  rw [← heaps]
  exact endA

set_option maxHeartbeats 1500000 in
/-- Every actual refill branch preserves the earlier frontier: empty and
nonempty caller input, slide and no slide, every pending insertion count,
and high-water padding. No intermediate execution contract is assumed. -/
theorem fill_end_frontier_execution {h : Heap} {r : ZStreamRef} {ds origin : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8}
    (boundary : PendingBoundary h r ds z d input origin xs) (frontier : EndFrontier h d)
    (short : d.lookahead.toNat < 262) (wrap : d.wrap = 1) (buffers : StreamBuffers h r)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null) :
    ∃ after z' result, fill_window (some (.tab ds)) h = .ok ((), after) ∧
      DGood after r ds z' result ∧ EndFrontier after result := by
  by_cases empty : z.avail_in = 0
  · obtain ⟨after, result, run, goodA, endA⟩ := fill_empty_end_frontier_execution boundary frontier empty
    exact ⟨after, z, result, run, goodA, endA⟩
  · obtain ⟨ref, io, pointer⟩ : ∃ ref io, z.next_in = .ref ref io := by
      cases pointer : z.next_in with
      | null => exact False.elim (inputValid empty pointer)
      | ref ref io => exact ⟨ref, io, rfl⟩
    obtain ⟨ia, data, inputBound⟩ := caller_input_array boundary.good buffers pointer
    by_cases taken : d.strstart ≥ d.w_size + (d.w_size - MIN_LOOKAHEAD_u)
    · obtain ⟨w, p, q, wa, pa, qa, pa', qa', env, sizeP, sizeH, prefixRun, boundaryS⟩ :=
        slide_pending_boundary boundary taken
      let hs := slideHeap h ds w p q d wa pa' qa'
      have endS : EndFrontier hs (slideState d) := slide_run_end_frontier boundary frontier taken prefixRun
      have geometry := fill_slide_counts boundary.good env.win env.wbytes boundary.range taken
      have noSlide := geometry.2.2.2.2.2.2.2.2
      have separate := caller_input_window_separate boundary.good buffers env.win pointer
      have getS : hs.bytes w = some (slideWindow d wa) := by simp [hs, slideHeap]
      have dataS : Space.get hs ref = some ia := by rw [slide_input_frame boundary.good separate]; exact data
      obtain ⟨after, result, output, run, goodA, _chains, _win, _bytes, _range, _pad, _form,
          _fields, _count, _other, _prefix, _stopped, _storage, endA⟩ :=
        fill_window_pending_complete_end_frontier boundaryS.good boundaryS.frontier endS boundaryS.insert_le
          env.win getS boundaryS.range short noSlide wrap pointer dataS inputBound empty separate
      exact ⟨after, _, result,
        (fill_window_slide_transfer boundary.good env sizeP sizeH boundary.range taken prefixRun).trans run, goodA, endA⟩
    · obtain ⟨w, wa, win, get, _view, _form⟩ := boundary.data
      have separate := caller_input_window_separate boundary.good buffers win pointer
      obtain ⟨after, result, output, run, goodA, _chains, _win, _bytes, _range, _pad, _form,
          _fields, _count, _other, _prefix, _stopped, _storage, endA⟩ :=
        fill_window_pending_complete_end_frontier boundary.good boundary.frontier frontier boundary.insert_le
          win get boundary.range short taken wrap pointer data inputBound empty separate
      exact ⟨after, _, result, run, goodA, endA⟩

/-- Transfer the stronger frontier to the exact state returned by the
existing actual refill and initialized strategy-boundary theorem. -/
theorem fill_window_run_end_frontier {h after : Heap} {r : ZStreamRef} {ds origin : Nat}
    {z : ZStream} {d result : DeflateState} {xs : List Symbol} {input : Nat → UInt8}
    (boundary : PendingBoundary h r ds z d input origin xs) (frontier : EndFrontier h d)
    (short : d.lookahead.toNat < 262) (wrap : d.wrap = 1) (buffers : StreamBuffers h r)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (run : fill_window (some (.tab ds)) h = .ok ((), after)) (live : after.dstates ds = some result) :
    EndFrontier after result := by
  obtain ⟨other, otherZ, otherD, otherRun, otherGood, endA⟩ :=
    fill_end_frontier_execution boundary frontier short wrap buffers inputValid
  have heaps : other = after := (Prod.mk.inj (Except.ok.inj (otherRun.symm.trans run))).2
  rw [heaps] at otherGood endA
  have stateEq : otherD = result := Option.some.inj (otherGood.live.hs.symm.trans live)
  rw [← stateEq]
  exact endA

end Zlib.Deflate.Engine.Proofs
