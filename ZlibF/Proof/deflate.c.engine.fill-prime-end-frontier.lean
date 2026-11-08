import ZlibF.Proof.«deflate.c.engine.fill-empty-end-frontier»

/-! # Actual refill read and pending insertion retain the EOF frontier -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- Appending caller input grows the valid endpoint without invalidating
any earlier hash key. The earlier frontier can then advance monotonically. -/
theorem pending_read_end_frontier {h : Heap} {r : ZStreamRef} {ds w io : Nat}
    {z : ZStream} {d : DeflateState} {ref : BRef} {ia wa : Array UInt8}
    (good : DGood h r ds z d) (frontier : EndFrontier h d)
    (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa)
    (range : fillEnd d ≤ d.window_size.toNat) :
    let n := rbLen z.avail_in (fillMore d)
    EndFrontier (pendingReadHeap h r ds w z d ref io ia wa) (pendingReadState d n) := by
  have chains := pending_read_chains (ref := ref) (io := io) (ia := ia) good frontier win get range
  have counts := resume_read_counts good win get range
  unfold EndFrontier
  apply heap_chains_raise chains
  have look : (pendingReadState d (rbLen z.avail_in (fillMore d))).lookahead.toNat =
      d.lookahead.toNat + (rbLen z.avail_in (fillMore d)).toNat := counts.2.1
  change min d.strstart.toNat (fillEnd d - 2) ≤
    min d.strstart.toNat (d.strstart.toNat + (pendingReadState d (rbLen z.avail_in (fillMore d))).lookahead.toNat - 2)
  dsimp only [fillEnd]
  rw [look]
  omega

/-- Priming either inserts the pending keys up to the real endpoint, or
executes the actual no-op branch when fewer than three key bytes exist. -/
theorem fill_prime_end_frontier_execution {h : Heap} {r : ZStreamRef} {ds w : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8}
    (good : DGood h r ds z d) (chains : HeapChains h d (d.strstart.toNat - d.insert.toNat))
    (frontier : EndFrontier h d) (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa)
    (range : fillEnd d ≤ d.window_size.toNat) (pending : d.insert.toNat ≤ d.strstart.toNat) :
    ∃ after result, fillPrime (some (.tab ds)) h = .ok ((), after) ∧
      DGood after r ds z result ∧ EndFrontier after result := by
  by_cases enter : d.lookahead + d.insert ≥ MIN_MATCH_u
  · obtain ⟨after, result, run, goodA, chainsA, _bytes, frame, count, _form, _storage⟩ :=
      fill_prime_pending_storage good chains win get range pending
    have sum := pending_sum_nat good win get range pending
    have enough : 3 ≤ d.lookahead.toNat + d.insert.toNat := by
      have value := UInt32.le_iff_toNat_le.mp enter
      rw [sum] at value
      exact value
    have lookA : result.lookahead = d.lookahead := congrArg (·.lookahead) frame
    have countA : result.insert.toNat = 2 - d.lookahead.toNat := by
      rw [count]
      exact Nat.min_eq_right (by omega)
    have topEq : min result.strstart.toNat (fillEnd result - 2) = result.strstart.toNat - result.insert.toNat := by
      dsimp only [fillEnd]
      rw [lookA, countA]
      omega
    refine ⟨after, result, run, goodA, ?_⟩
    unfold EndFrontier
    rw [topEq]
    exact chainsA
  · refine ⟨h, d, ?_, good, frontier⟩
    rw [fill_prime_pending_source]
    simp only [bind_app, ldDeflateState_tab good.live.hs, enter, ite_false, pure_app]

/-- Transfer priming's stronger frontier to the established actual run. -/
theorem fill_prime_run_end_frontier {h after : Heap} {r : ZStreamRef} {ds w : Nat}
    {z : ZStream} {d result : DeflateState} {wa : Array UInt8}
    (good : DGood h r ds z d) (chains : HeapChains h d (d.strstart.toNat - d.insert.toNat))
    (frontier : EndFrontier h d) (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa)
    (range : fillEnd d ≤ d.window_size.toNat) (pending : d.insert.toNat ≤ d.strstart.toNat)
    (run : fillPrime (some (.tab ds)) h = .ok ((), after)) (live : after.dstates ds = some result) :
    EndFrontier after result := by
  obtain ⟨other, otherD, otherRun, otherGood, otherEnd⟩ :=
    fill_prime_end_frontier_execution good chains frontier win get range pending
  have heaps : other = after := (Prod.mk.inj (Except.ok.inj (otherRun.symm.trans run))).2
  rw [heaps] at otherGood otherEnd
  have stateEq : otherD = result := Option.some.inj (otherGood.live.hs.symm.trans live)
  rw [← stateEq]
  exact otherEnd

end Zlib.Deflate.Engine.Proofs
