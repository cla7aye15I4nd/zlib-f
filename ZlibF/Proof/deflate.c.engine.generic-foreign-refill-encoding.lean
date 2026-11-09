import ZlibF.Proof.«deflate.c.engine.generic-foreign-nonpublishing-encoding»
import ZlibF.Proof.«deflate.c.engine.refill-encoding»

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Complete actual zlib refill, including sliding, pending insertion and padding, with
legal foreign-depth caller output. No output is published; held bits and both initialized
frontiers are preserved, and the extended logical input agrees with the accepted prefix.
The explicit cutpoint requires short lookahead, zlib wrap, caller buffers and PublishReady. -/
theorem default_foreign_fill_window_strategy_encoding {h : Heap} {r : ZStreamRef} {ds owner oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (short : d.lookahead.toNat < 262)
    (wrap : config.wrap = 1) (buffers : StreamBuffers h r)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (pointer : z.next_out = .ref (.dstate_depth owner) oo) (publish : PublishReady d) :
    ∃ used after z' result extended nextOrigin before,
      fill_window (some (.tab ds)) h = .ok ((), after) ∧
      StrategyBoundary after r ds z' result extended nextOrigin base xs config ∧ EndFrontier after result ∧
      StreamAccounting z z' used 0 ∧ StreamBuffers after r ∧
      nextOrigin + result.strstart.toNat = origin + d.strstart.toNat ∧
      result.lookahead.toNat = d.lookahead.toNat + used ∧
      (∀ i, i < origin + fillEnd d → extended i = input i) ∧
      (262 ≤ result.lookahead.toNat ∨ z'.avail_in = 0) ∧ FillRecordFrame d result ∧
      PublishReady result ∧ PendingBits h d before ∧ Bytes after z.next_out 0 [] ∧ PendingBits after result before ∧
      (∀ k, k ≤ origin + fillEnd d → inputPrefix extended k = inputPrefix input k) := by
  obtain ⟨used, after, z', result, extended, nextOrigin, run, stateA, accountA,
      buffersA, startA, lookA, agreesA, stoppedA, frameA⟩ :=
    fill_window_strategy_boundary boundary short wrap buffers inputValid
  have actualWrap : d.wrap = 1 := (congrArg EngineConfig.wrap boundary.configuration).trans wrap
  have endA := fill_window_run_end_frontier boundary.toContentBoundary.toPendingBoundary frontier
    short actualWrap buffers inputValid run stateA.good.live.hs
  have readyA := PublishReady.fill publish frameA
  obtain ⟨pb, buf, trees, _ledger, _balance⟩ := boundary.symbols
  have beforeInitial := pending_bits_base trees publish.2.1
  obtain ⟨pbA, bufA, treesA, _ledgerA, _balanceA⟩ := stateA.symbols
  have afterBits := pending_bits_base treesA readyA.2.1
  have valueInitial := pending_bits_zero_value publish.1 beforeInitial
  have valueAfter := pending_bits_zero_value readyA.1 afterBits
  have word : result.bi_buf = d.bi_buf := by rw [frameA]
  have count : result.bi_valid = d.bi_valid := by rw [frameA]
  rw [word, count] at valueAfter
  have sameBits : Zlib.Trees.Proofs.Out.outBits bufA result = Zlib.Trees.Proofs.Out.outBits buf d :=
    valueAfter.trans valueInitial.symm
  rw [sameBits] at afterBits
  have outputSame : z'.next_out = z.next_out := by
    rw [accountA.2.2.2.2.2.1,advance_zero]
  have pointerA : z'.next_out = .ref (.dstate_depth owner) oo := outputSame.trans pointer
  have bytesA : Bytes after z.next_out 0 [] := by
    rw [← outputSame]
    exact caller_empty_output_view stateA.good.live.hz buffersA pointerA
  refine ⟨used, after, z', result, extended, nextOrigin, Zlib.Trees.Proofs.Out.outBits buf d,
    run, stateA, endA, accountA, buffersA, startA, lookA, agreesA, stoppedA, frameA,
    readyA, beforeInitial, bytesA, afterBits, ?_⟩
  intro k bound
  unfold inputPrefix
  apply List.map_congr_left
  intro i member
  exact agreesA i (by have less := List.mem_range.mp member; omega)

end Zlib.Deflate.Engine.Proofs
