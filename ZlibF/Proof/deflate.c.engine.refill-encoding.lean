import ZlibF.Proof.«deflate.c.engine.search-decision-encoding»
import ZlibF.Proof.«deflate.c.engine.strategy-refill»
import ZlibF.Proof.«deflate.c.engine.fill-end-frontier»

/-! # Actual refill preserves all output bits and the previously accepted input prefix -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- The complete actual refill, including sliding, pending insertions and
padding, retains every output bit and both initialized frontiers. Its
extended logical input agrees with every previously accepted prefix.
No refill/copy/checksum contract is a caller assumption. This is the
refill cutpoint; complete body and public histories remain separate. -/
theorem fill_window_strategy_encoding {h : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (short : d.lookahead.toNat < 262)
    (wrap : config.wrap = 1) (buffers : StreamBuffers h r)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (pointer : z.next_out = .ref (.blk ob) oo) (publish : PublishReady d) :
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
  obtain ⟨written, bytesA, length⟩ := accounted_output_bytes stateA.good.live.hz buffersA pointer accountA
  have emptyWritten : written = [] := by
    cases written with
    | nil => rfl
    | cons _ _ => simp at length
  rw [emptyWritten] at bytesA
  refine ⟨used, after, z', result, extended, nextOrigin, Zlib.Trees.Proofs.Out.outBits buf d,
    run, stateA, endA, accountA, buffersA, startA, lookA, agreesA, stoppedA, frameA,
    readyA, beforeInitial, bytesA, afterBits, ?_⟩
  intro k bound
  unfold inputPrefix
  apply List.map_congr_left
  intro i member
  exact agreesA i (by have less := List.mem_range.mp member; omega)

end Zlib.Deflate.Engine.Proofs
