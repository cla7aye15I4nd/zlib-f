import ZlibF.Proof.«deflate.c.engine.body-prefix»

/-! # A uniform actual-body encoding step for the loop induction -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols ZlibF.Math.DeflateEncoding
set_option autoImplicit false

/-- Exact written and pending bits determine the next absolute bit-position
residue. Pending bytes contribute whole bytes even when publication stops. -/
theorem pending_encoding_position {h after : Heap} {d result : DeflateState}
    {before remaining blockBits : List Bool} {written : List UInt8} {offset : Nat}
    (pendingBefore : PendingBits h d before) (pendingAfter : PendingBits after result remaining)
    (wire : ZlibF.Spec.bytesToBits written ++ remaining = before ++ blockBits)
    (position : offset % 8 = d.bi_valid.toInt.toNat % 8) :
    (offset + blockBits.length) % 8 = result.bi_valid.toInt.toNat % 8 := by
  have beforeLength := pending_bits_exact_length pendingBefore
  have afterLength := pending_bits_exact_length pendingAfter
  have count := congrArg List.length wire
  simp only [List.length_append, encoded_bytes_length] at count
  omega

/-- Every actual body has one composable encoding prefix, including the
empty prefix on refill/EOF/output stops and nonpublishing decisions.
Input-prefix agreement across refill makes that identity meaningful even
when the logical input function changes. The same result retains the
loop's complete initialized, accounting and rank/control cutpoints. -/
theorem slow_body_composable_prefix {h : Heap} {r : ZStreamRef} {ds ob oo origin base offset : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (positive : 0 < config.level.toInt) (pointer : z.next_out = .ref (.blk ob) oo)
    (memory : config.memory.toNat = 16384) (wrap : config.wrap = 1) (publish : PublishReady d)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null) (position : offset % 8 = d.bi_valid.toInt.toNat % 8)
    (flush : Int32) (st : LoopS) :
    ∃ used produced next after z' result base' ys extended nextOrigin before written remaining blockBits,
      deflate_slow_body (some (.tab ds)) flush st h = .ok (next, after) ∧
      StrategyBoundary after r ds z' result extended nextOrigin base' ys config ∧ EndFrontier after result ∧
      StreamBuffers after r ∧ StreamAccounting z z' used produced ∧ written.length = produced ∧
      (∀ i, i < origin + fillEnd d → extended i = input i) ∧
      nextOrigin + fillEnd result = origin + fillEnd d + used ∧ base ≤ base' ∧
      (next.ret = st.ret ∨ next.ret = some need_more) ∧
      (0 < z.avail_out.toNat → next.ret = none → 0 < z'.avail_out.toNat) ∧
      (next.ret = none → next.brk = false → result.lookahead.toNat + z'.avail_in.toNat < d.lookahead.toNat + z.avail_in.toNat) ∧
      (next.brk = true → st.brk = true ∨ (result.lookahead = 0 ∧ z'.avail_in = 0)) ∧
      (next.ret = some need_more → st.ret = some need_more ∨
        ((flush = Z_NO_FLUSH ∧ result.lookahead.toNat < 262 ∧ z'.avail_in = 0) ∨ z'.avail_out = 0)) ∧
      PendingBits h d before ∧ Bytes after z.next_out produced written ∧ PendingBits after result remaining ∧
      ZlibF.Spec.bytesToBits written ++ remaining = before ++ blockBits ∧
      BlockPrefix [] offset (inputPrefix input base) blockBits (inputPrefix extended base') ∧
      (offset + blockBits.length) % 8 = result.bi_valid.toInt.toNat % 8 := by
  obtain ⟨used, produced, next, after, z', result, base', ys, extended, nextOrigin,
    before, written, remaining, run, stateA, endA, buffersA, accountA, length,
    agrees, endpoint, baseLe, returns, continues, less, breaks, reason,
    pendingBefore, bytesA, pendingAfter, casesA⟩ :=
    slow_body_strategy_prefix (offset := offset) boundary frontier buffers positive pointer memory wrap publish inputValid position flush st
  have encoded : ∃ blockBits, ZlibF.Spec.bytesToBits written ++ remaining = before ++ blockBits ∧
      BlockPrefix [] offset (inputPrefix input base) blockBits (inputPrefix extended base') := by
    rcases casesA with ⟨baseEq, _zero, empty, same⟩ | ⟨_symbols, blockBits, wire, meaning, _position⟩
    · have baseBound : base ≤ origin + fillEnd d := by
        have balance := boundary.accounted
        dsimp only [fillEnd]
        omega
      have history : inputPrefix extended base = inputPrefix input base := by
        unfold inputPrefix
        apply List.map_congr_left
        intro i hi
        exact agrees i (Nat.lt_of_lt_of_le (List.mem_range.mp hi) baseBound)
      refine ⟨[], ?_, ?_⟩
      · simp only [empty, ZlibF.Spec.bytesToBits, List.flatMap_nil, List.nil_append, same, List.append_nil]
      · rw [baseEq, history]
        exact block_prefix_empty _ _ _
    · exact ⟨blockBits, wire, meaning⟩
  obtain ⟨blockBits, wire, meaning⟩ := encoded
  exact ⟨used, produced, next, after, z', result, base', ys, extended, nextOrigin,
    before, written, remaining, blockBits, run, stateA, endA, buffersA, accountA, length,
    agrees, endpoint, baseLe, returns, continues, less, breaks, reason, pendingBefore,
    bytesA, pendingAfter, wire, meaning, pending_encoding_position pendingBefore pendingAfter wire position⟩

end Zlib.Deflate.Engine.Proofs
