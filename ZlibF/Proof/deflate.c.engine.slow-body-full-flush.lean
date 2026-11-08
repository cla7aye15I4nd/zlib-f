import ZlibF.Proof.«deflate.c.engine.slow-match-flush»
import ZlibF.Proof.«deflate.c.engine.slow-body-loop»
import ZlibF.Proof.«deflate.c.engine.slow-literal-flush»
import ZlibF.Proof.«deflate.c.engine.slow-caller-storage»

/-! # Every slow decision with one remaining symbol slot -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

set_option maxHeartbeats 3000000 in
/-- The complete actual ready-lookahead body covers every decision at
one remaining symbol slot: full match, full literal, or no emitted symbol.
Actual insertion/search choose the branch. No selected-encoder or branch
contract is assumed. The input/content boundary comes from default init.
Short lookahead and the outer strategy loop are separate obligations. -/
theorem slow_body_full_slot {h : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8}
    (boundary : ContentBoundary h r ds z d input origin base xs)
    (buffers : StreamBuffers h r) (positive : 0 < d.level.toInt)
    (pointer : z.next_out = .ref (.blk ob) oo) (cursor : d.pending_out = d.pending_buf)
    (memory : d.lit_bufsize.toNat = 16384) (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7)
    (clear : BlockInit.BlockClear d) (lookahead : 262 ≤ d.lookahead.toNat)
    (full : d.sym_next.toNat + 3 = d.sym_end.toNat) (flush : Int32) (st : LoopS) :
    ∃ (produced : Nat) (next : LoopS) (after : Heap) (z' : ZStream) (result : DeflateState)
      (base' : Nat) (ys : List Symbol),
      deflate_slow_body (some (.tab ds)) flush st h = .ok (next, after) ∧
      ContentBoundary after r ds z' result input origin base' ys ∧
      StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧ BlockInit.BlockClear result ∧
      d.strstart.toNat < result.strstart.toNat ∧ result.lookahead.toNat < d.lookahead.toNat ∧
      fillEnd result = fillEnd d ∧ result.sym_next.toNat < result.sym_end.toNat ∧ base ≤ base' ∧ next.brk = st.brk ∧
      (next.ret = st.ret ∨ next.ret = some need_more) ∧
      ((base' = base ∧ ys = xs ∧ next.bflush = false) ∨ (ys = [] ∧ next.bflush = true)) := by
  obtain ⟨produced, next, after, z', result, base', ys, run, state, buffersA, accountA, clearA, progress, less, endpoint, countA, baseLe, brkA, retA, casesA, _config, _low, _phase, _continued, _reason⟩ :=
    slow_body_full_slot_loop boundary buffers positive pointer cursor memory pending bits clear lookahead full flush st
  exact ⟨produced, next, after, z', result, base', ys, run, state, buffersA, accountA, clearA, progress, less, endpoint, countA, baseLe, brkA, retA, casesA⟩

/-- Every actual ready-lookahead iteration preserves the initialized
content boundary, including all full-buffer encodings and both kinds
of symbol emission. Aligned strict symbol count derives tally room;
no extra room or selected-branch premise is assumed. This is one body
iteration; refill, EOF/flush tails and the outer loop remain separate. -/
theorem slow_body_ready_all {h : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8}
    (boundary : ContentBoundary h r ds z d input origin base xs)
    (buffers : StreamBuffers h r) (positive : 0 < d.level.toInt)
    (pointer : z.next_out = .ref (.blk ob) oo) (cursor : d.pending_out = d.pending_buf)
    (memory : d.lit_bufsize.toNat = 16384) (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7)
    (clear : BlockInit.BlockClear d) (lookahead : 262 ≤ d.lookahead.toNat)
    (strict : d.sym_next.toNat < d.sym_end.toNat) (flush : Int32) (st : LoopS) :
    ∃ (produced : Nat) (next : LoopS) (after : Heap) (z' : ZStream) (result : DeflateState)
      (base' : Nat) (ys : List Symbol),
      deflate_slow_body (some (.tab ds)) flush st h = .ok (next, after) ∧
      ContentBoundary after r ds z' result input origin base' ys ∧
      StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧ BlockInit.BlockClear result ∧
      d.strstart.toNat < result.strstart.toNat ∧ result.lookahead.toNat < d.lookahead.toNat ∧
      fillEnd result = fillEnd d ∧ result.sym_next.toNat < result.sym_end.toNat ∧ base ≤ base' ∧
      next.brk = st.brk ∧ (next.ret = st.ret ∨ next.ret = some need_more) := by
  obtain ⟨produced, next, after, z', result, base', ys, run, state, buffersA, accountA, clearA, progress, less, endpoint, countA, baseLe, brkA, retA, _config, _low, _phase, _continued, _reason⟩ :=
    slow_body_ready_all_loop boundary buffers positive pointer cursor memory pending bits clear lookahead strict flush st
  exact ⟨produced, next, after, z', result, base', ys, run, state, buffersA, accountA, clearA, progress, less, endpoint, countA, baseLe, brkA, retA⟩

end Zlib.Deflate.Engine.Proofs
