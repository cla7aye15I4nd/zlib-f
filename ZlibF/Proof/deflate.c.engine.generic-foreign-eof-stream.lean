import ZlibF.Proof.«deflate.c.engine.generic-foreign-eof-encoding»
import ZlibF.Proof.«deflate.c.engine.eof-stream-encoding»

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols ZlibF.Math.DeflateEncoding
set_option autoImplicit false

theorem default_foreign_slow_eof_finish_tail_complete_stream {h : Heap} {r : ZStreamRef} {ds owner oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8}
    {before completed : List Bool} {previous : List UInt8}
    (boundary : StrategyBoundary h r ds z d input origin base xs (engineConfig d))
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (empty : d.lookahead = 0) (positive : 0 < d.level.toInt)
    (pointer : z.next_out = .ref (.dstate_depth owner) oo) (cursor : d.pending_out = d.pending_buf)
    (memory : d.lit_bufsize.toNat = 16384) (pending : d.pending = 0) (wrap : d.wrap = 1)
    (held : PendingBits h d before)
    (wirePrefix : ZlibF.Spec.bytesToBits previous ++ before = completed)
    (prefixMeaning : BlockPrefix [] 0 [] completed (inputPrefix input base)) :
    ∃ produced after z' result ys written tailBytes,
      slowEofTail (some (.tab ds)) Z_FINISH h =
        .ok ((if z'.avail_out == 0 then finish_started else finish_done), after) ∧
      ContentBoundary after r ds z' result input origin (base + represented ys) [] ∧
      StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧
      Bytes after z.next_out produced written ∧
      Bytes after result.pending_out result.pending.toNat tailBytes ∧ result.bi_valid.toInt.toNat = 0 ∧
      ZlibF.Spec.Deflate.Valid (inputPrefix input (origin + d.strstart.toNat))
        (previous ++ written ++ tailBytes) ∧
      BufferFrame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) [⟨z.next_out,produced⟩] := by
  obtain ⟨produced, after, z', result, ys, beforeA, written, remaining, kind, body, padding,
      run, stateA, buffersA, accountA, _clear, _config, _empty, _start, _available,
      _insert, _bits, _phase, _symbols, finalA, pendingBefore, bytesA, pendingA,
      kindA, padBound, storedPad, wire, grammar,bufferFrame⟩ :=
    default_foreign_slow_eof_finish_tail_encoding boundary frontier buffers empty positive pointer cursor memory pending wrap
  have beforeEq : beforeA = before :=
    (pending_bits_zero_value pending pendingBefore).trans (pending_bits_zero_value pending held).symm
  obtain ⟨tailBytes, tailData, tailEq⟩ := pendingA
  have remainingEq : remaining = ZlibF.Spec.bytesToBits tailBytes := by
    simpa only [finalA, List.range_zero, List.map_nil, List.append_nil] using tailEq
  have fullWire : ZlibF.Spec.bytesToBits (previous ++ written ++ tailBytes) =
      completed ++ Zlib.Trees.Proofs.Out.natBits 1 1 ++ Zlib.Trees.Proofs.Out.natBits kind 2 ++ body ++ padding := by
    rw [beforeEq, remainingEq] at wire
    simp only [ZlibF.Spec.bytesToBits, List.flatMap_append, List.append_assoc] at wirePrefix wire ⊢
    rw [wire, ← List.append_assoc, wirePrefix]
  have valid := block_prefix_terminal_valid prefixMeaning (by omega) padBound fullWire
    (grammar padding (fun stored => by rw [storedPad stored]; rfl))
  exact ⟨produced, after, z', result, ys, written, tailBytes, run, stateA, buffersA,
    accountA, bytesA, tailData, finalA, valid,bufferFrame⟩

end Zlib.Deflate.Engine.Proofs
