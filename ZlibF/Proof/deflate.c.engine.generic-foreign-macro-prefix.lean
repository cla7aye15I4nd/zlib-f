import ZlibF.Proof.«deflate.c.engine.generic-foreign-nonfinal-boundary»
import ZlibF.Proof.«deflate.c.engine.flush-block-prefix»

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols ZlibF.Math.DeflateEncoding
set_option autoImplicit false

/-- Exact real foreign-output nonfinal block publication refines a composable block prefix. -/
theorem default_foreign_flush_nonfinal_end_block_prefix {h : Heap} {r : ZStreamRef} {ds owner oo origin base offset : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8}
    (boundary : ContentBoundary h r ds z d input origin base xs) (frontier : EndFrontier h d)
    (buffers : StreamBuffers h r) (positive : 0 < d.level.toInt)
    (pointer : z.next_out = .ref (.dstate_depth owner) oo) (cursor : d.pending_out = d.pending_buf)
    (memory : d.lit_bufsize.toNat = 16384) (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7)
    (clear : BlockInit.BlockClear d) (available : d.match_available = 0)
    (position : offset % 8 = d.bi_valid.toInt.toNat % 8) :
    ∃ produced after z' result before written remaining kind body,
      FLUSH_BLOCK (some (.tab ds)) 0 h =
        .ok ((if z'.avail_out == 0 then some need_more else none), after) ∧
      ContentBoundary after r ds z' result input origin (base + represented xs) [] ∧ EndFrontier after result ∧
      StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧ BlockInit.BlockClear result ∧
      FlushWorkFrame { d with block_start := d.strstart.toUInt64.toInt64 } result ∧
      result.bi_valid.toInt < 8 ∧ (0 < z'.avail_out.toNat → PublishReady result) ∧
      PendingBits h d before ∧ Bytes after z.next_out produced written ∧ PendingBits after result remaining ∧
      kind < 3 ∧ (kind = 0 → result.bi_valid.toInt.toNat = 0) ∧
      (offset + 3 + body.length) % 8 = result.bi_valid.toInt.toNat % 8 ∧
      ZlibF.Spec.bytesToBits written ++ remaining = before ++
        (Zlib.Trees.Proofs.Out.natBits 0 1 ++ Zlib.Trees.Proofs.Out.natBits kind 2 ++ body) ∧
      BlockPrefix [] offset (inputPrefix input base)
        (Zlib.Trees.Proofs.Out.natBits 0 1 ++ Zlib.Trees.Proofs.Out.natBits kind 2 ++ body)
        (inputPrefix input (base + represented xs)) := by
  obtain ⟨pb, buf, trees, ledger, balance⟩ := boundary.symbols
  obtain ⟨w, window, win, get, view, _form⟩ := boundary.data
  have balance0 : BlockBalance d xs 0 := by
    simpa only [deferredCredit, available, ite_true] using balance
  have account0 : base + represented xs = origin + d.strstart.toNat := by
    simpa only [pendingCredit, available, ite_true, Nat.add_zero] using boundary.accounted
  obtain ⟨produced, after, z', result, written, remaining, kind, body, padding,
    run, goodA, buffersA, accountA, _sizes, _storage, clearA, _frequencies,
    _position, _low, bytesA, pendingA, _drained, _final, storedA, kindA, _padBound,
    padNone, _storedPad, outputA, grammarA⟩ :=
    default_foreign_flush_block_only_publish_aligned boundary.good trees buffers positive pointer cursor memory pending bits
      ledger clear boundary.trace win get boundary.range balance0 account0 view false
  have noPadding := padNone rfl
  rw [noPadding, List.append_nil] at outputA
  have actual : FLUSH_BLOCK (some (.tab ds)) 0 h =
      .ok ((if z'.avail_out == 0 then some need_more else none), after) := by
    have run0 : FLUSH_BLOCK_ONLY (some (.tab ds)) 0 h = .ok ((), after) := run
    unfold FLUSH_BLOCK
    simp only [bind_app, run0, ldDeflateState_tab goodA.live.hs,
      goodA.live.back, zrd_eq, goodA.live.hz]
    by_cases empty : (z'.avail_out == 0) = true <;> simp [empty, pure_app]
  obtain ⟨_otherCount, otherHeap, otherZ, otherD, otherRun, otherBoundary, otherFrontier,
    _otherBuffers, _otherAccount, _otherClear, otherFrame, otherLow, otherPhase⟩ :=
    default_foreign_flush_nonfinal_end_boundary boundary frontier buffers positive pointer cursor memory pending bits clear available
  have heapEq : otherHeap = after := (Prod.mk.inj (Except.ok.inj (otherRun.symm.trans actual))).2
  rw [heapEq] at otherBoundary otherFrontier
  have streamEq : otherZ = z' := Option.some.inj (otherBoundary.good.live.hz.symm.trans goodA.live.hz)
  have stateEq : otherD = result := Option.some.inj (otherBoundary.good.live.hs.symm.trans goodA.live.hs)
  rw [streamEq, stateEq] at otherBoundary
  rw [stateEq] at otherFrontier otherFrame otherLow
  rw [streamEq, stateEq] at otherPhase
  have beforeA := pending_bits_base trees cursor
  have beforeLength := pending_bits_exact_length beforeA
  have afterLength := pending_bits_exact_length pendingA
  have outputLength := congrArg List.length outputA
  rw [pending] at beforeLength
  simp only [UInt64.toNat_zero, Nat.mul_zero, Nat.zero_add] at beforeLength
  simp only [List.length_append, encoded_bytes_length, Zlib.Trees.Proofs.Out.natBits_length] at outputLength
  have nextPosition : (offset + 3 + body.length) % 8 = result.bi_valid.toInt.toNat % 8 := by
    omega
  have meaning : BlockPrefix [] offset (inputPrefix input base)
      (Zlib.Trees.Proofs.Out.natBits 0 1 ++ Zlib.Trees.Proofs.Out.natBits kind 2 ++ body)
      (inputPrefix input (base + represented xs)) :=
    nonfinal_block_prefix (by omega) (fun stored => by rw [nextPosition, storedA stored]) grammarA
  exact ⟨produced, after, z', result, Zlib.Trees.Proofs.Out.outBits buf d, written, remaining, kind, body,
    actual, otherBoundary, otherFrontier, buffersA, accountA, clearA, otherFrame, otherLow,
    otherPhase, beforeA, bytesA, pendingA, kindA, storedA, nextPosition, outputA, meaning⟩

end Zlib.Deflate.Engine.Proofs
