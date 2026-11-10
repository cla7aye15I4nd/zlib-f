import ZlibF.Proof.«deflate.c.engine.memory-macro-content-from-four»
import ZlibF.Proof.«deflate.c.engine.memory-macro-publish-from-four»
import ZlibF.Proof.«deflate.c.engine.eof-tail-encoding»

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Actual insertion reset keeps caller ranges and the exact content/frontiers. -/
theorem memory_eof_insert_content_buffers_from_four {h : Heap} {r : ZStreamRef} {ds origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8}
    (boundary : ContentBoundary h r ds z d input origin base xs)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r) (empty : d.lookahead = 0) :
    wr (some (.tab ds)) eofInsert h = .ok ((), setD h ds (eofInsert d)) ∧
      ContentBoundary (setD h ds (eofInsert d)) r ds z (eofInsert d) input origin base xs ∧
      EndFrontier (setD h ds (eofInsert d)) (eofInsert d) ∧
      StreamBuffers (setD h ds (eofInsert d)) r ∧ ConfigFrame d (eofInsert d) := by
  obtain ⟨run, stateA, endA, configA⟩ := eof_insert_content_boundary boundary frontier empty
  have owned := stream_owned_keys boundary.good stateA.good rfl rfl rfl rfl
  have buffersA := stream_buffers_private_read boundary.good.live.hz stateA.good.live.hz buffers
    (byte_frame_setD h ds (eofInsert d))
    (fun k equal => (stream_owned_deflate boundary.good k).mpr (Or.inl equal)) owned (stream_accounting_zero z) rfl
  exact ⟨run, stateA, endA, buffersA, configA⟩

/-- The actual FINISH macro and tail at memory four through nine retain
independent final-block meaning, all loop frontiers and exact output bits. -/
theorem memory_finish_tail_final_content_encoding_from_four {memory : Nat} {h : Heap} {r : ZStreamRef}
    {ds ob oo origin base : Nat} {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8}
    (boundary : ContentBoundary h r ds z d input origin base xs) (frontier : EndFrontier h d)
    (buffers : StreamBuffers h r) (positive : 0 < d.level.toInt)
    (pointer : z.next_out = .ref (.blk ob) oo) (cursor : d.pending_out = d.pending_buf)
    (allocation : d.lit_bufsize.toNat = 2 ^ (memory + 6)) (memoryLow : 4 ≤ memory) (memoryHigh : memory ≤ 9)
    (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7)
    (clear : BlockInit.BlockClear d) (available : d.match_available = 0) (wrap : d.wrap = 1)
    (startSmall : d.strstart.toNat < 65536) :
    ∃ produced after z' result before written remaining kind body padding,
      finish_tail (some (.tab ds)) Z_FINISH h = .ok ((if z'.avail_out == 0 then finish_started else finish_done), after) ∧
      ContentBoundary after r ds z' result input origin (base + represented xs) [] ∧ EndFrontier after result ∧
      StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧ BlockInit.BlockClear result ∧
      FlushWorkFrame {d with block_start := d.strstart.toUInt64.toInt64} result ∧
      result.bi_valid.toInt < 8 ∧ (0 < z'.avail_out.toNat → PublishReady result) ∧
      (result.pending = 0 → result.pending_out = result.pending_buf) ∧
      result.bi_valid.toInt.toNat = 0 ∧ PendingBits h d before ∧ Bytes after z.next_out produced written ∧
      PendingBits after result remaining ∧ kind < 3 ∧ padding.length < 8 ∧ (kind = 0 → padding = []) ∧
      ZlibF.Spec.bytesToBits written ++ remaining = before ++
        (Zlib.Trees.Proofs.Out.natBits 1 1 ++ Zlib.Trees.Proofs.Out.natBits kind 2 ++ body ++ padding) ∧
      ∀ suffix : List Bool, (kind = 0 → suffix.length % 8 = 0) →
        ZlibF.Spec.Body [] kind (inputPrefix input base) (body ++ suffix) suffix
          (inputPrefix input (base + represented xs)) := by
  obtain ⟨produced, after, z', result, before, written, remaining, kind, body, padding,
      macroRun, stateA, endA, buffersA, accountA, clearA, frameA, lowA, phaseA, cursorA,
      pendingBefore, bytesA, pendingA, kindA, padBound, _padNone, storedPad, wire, grammar⟩ :=
    memory_flush_macro_content_encoding_from_four boundary frontier buffers positive pointer cursor allocation memoryLow memoryHigh
      pending bits clear available startSmall true
  obtain ⟨pb, buf, trees, ledger, balance⟩ := boundary.symbols
  obtain ⟨w, window, win, get, view, _form⟩ := boundary.data
  have balance0 : BlockBalance d xs 0 := by simpa only [deferredCredit, available, ite_true] using balance
  have account0 : base + represented xs = origin + d.strstart.toNat := by
    simpa only [pendingCredit, available, ite_true, Nat.add_zero] using boundary.accounted
  obtain ⟨_pc, other, _zc, otherD, _wc, _rc, _kc, _body, _pad, otherRun, otherGood,
      _buffers, _account, _sizes, _storage, _clear, _frequencies, _count, _frame,
      _cursor, _phase, _position, _low, _bytes, _pending, _drained, final, _rest⟩ :=
    memory_flush_block_only_publish_from_four boundary.good trees buffers positive pointer cursor allocation memoryLow memoryHigh
      pending bits ledger clear boundary.trace win get boundary.range (fun _ => startSmall) balance0 account0 view true
  have heaps : other = after := (Prod.mk.inj (Except.ok.inj (otherRun.symm.trans macroRun))).2
  rw [heaps] at otherGood
  have states : otherD = result := Option.some.inj (otherGood.live.hs.symm.trans stateA.good.live.hs)
  rw [states] at final
  have wrapA : result.wrap = 1 := by rw [frameA]; exact wrap
  have run1 : FLUSH_BLOCK_ONLY (some (.tab ds)) 1 h = .ok ((), after) := macroRun
  have control : FLUSH_BLOCK (some (.tab ds)) 1 h =
      .ok ((if z'.avail_out == 0 then some finish_started else none), after) := by
    unfold FLUSH_BLOCK
    simp only [bind_app, run1, ldDeflateState_tab stateA.good.live.hs,
      stateA.good.live.back, zrd_eq, stateA.good.live.hz]
    by_cases empty : (z'.avail_out == 0) = true <;> simp [empty, pure_app, wrapA]
  refine ⟨produced, after, z', result, before, written, remaining, kind, body, padding,
    ?_, stateA, endA, buffersA, accountA, clearA, frameA, lowA, phaseA, cursorA, final rfl,
    pendingBefore, bytesA, pendingA, kindA, padBound, storedPad, wire, grammar⟩
  unfold finish_tail
  simp only [beq_self_eq_true, ite_true, bind_app, control]
  by_cases empty : (z'.avail_out == 0) = true <;> simp [empty, pure_app]

end Zlib.Deflate.Engine.Proofs
#print axioms Zlib.Deflate.Engine.Proofs.memory_eof_insert_content_buffers_from_four
#print axioms Zlib.Deflate.Engine.Proofs.memory_finish_tail_final_content_encoding_from_four
