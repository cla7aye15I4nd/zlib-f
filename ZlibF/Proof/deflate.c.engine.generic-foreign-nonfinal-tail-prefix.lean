import ZlibF.Proof.«deflate.c.engine.generic-foreign-nonfinal-control-frame»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-marker-private»
import ZlibF.Proof.«deflate.c.engine.nonfinal-tail-prefix»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols ZlibF.Math.DeflateEncoding
set_option autoImplicit false

/-- After deferred-byte settlement, the actual nonfinal EOF tail either
publishes its computed nonfinal block or skips an empty symbol buffer.
Both paths retain exact output and pending bits and an independently
composable prefix at the actual held-bit position. Public flush markers
are emitted later and are not assumed here. -/
theorem default_foreign_finish_tail_nonfinal_block_prefix {h : Heap} {r : ZStreamRef} {ds owner oo origin base offset : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8}
    (boundary : ContentBoundary h r ds z d input origin base xs) (frontier : EndFrontier h d)
    (buffers : StreamBuffers h r) (positive : 0 < d.level.toInt)
    (pointer : z.next_out = .ref (.dstate_depth owner) oo) (cursor : d.pending_out = d.pending_buf)
    (memory : d.lit_bufsize.toNat = 16384) (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7)
    (clear : BlockInit.BlockClear d) (available : d.match_available = 0)
    (position : offset % 8 = d.bi_valid.toInt.toNat % 8) (flush : Int32) (nonfinal : flush ≠ Z_FINISH) :
    ∃ produced ret after z' result before written remaining blockBits,
      finish_tail (some (.tab ds)) flush h = .ok (ret, after) ∧
      ContentBoundary after r ds z' result input origin (base + represented xs) [] ∧ EndFrontier after result ∧
      StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧ BlockInit.BlockClear result ∧
      ConfigFrame d result ∧ result.lookahead = d.lookahead ∧ result.strstart = d.strstart ∧
      result.match_available = 0 ∧ result.insert = d.insert ∧
      result.bi_valid.toInt < 8 ∧ (0 < z'.avail_out.toNat → PublishReady result) ∧
      PendingBits h d before ∧ Bytes after z.next_out produced written ∧ PendingBits after result remaining ∧
      ZlibF.Spec.bytesToBits written ++ remaining = before ++ blockBits ∧
      BlockPrefix [] offset (inputPrefix input base) blockBits (inputPrefix input (base + represented xs)) ∧
      (offset + blockBits.length) % 8 = result.bi_valid.toInt.toNat % 8 ∧
      (ret = need_more ∨ ret = block_done) ∧ (ret = need_more → z'.avail_out = 0) ∧ z'.adler=z.adler ∧ Shape h after ∧
      BufferFrame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) [⟨z.next_out,produced⟩] := by
  by_cases empty : d.sym_next = 0
  · obtain ⟨_pb, _buf, _trees, ledger, _balance⟩ := boundary.symbols
    have count := ledger.count
    rw [empty] at count
    have noSymbols : xs = [] := List.length_eq_zero_iff.mp (by simp only [UInt32.toNat_zero] at count; omega)
    subst xs
    obtain ⟨held, heldBytes⟩ := good_pending_bits boundary.good
    refine ⟨0, block_done, h, z, d, held, [], held, [], ?_, ?_, frontier, buffers,
      stream_accounting_zero z, clear, rfl, rfl, rfl, available, rfl, by omega,
      fun _ => ⟨pending, cursor, by omega⟩, heldBytes, caller_output_zero_slice boundary.good buffers,
      heldBytes, by simp [ZlibF.Spec.bytesToBits], ?_, ?_, Or.inr rfl, ?_,rfl,Shape.refl h,
      marker_private_buffer_frame boundary.good buffers pointer (full_storage_refl h _).2.1 (Shape.refl h)⟩
    · unfold finish_tail
      simp only [beq_eq_false_iff_ne.mpr nonfinal, Bool.false_eq_true, ite_false,
        bind_app, rdD_eq, boundary.good.live.hs, empty, bne_self_eq_false, pure_app]
    · simpa only [represented, Nat.add_zero] using boundary
    · simpa only [represented, Nat.add_zero] using block_prefix_empty ([] : List UInt8) (inputPrefix input base) offset
    · simpa only [List.length_nil, Nat.add_zero] using position
    · intro impossible
      exact False.elim ((by decide : block_done ≠ need_more) impossible)
  · obtain ⟨produced, after, z', result, before, written, remaining, kind, body,
        run, stateA, endA, buffersA, accountA, clearA, fields, lowA, readyA,
        beforeA, bytesA, pendingA, _kindA, _storedA, positionA, wireA, meaningA⟩ :=
      default_foreign_flush_nonfinal_end_block_prefix boundary frontier buffers positive pointer cursor memory pending bits clear available position
    obtain ⟨adlerA,shapeA,preciseA⟩ := default_foreign_nonfinal_control_run_frame boundary buffers positive pointer cursor memory pending bits clear available
      run stateA.good.live.hz accountA
    refine ⟨produced, if z'.avail_out == 0 then need_more else block_done, after, z', result,
      before, written, remaining, Zlib.Trees.Proofs.Out.natBits 0 1 ++ Zlib.Trees.Proofs.Out.natBits kind 2 ++ body,
      ?_, stateA, endA, buffersA, accountA, clearA, ?_, ?_, ?_, ?_, ?_, lowA, readyA,
      beforeA, bytesA, pendingA, wireA, meaningA, ?_, ?_, ?_,adlerA,shapeA,preciseA⟩
    · unfold finish_tail
      simp only [beq_eq_false_iff_ne.mpr nonfinal, Bool.false_eq_true, ite_false,
        bind_app, rdD_eq, boundary.good.live.hs, bne_iff_ne.mpr empty, ite_true, run]
      by_cases exhausted : (z'.avail_out == 0) = true <;> simp [exhausted, pure_app]
    · rw [fields]; rfl
    · rw [fields]
    · rw [fields]
    · rw [fields]; exact available
    · rw [fields]
    · simp only [List.length_append, Zlib.Trees.Proofs.Out.natBits_length]
      omega
    · by_cases exhausted : (z'.avail_out == 0) = true <;> simp [exhausted]
    · by_cases exhausted : (z'.avail_out == 0) = true
      · exact fun _ => beq_iff_eq.mp exhausted
      · simp [exhausted, show block_done ≠ need_more from by decide]

end Zlib.Deflate.Engine.Proofs
