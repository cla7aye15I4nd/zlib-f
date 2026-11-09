import ZlibF.Proof.«deflate.c.engine.generic-foreign-nonfinal-macro»

/-! # The actual nonfinal EOF tail, including an empty symbol buffer -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- After settling the deferred literal, a non-FINISH tail flushes exactly
when symbols remain. An empty symbol buffer returns block_done even at
zero output capacity. No final block or public marker is added here. -/
theorem default_foreign_finish_tail_nonfinal_boundary {h : Heap} {r : ZStreamRef} {ds owner oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8}
    (boundary : ContentBoundary h r ds z d input origin base xs)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r) (positive : 0 < d.level.toInt)
    (pointer : z.next_out = .ref (.dstate_depth owner) oo) (cursor : d.pending_out = d.pending_buf)
    (memory : d.lit_bufsize.toNat = 16384) (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7)
    (clear : BlockInit.BlockClear d) (available : d.match_available = 0)
    (flush : Int32) (nonfinal : flush ≠ Z_FINISH) :
    ∃ produced ret after z' result,
      finish_tail (some (.tab ds)) flush h = .ok (ret, after) ∧
      ContentBoundary after r ds z' result input origin (base + represented xs) [] ∧
      StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧ BlockInit.BlockClear result ∧
      ConfigFrame d result ∧ result.lookahead = d.lookahead ∧ result.strstart = d.strstart ∧
      result.match_available = 0 ∧ result.insert = d.insert ∧
      result.bi_valid.toInt < 8 ∧ (0 < z'.avail_out.toNat → PublishReady result) ∧
      (ret = need_more ∨ ret = block_done) ∧ (ret = need_more → z'.avail_out = 0) ∧ StrategyControls d result ∧ (ret=block_done → PublishReady result) := by
  by_cases empty : d.sym_next = 0
  · obtain ⟨pb, buf, trees, ledger, balance⟩ := boundary.symbols
    have count := ledger.count
    rw [empty] at count
    have noSymbols : xs = [] := List.length_eq_zero_iff.mp (by simp only [UInt32.toNat_zero] at count; omega)
    subst xs
    refine ⟨0, block_done, h, z, d, ?_, ?_, buffers, stream_accounting_zero z, clear,
      rfl, rfl, rfl, available, rfl, by omega, fun _ => ⟨pending, cursor, by omega⟩,
      Or.inr rfl, ?_,⟨fun _=>cursor,rfl,rfl⟩,fun _=>⟨pending,cursor,by omega⟩⟩
    · unfold finish_tail
      simp only [beq_eq_false_iff_ne.mpr nonfinal, Bool.false_eq_true, ite_false,
        bind_app, rdD_eq, boundary.good.live.hs, empty, bne_self_eq_false, pure_app]
    · simpa only [represented, Nat.add_zero] using boundary
    · intro impossible
      cases (show block_done ≠ need_more from by decide) impossible
  · obtain ⟨produced, after, z', result, run, stateA, buffersA, accountA, clearA, fields, lowA, readyA, controlsA⟩ :=
      default_foreign_flush_nonfinal_loop_boundary boundary frontier buffers positive pointer cursor memory pending bits clear available
    refine ⟨produced, if z'.avail_out == 0 then need_more else block_done, after, z', result,
      ?_, stateA, buffersA, accountA, clearA, ?_, ?_, ?_, ?_, ?_, lowA, readyA, ?_, ?_, controlsA, ?_⟩
    · unfold finish_tail
      simp only [beq_eq_false_iff_ne.mpr nonfinal, Bool.false_eq_true, ite_false,
        bind_app, rdD_eq, boundary.good.live.hs, bne_iff_ne.mpr empty, ite_true, run]
      by_cases exhausted : (z'.avail_out == 0) = true <;> simp [exhausted, pure_app]
    · rw [fields]; rfl
    · rw [fields]
    · rw [fields]
    · rw [fields]; exact available
    · rw [fields]
    · by_cases exhausted : (z'.avail_out == 0) = true <;> simp [exhausted]
    · by_cases exhausted : (z'.avail_out == 0) = true
      · exact fun _ => beq_iff_eq.mp exhausted
      · simp [exhausted, show block_done ≠ need_more from by decide]

    · intro done
      by_cases exhausted : (z'.avail_out==0)=true
      · simp only [exhausted,ite_true] at done
        cases done
      · apply readyA
        have nonzero : z'.avail_out.toNat≠0 := by
          intro zero
          have wordZero : z'.avail_out=0 := UInt32.toNat_inj.mp zero
          simp only [wordZero,BEq.rfl] at exhausted
          contradiction
        omega

end Zlib.Deflate.Engine.Proofs
