import ZlibF.Proof.«deflate.c.engine.search-boundary»

/-! # Every positive-lookahead deferred-byte decision restores the boundary -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- The real no-symbol decision consumes one byte and preserves both
pending insertion and the earlier EOF frontier. It requires one input
byte; a retained next hash is needed only if three bytes remain. -/
theorem slow_defer_search_boundary {h : Heap} {r : ZStreamRef} {ds w origin base : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8} {xs : List Symbol} {input : Nat → UInt8}
    (cut : SearchBoundary h r ds z d input origin base xs w wa)
    (buffers : StreamBuffers h r) (positive : 1 ≤ d.lookahead.toNat)
    (branch : (d.prev_length ≥ MIN_MATCH_u && d.match_length ≤ d.prev_length) = false)
    (available : d.match_available = 0) (strict : d.sym_next.toNat < d.sym_end.toNat)
    (flush : Int32) (st : LoopS) (candidate : UInt32) :
    ∃ after result,
      slowDecision (some (.tab ds)) flush st candidate h =
        .ok ({ st with hash_head := candidate, bflush := false }, after) ∧
      ContentBoundary after r ds z result input origin base xs ∧ EndFrontier after result ∧
      StreamBuffers after r ∧ SlowRecordFrame d result ∧
      result.strstart.toNat = d.strstart.toNat + 1 ∧
      result.lookahead.toNat = d.lookahead.toNat - 1 ∧ fillEnd result = fillEnd d ∧
      result.sym_next.toNat < result.sym_end.toNat ∧ ByteFrame h after (DeflateOwned ds d) := by
  let result := deferOne d
  let after := setD h ds result
  have counts := advance_one_counts cut.good.inv cut.range positive
  have kept := defer_one_good cut.good cut.frontier cut.range positive
  have endKept := (defer_one_good cut.good cut.end_frontier cut.range positive).2.1
  have symbolic := slow_defer_symbol_boundary cut.good cut.symbols cut.frontier cut.range positive branch available flush st candidate
  have startA : result.strstart.toNat = d.strstart.toNat + 1 := counts.1
  have lookA : result.lookahead.toNat = d.lookahead.toNat - 1 := counts.2.1
  have endpoint : fillEnd result = fillEnd d := counts.2.2
  have insertA : result.insert = d.insert := rfl
  have frontierA : HeapChains after result (result.strstart.toNat - result.insert.toNat) := by
    simpa only [startA, insertA] using kept.2.1
  have chainsA : HeapChains after result result.strstart.toNat :=
    heap_chains_raise frontierA (Nat.sub_le _ _)
  have endA : EndFrontier after result := by
    unfold EndFrontier
    simpa only [startA, endpoint] using endKept
  have matching : 3 ≤ d.match_length.toNat →
      GoodMatch wa d.strstart.toNat d.w_size.toNat d.match_start.toNat d.match_length.toNat := by
    intro large
    exact cut.matching large (literal_search_improves branch large)
  have windowHistory := window_lazy_history_defer_bounded cut.good.inv cut.range positive cut.length cut.clipped matching
  have historyA : LazyHistory input origin result := window_history_logical windowHistory (by
    intro i fit
    change i < fillEnd result at fit
    rw [endpoint] at fit
    exact cut.view i fit)
  have goodA : DGood after r ds z result := kept.1
  have owned := stream_owned_keys cut.good goodA rfl rfl rfl rfl
  have storage := (byte_frame_setD h ds result).weaken (fun _ equal => Or.inl equal :
    ∀ k, k = ds → DeflateOwned ds d k)
  have buffersA := stream_buffers_private_read cut.good.live.hz goodA.live.hz buffers storage
    (fun k own => (stream_owned_deflate cut.good k).mpr own) owned (stream_accounting_zero z) rfl
  refine ⟨after, result, symbolic.1, ?_, endA, buffersA, symbolic.2.2,
    startA, lookA, endpoint, strict, storage⟩
  refine ⟨⟨⟨goodA, chainsA, kept.2.2, historyA, ?_, symbolic.2.1, ?_⟩,
    ?_, frontierA, ?_⟩, cut.trace, ?_⟩
  · intro _; rw [startA]; omega
  · refine ⟨w, wa, cut.window, cut.bytes, ?_, ?_⟩
    · intro i fit; rw [endpoint] at fit; exact cut.view i fit
    · intro enough
      change InsHForm d.hash_shift d.hash_mask (bfn wa) result.strstart.toNat d.ins_h
      rw [startA]
      apply cut.primed
      change 3 ≤ result.lookahead.toNat at enough
      rw [lookA] at enough
      omega
  · change d.insert.toNat ≤ result.strstart.toNat
    rw [startA]
    have bound := cut.insert_le
    omega
  · intro enough
    change d.insert = 0
    apply cut.ready
    change 3 ≤ result.lookahead.toNat at enough
    rw [lookA] at enough
    omega
  · have accounted : base + represented xs = origin + d.strstart.toNat := by
      simpa only [pendingCredit, available, ite_true, Nat.add_zero] using cut.accounted
    change base + represented xs + 1 = origin + result.strstart.toNat
    rw [startA]
    omega

end Zlib.Deflate.Engine.Proofs
