import ZlibF.Proof.«deflate.c.engine.match-full-encoding»
import ZlibF.Proof.«deflate.c.engine.match-nonfull-encoding»

/-! # Every actual selected match decision retains its complete encoding alternative -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Every actual selected match decision retains both loop frontiers,
its input ledger and its exact output bits. Nonfull tallies keep all bits
and extend the symbol ledger. Full tallies emit the actual independently
decoded block and restore an empty ledger. Covers all initialized remaining
input lengths and every real coding/output-capacity choice. -/
theorem slow_match_search_encoding {h : Heap} {r : ZStreamRef} {ds w ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8} {xs : List Symbol} {input : Nat → UInt8}
    (cut : SearchBoundary h r ds z d input origin base xs w wa)
    (buffers : StreamBuffers h r)
    (selected : (d.prev_length ≥ MIN_MATCH_u && d.match_length ≤ d.prev_length) = true)
    (strict : d.sym_next.toNat < d.sym_end.toNat)
    (positive : 0 < d.level.toInt) (pointer : z.next_out = .ref (.blk ob) oo)
    (cursor : d.pending_out = d.pending_buf) (memory : d.lit_bufsize.toNat = 16384)
    (pending : d.pending = 0) (bits : d.bi_valid.toInt < 8) (clear : BlockInit.BlockClear d)
    (flush : Int32) (st : LoopS) (hash_head : UInt32) :
    ∃ produced head after z' result base' ys before written remaining,
      slowDecision (some (.tab ds)) flush st hash_head h =
        .ok ((if d.sym_next + 3 == d.sym_end then
          if z'.avail_out == 0 then { st with hash_head := head, bflush := true, ret := some need_more }
          else { st with hash_head := head, bflush := true }
          else { st with hash_head := head, bflush := false }), after) ∧
      ContentBoundary after r ds z' result input origin base' ys ∧ EndFrontier after result ∧
      StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧ written.length = produced ∧
      BlockInit.BlockClear result ∧ result.strstart.toNat = d.strstart.toNat + (d.prev_length.toNat - 1) ∧
      result.lookahead.toNat = d.lookahead.toNat - (d.prev_length.toNat - 1) ∧ fillEnd result = fillEnd d ∧
      result.sym_next.toNat < result.sym_end.toNat ∧ base ≤ base' ∧ ConfigFrame d result ∧
      result.bi_valid.toInt < 8 ∧ (0 < z'.avail_out.toNat → PublishReady result) ∧
      PendingBits h d before ∧ Bytes after z.next_out produced written ∧ PendingBits after result remaining ∧
      (((d.sym_next + 3 == d.sym_end) = false ∧ z' = z ∧ produced = 0 ∧ written = [] ∧
        remaining = before ∧ base' = base ∧ ys = xs ++ [emittedMatch d]) ∨
       ((d.sym_next + 3 == d.sym_end) = true ∧ base' = base + represented (xs ++ [emittedMatch d]) ∧ ys = [] ∧
        ∃ kind body, kind < 3 ∧ ZlibF.Spec.bytesToBits written ++ remaining = before ++
          (Zlib.Trees.Proofs.Out.natBits 0 1 ++ Zlib.Trees.Proofs.Out.natBits kind 2 ++ body) ∧
          ∀ suffix : List Bool, (kind = 0 → suffix.length % 8 = 0) →
            ZlibF.Spec.Body [] kind (inputPrefix input base) (body ++ suffix) suffix
              (inputPrefix input (base + represented (xs ++ [emittedMatch d]))))) := by
  by_cases full : (d.sym_next + 3 == d.sym_end) = true
  · obtain ⟨produced, head, after, z', result, before, written, remaining, kind, body,
      run, boundaryA, endA, buffersA, accountA, clearA, startA, lookA, endpoint,
      strictA, configA, lowA, phaseA, pendingBefore, bytesA, pendingAfter,
      kindA, outputA, grammarA⟩ :=
      slow_match_full_search_encoding cut buffers selected strict full positive pointer cursor memory pending
        (by omega) clear flush st hash_head
    refine ⟨produced, head, after, z', result, base + represented (xs ++ [emittedMatch d]), [],
      before, written, remaining, ?_, boundaryA, endA, buffersA, accountA, public_bytes_length bytesA,
      clearA, startA, lookA, endpoint, strictA, Nat.le_add_right _ _, configA,
      lowA, phaseA, pendingBefore, bytesA, pendingAfter, ?_⟩
    · simpa only [full, ite_true] using run
    · exact Or.inr ⟨full, rfl, rfl, kind, body, kindA, outputA, grammarA⟩
  · have nonfull : (d.sym_next + 3 == d.sym_end) = false := Bool.eq_false_iff.mpr full
    obtain ⟨head, after, result, before, run, boundaryA, endA, buffersA, accountA,
      clearA, startA, lookA, endpoint, strictA, configA, lowA, readyA,
      pendingBefore, bytesA, pendingAfter⟩ :=
      slow_match_nonfull_search_encoding cut buffers selected strict nonfull pointer cursor pending bits clear flush st hash_head
    refine ⟨0, head, after, z, result, base, xs ++ [emittedMatch d], before, [], before,
      ?_, boundaryA, endA, buffersA, accountA, rfl, clearA, startA, lookA, endpoint,
      strictA, Nat.le_refl _, configA, lowA, fun _ => readyA, pendingBefore, bytesA, pendingAfter, ?_⟩
    · simpa only [nonfull, Bool.false_eq_true, ite_false] using run
    · exact Or.inl ⟨nonfull, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Zlib.Deflate.Engine.Proofs
