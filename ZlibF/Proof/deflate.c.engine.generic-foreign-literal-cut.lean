import ZlibF.Proof.«deflate.c.engine.generic-foreign-slow-literal-search»

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols ZlibF.Math.DeflateEncoding
set_option autoImplicit false

theorem default_foreign_literal_full_search_safety {h : Heap} {r : ZStreamRef} {ds w owner oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8} {xs : List Symbol} {input : Nat → UInt8}
    (cut : SearchBoundary h r ds z d input origin base xs w wa)
    (buffers : StreamBuffers h r) (lookahead : 1 ≤ d.lookahead.toNat)
    (branch : (d.prev_length ≥ MIN_MATCH_u && d.match_length ≤ d.prev_length) = false)
    (available : d.match_available ≠ 0) (full : d.sym_next.toNat + 3 = d.sym_end.toNat)
    (positive : 0 < d.level.toInt) (pointer : z.next_out = .ref (.dstate_depth owner) oo)
    (cursor : d.pending_out = d.pending_buf) (memory : d.lit_bufsize.toNat = 16384)
    (comparisonRoom : d.strstart.toNat+262≤d.window_size.toNat) (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7) (clear : BlockInit.BlockClear d)
    (flush : Int32) (st : LoopS) (candidate : UInt32) :
    ∃ produced after z' result,
      slowDecision (some (.tab ds)) flush st candidate h =
        .ok ((if z'.avail_out == 0 then { st with hash_head := candidate, bflush := true, ret := some need_more }
          else { st with hash_head := candidate, bflush := true }), after) ∧
      ContentBoundary after r ds z' result input origin (base + represented (xs ++ [emittedLiteral d wa])) [] ∧
      EndFrontier after result ∧ StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧
      BlockInit.BlockClear result ∧ result.strstart.toNat = d.strstart.toNat + 1 ∧
      result.lookahead.toNat = d.lookahead.toNat - 1 ∧ fillEnd result = fillEnd d ∧
      result.sym_next.toNat < result.sym_end.toNat ∧ ConfigFrame d result ∧
      result.bi_valid.toInt < 8 ∧ (0 < z'.avail_out.toNat → PublishReady result) := by
  obtain ⟨produced,after,z',result,_before,_written,_remaining,_kind,_body,
    run,stateA,endA,buffersA,accountA,clearA,startA,lookA,endpoint,strictA,configA,lowA,phaseA,_rest⟩ :=
    default_foreign_slow_literal_full_search_boundary cut buffers lookahead branch available full positive pointer cursor
      memory comparisonRoom pending bits clear flush st candidate
  exact ⟨produced,after,z',result,run,stateA,endA,buffersA,accountA,clearA,startA,lookA,endpoint,strictA,configA,lowA,phaseA⟩

end Zlib.Deflate.Engine.Proofs
