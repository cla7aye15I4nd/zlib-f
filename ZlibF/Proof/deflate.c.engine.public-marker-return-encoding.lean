import ZlibF.Proof.«deflate.c.engine.marker-raw-checksum»
import ZlibF.Proof.«deflate.c.engine.partial-sync-marker-endpoint»
import ZlibF.Proof.«deflate.c.engine.full-marker-endpoint»
import ZlibF.Proof.«deflate.c.engine.partial-sync-return»
import ZlibF.Proof.«deflate.c.engine.full-flush-return»
import ZlibF.Proof.«deflate.c.engine.partial-sync-effects»
import ZlibF.Proof.«deflate.c.engine.full-flush-effects»
import ZlibF.Proof.«deflate.c.engine.input-snapshot-controls»
import ZlibF.Proof.«deflate.c.engine.public-no-flush-encoding»

/-! # Actual marker returns retain cumulative encoding and the input endpoint -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
open Zlib.Trees.Proofs.Out (TreesInvAt)
set_option autoImplicit false

/-- The actual PARTIAL/SYNC block-done return includes marker emission,
pending publication and the output-exhaustion retry store. All capacities
retain exact final-heap output, cumulative encoding and Adler, the logical
input endpoint and the caller interval needed to append earlier output. -/
theorem public_strategy_partial_sync_done_raw_encoding {h : Heap} {r : ZStreamRef} {ds pb ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8} {input : Nat → UInt8} {config : EngineConfig}
    {published : List UInt8}
    (boundary : BufferedBoundary h r ds z d input origin base [] config)
    (buffers : StreamBuffers h r) (trees : TreesInvAt h ds d pb buf)
    (pointer : z.next_out = .ref (.blk ob) oo) (publish : PublishReady d)
    (flush : Int32) (flag : flush = Z_PARTIAL_FLUSH ∨ flush = Z_SYNC_FLUSH)
    (encoding : RawPrefix h d input base published) :
    ∃ produced after z' result written,
      publicStrategyReturn (some r) (some (.tab ds)) flush block_done h = .ok (Z_OK, after) ∧
      BufferedBoundary after r ds z' result input origin base [] config ∧ StreamBuffers after r ∧
      StreamAccounting z z' 0 produced ∧ Bytes after z.next_out produced written ∧
      RawPrefix after result input base (published ++ written) ∧ ConfigFrame d result ∧
      result.status = d.status ∧ (result.last_flush = d.last_flush ∨ result.last_flush = -1) ∧
      z'.adler = z.adler ∧ fillEnd result = fillEnd d ∧ result.match_available = d.match_available ∧
      RawOutputInterval h after ob oo produced := by
  have room : 8 ≤ buf.size := by have size := trees.base.size; have lower := trees.base.lit_lo; omega
  obtain ⟨produced, middle, z', result, written, run, stateA, buffersA, accountA, bytesA,
      encodingA, configA, statusA, lastA, _readyA, adlerA⟩ :=
    empty_partial_sync_publish_raw_prefix_adler boundary buffers trees pointer publish room flush flag encoding
  obtain ⟨_count, other, _otherZ, otherD, _written, _remaining, actual, stateOther, _buffers,
      _account, _sizes, _storage, _config, _status, _last, _ready, _bytes, _pending, _wire,
      _adler, endpointA, availableA⟩ :=
    empty_partial_sync_publish_adler_endpoint boundary buffers trees pointer publish room flush flag
  have heaps : other = middle := (Prod.mk.inj (Except.ok.inj (actual.symm.trans run))).2
  rw [heaps] at stateOther
  have states : otherD = result := Option.some.inj (stateOther.good.live.hs.symm.trans stateA.good.live.hs)
  rw [states] at endpointA availableA
  obtain ⟨_amount, _next, _nextZ, _nextD, effectRun, effectGood, _effectBuffers, effectAccount,
      _inputEffect, _outputEffect, outputEffect, _storageEffect⟩ :=
    partial_sync_publication_effects boundary.good trees buffers pointer publish flush flag
  have interval : RawOutputInterval h middle ob oo produced :=
    RawOutputInterval.identify effectRun run effectGood.live.hz stateA.good.live.hz effectAccount accountA outputEffect
  have source : publicStrategyReturn (some r) (some (.tab ds)) flush block_done h =
      (if z'.avail_out == 0 then .ok (Z_OK, setD middle ds {result with last_flush := -1}) else .ok (Z_OK, middle)) := by
    rw [public_strategy_partial_sync_source _ _ flush flag, bind_app, run]
    simp only [bind_app, zrd_eq, stateA.good.live.hz]
    split <;> simp only [wrD_eq, stateA.good.live.hs, bind_app, pure_app]
  by_cases exhausted : (z'.avail_out == 0) = true
  · have bytesF := caller_bytes_setD_depth (result := {result with last_flush := -1}) stateA.good.live.hs rfl bytesA
    have intervalF : RawOutputInterval middle (setD middle ds {result with last_flush := -1}) ob (oo + produced) 0 := .of_same rfl
    refine ⟨produced, _, z', _, written, by simpa only [exhausted, ite_true] using source,
      last_flush_buffered_boundary stateA (-1), last_flush_buffers stateA.good buffersA (-1), accountA,
      bytesF, encodingA.last_flush stateA.good (-1), configA.trans (by rfl), statusA, Or.inr rfl,
      adlerA, endpointA, availableA, ?_⟩
    simpa only [Nat.add_zero] using interval.trans intervalF
  · exact ⟨produced, middle, z', result, written,
      by simpa only [exhausted, Bool.false_eq_true, ite_false] using source,
      stateA, buffersA, accountA, bytesA, encodingA, configA, statusA, Or.inl lastA, adlerA,
      endpointA, availableA, interval⟩

/-- The actual FULL block-done return includes hash clearing, position
reset and every pending-output capacity. Its new origin is the global
logical base. Cumulative raw meaning, Adler and exact output survive both
ordinary and retry returns; no earlier input history is discarded. -/
theorem public_strategy_full_done_raw_encoding {h : Heap} {r : ZStreamRef} {ds pb ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8} {input : Nat → UInt8} {config : EngineConfig}
    {published : List UInt8}
    (boundary : BufferedBoundary h r ds z d input origin base [] config)
    (buffers : StreamBuffers h r) (trees : TreesInvAt h ds d pb buf)
    (pointer : z.next_out = .ref (.blk ob) oo) (publish : PublishReady d)
    (look : d.lookahead = 0) (available : d.match_available = 0)
    (encoding : RawPrefix h d input base published) :
    ∃ produced after z' result written,
      publicStrategyReturn (some r) (some (.tab ds)) Z_FULL_FLUSH block_done h = .ok (Z_OK, after) ∧
      BufferedBoundary after r ds z' result input base base [] config ∧ StreamBuffers after r ∧
      StreamAccounting z z' 0 produced ∧ Bytes after z.next_out produced written ∧
      RawPrefix after result input base (published ++ written) ∧ ConfigFrame d result ∧
      result.status = d.status ∧ (result.last_flush = d.last_flush ∨ result.last_flush = -1) ∧
      z'.adler = z.adler ∧ fillEnd result = 0 ∧ result.match_available = 0 ∧
      RawOutputInterval h after ob oo produced := by
  obtain ⟨produced, middle, z', result, written, run, stateA, buffersA, accountA, bytesA,
      encodingA, configA, statusA, lastA, adlerA⟩ :=
    empty_full_marker_publish_raw_prefix_adler boundary buffers trees pointer publish look available encoding
  obtain ⟨_count, other, _otherZ, otherD, _written, _remaining, actual, stateOther, _buffers,
      _account, _config, _status, _last, _bytes, _pending, _wire, _adler, endpointA, availableA⟩ :=
    empty_full_marker_publish_adler_endpoint boundary buffers trees pointer publish look available
  have heaps : other = middle := (Prod.mk.inj (Except.ok.inj (actual.symm.trans run))).2
  rw [heaps] at stateOther
  have states : otherD = result := Option.some.inj (stateOther.good.live.hs.symm.trans stateA.good.live.hs)
  rw [states] at endpointA availableA
  obtain ⟨_amount, _next, _nextZ, _nextD, effectRun, effectGood, _effectBuffers, effectAccount,
      _inputEffect, _outputEffect, outputEffect, _storageEffect⟩ :=
    full_publication_effects boundary buffers trees pointer publish look available
  have interval : RawOutputInterval h middle ob oo produced :=
    RawOutputInterval.identify effectRun run effectGood.live.hz stateA.good.live.hz effectAccount accountA outputEffect
  have source : publicStrategyReturn (some r) (some (.tab ds)) Z_FULL_FLUSH block_done h =
      (if z'.avail_out == 0 then .ok (Z_OK, setD middle ds {result with last_flush := -1}) else .ok (Z_OK, middle)) := by
    rw [public_strategy_full_source, bind_app, run]
    simp only [bind_app, zrd_eq, stateA.good.live.hz]
    split <;> simp only [wrD_eq, stateA.good.live.hs, bind_app, pure_app]
  by_cases exhausted : (z'.avail_out == 0) = true
  · have bytesF := caller_bytes_setD_depth (result := {result with last_flush := -1}) stateA.good.live.hs rfl bytesA
    have intervalF : RawOutputInterval middle (setD middle ds {result with last_flush := -1}) ob (oo + produced) 0 := .of_same rfl
    refine ⟨produced, _, z', _, written, by simpa only [exhausted, ite_true] using source,
      last_flush_buffered_boundary stateA (-1), last_flush_buffers stateA.good buffersA (-1), accountA,
      bytesF, encodingA.last_flush stateA.good (-1), configA.trans (by rfl), statusA, Or.inr rfl,
      adlerA, endpointA, availableA, ?_⟩
    simpa only [Nat.add_zero] using interval.trans intervalF
  · exact ⟨produced, middle, z', result, written,
      by simpa only [exhausted, Bool.false_eq_true, ite_false] using source,
      stateA, buffersA, accountA, bytesA, encodingA, configA, statusA, Or.inl lastA, adlerA,
      endpointA, availableA, interval⟩

end Zlib.Deflate.Engine.Proofs
