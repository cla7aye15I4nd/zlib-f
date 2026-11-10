import ZlibF.Proof.«inflate.c.whole-epoch-dictionary-source-invariant»
namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs
set_option autoImplicit false

/-- Non-DICT requests refuse before reading bytes, retaining exact routing. -/
theorem SourceInvariant.dictionary_non_dict_refused
    {h : Heap} {r : ZStreamRef} {log : DataLog}
    (before : SourceInvariant h r log) (source : BPtr) (len : UInt32)
    (mode : before.core.source.point.state.mode ≠ DICT) :
    C.run (inflateSetDictionary (some r) source len) h = .ok (Z_STREAM_ERROR, h) ∧
      Nonempty (SourceInvariant h r log) := by
  exact ⟨inflateSetDictionary_refused_any before.core.source.point.good.live source len
    (Or.inr ⟨by rw [before.core.wrapperOrigins.wrapped]; decide, mode⟩), ⟨before⟩⟩

/-- The proved actual setter produces a return for every supplied byte
view. Its observed transition keeps the complete v4 invariant whenever
that return is admitted by the unchanged dictionary handshake protocol. -/
theorem SourceInvariant.dictionary_run
    {h : Heap} {r : ZStreamRef} {log : DataLog} {pending : Bool}
    {source : BPtr} {len : UInt32} {bytes : List UInt8}
    (before : SourceInvariant h r log)
    (trace : InflateProtocolTrace 15 r h log pending) (scope : ProtocolWindow.PlatformScope trace)
    (range : CallerRange h r source len.toNat false) (input : Bytes h source len.toNat bytes) :
    ∃ rc after, C.run (inflateSetDictionary (some r) source len) h = .ok (rc, after) ∧
      (rc ≠ Z_OK ∨ pending = true →
        Nonempty (SourceInvariant after r {log with dictionary := if rc = Z_OK then bytes else log.dictionary})) := by
  obtain ⟨rc, after, _state, actual, _current, _outcome⟩ :=
    inflateSetDictionary_source_frame before.core.origin before.core.allocator range input
  exact ⟨rc, after, actual, fun allowed => before.dictionary trace scope range input actual allowed⟩

#print axioms SourceInvariant.dictionary_non_dict_refused
#print axioms SourceInvariant.dictionary_run
end Zlib.Inflate.Proofs.WholeEpoch
