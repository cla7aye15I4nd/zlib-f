import ZlibF.Proof.«inflate.c.whole-epoch-dictionary-transition-v4»
namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs
set_option autoImplicit false

/-- Every wrapped non-DICT state refuses before reading source memory.
This includes the genuine unchecked MATCH and MEM public snapshots. -/
theorem Invariant4.dictionary_non_dict_refused
    {h : Heap} {r : ZStreamRef} {log : DataLog}
    (before : Invariant4 h r log) (source : BPtr) (len : UInt32)
    (mode : before.source.point.state.mode ≠ DICT) :
    C.run (inflateSetDictionary (some r) source len) h = .ok (Z_STREAM_ERROR, h) ∧
      Nonempty (Invariant4 h r log) := by
  exact ⟨inflateSetDictionary_refused_any before.source.point.good.live source len
    (Or.inr ⟨by rw [before.wrapperOrigins.wrapped]; decide, mode⟩), ⟨before⟩⟩

/-- The proved actual setter produces a return for every supplied byte
view. Its observed transition keeps the complete v4 invariant whenever
that return is admitted by the unchanged dictionary handshake protocol. -/
theorem Invariant4.dictionary_run
    {h : Heap} {r : ZStreamRef} {log : DataLog} {pending : Bool}
    {source : BPtr} {len : UInt32} {bytes : List UInt8}
    (before : Invariant4 h r log)
    (trace : InflateProtocolTrace 15 r h log pending) (scope : ProtocolWindow.PlatformScope trace)
    (range : CallerRange h r source len.toNat false) (input : Bytes h source len.toNat bytes) :
    ∃ rc after, C.run (inflateSetDictionary (some r) source len) h = .ok (rc, after) ∧
      (rc ≠ Z_OK ∨ pending = true →
        Nonempty (Invariant4 after r {log with dictionary := if rc = Z_OK then bytes else log.dictionary})) := by
  obtain ⟨rc, after, _state, actual, _current, _outcome⟩ :=
    inflateSetDictionary_source_frame before.origin before.allocator range input
  exact ⟨rc, after, actual, fun allowed => before.dictionary trace scope range input actual allowed⟩

#print axioms Invariant4.dictionary_non_dict_refused
#print axioms Invariant4.dictionary_run
end Zlib.Inflate.Proofs.WholeEpoch
