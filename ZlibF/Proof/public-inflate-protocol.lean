import ZlibF.Spec.Public.Sequences
import ZlibF.Spec.Functional.Sequences

/-!
The functional protocol records the same actual calls as the broad data
history. Erasure retains all source executions and buffer observations.
-/

namespace ZlibF.Spec.Public
open C ZlibF.Spec
set_option autoImplicit false

theorem InflateProtocolTrace.erase {wb : Int32} {r : ZStreamRef} {h : Heap} {log : DataLog} {pending : Bool}
    (trace : InflateProtocolTrace wb r h log pending) : InflateDataTrace wb r h log := by
  induction trace with
  | init domain run => exact .init domain run
  | caller _ rebound platform ih => exact .caller ih rebound platform
  | step _ platform observation ih => exact .step ih platform observation
  | dictionary _ platform arguments bytes run _ ih => exact .dictionary ih platform arguments bytes run

theorem AllowedInflateProtocol.erase {wb : Int32} {r : ZStreamRef} {h : Heap} {log : DataLog}
    (trace : AllowedInflateProtocol wb r h log) : InflateDataTrace wb r h log := by
  exact trace.choose_spec.erase

/-- Every raw data history remains admitted, including repeated dictionary
amendments and all actual refused requests. -/
theorem InflateDataTrace.raw_protocol {wb : Int32} {r : ZStreamRef} {h : Heap} {log : DataLog}
    (raw : wb.toInt < 0) (trace : InflateDataTrace wb r h log) :
    AllowedInflateProtocol wb r h log := by
  induction trace with
  | init domain run => exact ⟨false, .init domain run⟩
  | caller _ rebound platform ih =>
    obtain ⟨pending, previous⟩ := ih
    exact ⟨pending, .caller previous rebound platform⟩
  | step _ platform observation ih =>
    obtain ⟨pending, previous⟩ := ih
    exact ⟨_, .step previous platform observation⟩
  | dictionary _ platform arguments bytes run ih =>
    obtain ⟨pending, previous⟩ := ih
    exact ⟨_, .dictionary previous platform arguments bytes run (Or.inl raw)⟩

/-- A failed setter remains admitted at any protocol stage. It does not
consume a pending request, so a checksum refusal permits a retry. -/
theorem InflateProtocolTrace.dictionary_refused
    {wb : Int32} {r : ZStreamRef} {h after : Heap} {log : DataLog} {pending : Bool}
    {p : BPtr} {n : UInt32} {bytes : List UInt8} {rc : Int32}
    (trace : InflateProtocolTrace wb r h log pending) (platform : ZlibF.PlatformMemory.ByteObjectsFit h)
    (arguments : StreamArguments h r (.inflateSetDictionary (some r) p n))
    (input : Bytes h p n.toNat bytes)
    (run : C.run (Zlib.Inflate.inflateSetDictionary (some r) p n) h = .ok (rc, after))
    (refused : rc ≠ Z_OK) : InflateProtocolTrace wb r after log pending := by
  have result := InflateProtocolTrace.dictionary trace platform arguments input run (Or.inr (Or.inl refused))
  simpa [refused] using result

#print axioms InflateProtocolTrace.erase
#print axioms AllowedInflateProtocol.erase
#print axioms InflateDataTrace.raw_protocol
#print axioms InflateProtocolTrace.dictionary_refused
end ZlibF.Spec.Public
