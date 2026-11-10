import ZlibF.Proof.«inflate.c.slow-copy-fragment-consumer»
namespace Zlib.Inflate.Proofs.SlowInputFragment
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs ZlibF.Math.LZ77History ZlibF.Math.LZ77Copy SlowMatchCompletion
set_option autoImplicit false

/-- Internal logical progress of a copy split across public output calls.
The byte equality is established by actual emission, not requested as a
public API precondition. -/
def LogicalCopyProgress {L D : List Nat} (p : CopySyntax L D)
    (dict original current : List UInt8) (s : InflateState) : Prop :=
  s.length.toNat ≤ lengthBases.getD (p.symbol - 257) 0 + p.lengthValue ∧
  current = copyBack dict (distBases.getD p.distanceSymbol 0 + p.distanceValue)
    (lengthBases.getD (p.symbol - 257) 0 + p.lengthValue - s.length.toNat) original

/-- The exact actual byte prefix and remaining-length balance establish
logical progress for a newly parsed copy token. -/
theorem logical_progress_of_prefix {L D : List Nat} {p : CopySyntax L D}
    {dict original current : List UInt8} {s : InflateState} {made : Nat}
    (balance : s.length.toNat + made = lengthBases.getD (p.symbol - 257) 0 + p.lengthValue)
    (bytes : current = copyBack dict (distBases.getD p.distanceSymbol 0 + p.distanceValue) made original) :
    LogicalCopyProgress p dict original current s := by
  refine ⟨by omega, ?_⟩
  have count : lengthBases.getD (p.symbol - 257) 0 + p.lengthValue - s.length.toNat = made := by omega
  rw [count]
  exact bytes

/-- An additional actual fragment advances the original copy ghost by
its exact emitted amount, even after a public call changed the window. -/
theorem logical_progress_append {L D : List Nat} {p : CopySyntax L D}
    {dict original current next : List UInt8} {s state : InflateState} {made : Nat}
    (prior : LogicalCopyProgress p dict original current s)
    (balance : state.length.toNat + made = s.length.toNat)
    (bytes : next = copyBack dict (distBases.getD p.distanceSymbol 0 + p.distanceValue) made current) :
    LogicalCopyProgress p dict original next state := by
  refine ⟨by have := prior.1; omega, ?_⟩
  rw [bytes, prior.2, ← copy_back_compose]
  have count : lengthBases.getD (p.symbol - 257) 0 + p.lengthValue - s.length.toNat + made =
      lengthBases.getD (p.symbol - 257) 0 + p.lengthValue - state.length.toNat := by have := prior.1; omega
  rw [count]

/-- Completing the original token supplies exactly the original Symbols
copy constructor and its untouched continuation. -/
theorem logical_progress_completed_symbols {L D : List Nat} {p : CopySyntax L D}
    {dict original current final : List UInt8} {s : InflateState} {tail : List Bool}
    (progress : LogicalCopyProgress p dict original current s) (done : s.length = 0)
    (validDistance : distBases.getD p.distanceSymbol 0 + p.distanceValue ≤ (dict ++ original).length)
    (continuation : Symbols L D dict current p.rest tail final) :
    Symbols L D dict original p.input tail final := by
  have currentEq := progress.2
  rw [done, UInt32.toNat_zero, Nat.sub_zero] at currentEq
  rw [currentEq] at continuation
  exact Symbols.copy p.lengthDecode p.lengthLower p.lengthUpper p.lengthRead p.distanceDecode
    p.distanceUpper p.distanceRead (by simpa only [Nat.add_comm] using validDistance) continuation

/-- Retained-window emission from the actual protocol reconstructs the
full independent output history and therefore composes with Symbols. -/
theorem protocol_completed_symbols {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {log : DataLog} {L D : List Nat} (p : CopySyntax L D)
    (allowed : AllowedInflateProtocol 15 r h log) (scope : ProtocolWindow.PlatformScope allowed.choose_spec)
    (good : Good h r zs z s) (active : s.mode < CHECK)
    (current after : List UInt8) {tail : List Bool} {final : List UInt8}
    (validDistance : distBases.getD p.distanceSymbol 0 + p.distanceValue ≤ (log.dictionary ++ log.output ++ current).length)
    (bytes : after = copyBack ((log.dictionary ++ log.output).drop ((log.dictionary ++ log.output).length - 32768))
      (distBases.getD p.distanceSymbol 0 + p.distanceValue)
      (lengthBases.getD (p.symbol - 257) 0 + p.lengthValue) current)
    (continuation : Symbols L D log.dictionary (log.output ++ after) p.rest tail final) :
    Symbols L D log.dictionary (log.output ++ current) p.input tail final := by
  obtain ⟨_physical, _available, agreed⟩ := protocol_copy_history p allowed scope good active current
    (lengthBases.getD (p.symbol - 257) 0 + p.lengthValue) validDistance
  rw [bytes, ← agreed] at continuation
  exact Symbols.copy p.lengthDecode p.lengthLower p.lengthUpper p.lengthRead p.distanceDecode
    p.distanceUpper p.distanceRead (by simpa only [List.append_assoc, Nat.add_comm] using validDistance) continuation

#print axioms logical_progress_of_prefix
#print axioms logical_progress_append
#print axioms logical_progress_completed_symbols
#print axioms protocol_completed_symbols
end Zlib.Inflate.Proofs.SlowInputFragment
