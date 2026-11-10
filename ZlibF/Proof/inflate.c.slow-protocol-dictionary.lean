import ZlibF.Proof.«inflate.c.slow-input-fragment»
import ZlibF.Proof.«inflate.c.slow-distance-extra-semantic»
import ZlibF.Proof.«inflate.c.protocol-window-history»
import ZlibF.Math.LZ77History
namespace Zlib.Inflate.Proofs.SlowInputFragment
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs ZlibF.Math.LZ77History SlowExtraSemanticPath
set_option autoImplicit false

/-- The actual admitted protocol identifies this same live state and its
exact retained logical dictionary. No initial decoder invariant or saved
window meaning is assumed; both come from the real trace producer. -/
theorem protocol_saved_dictionary {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {log : DataLog}
    (allowed : AllowedInflateProtocol 15 r h log)
    (scope : ProtocolWindow.PlatformScope allowed.choose_spec)
    (good : Good h r zs z s) (active : s.mode < CHECK) :
    DefaultStateJ h r zs z s ∧ DefAlloc z ∧
    InflateDictionary h s ((log.dictionary ++ log.output).drop ((log.dictionary ++ log.output).length - 32768)) := by
  obtain ⟨block, stream, state, current, allocator, dictionary⟩ := ProtocolWindow.allowed_saved_logical_exact allowed scope
  have streamEq : stream = z := Option.some.inj (current.good.live.hz.symm.trans good.live.hz)
  subst stream
  have blockEq : block = zs := by
    have same := current.good.live.zst.symm.trans good.live.zst
    cases same
    rfl
  subst block
  have stateEq : state = s := Option.some.inj (current.good.live.hs.symm.trans good.live.hs)
  subst state
  have physical := dictionary active
  rw [current.window] at physical
  exact ⟨current, allocator, physical⟩

/-- The independent copy syntax itself bounds the decoded distance. -/
theorem CopySyntax.distance_bounds {L D : List Nat} (p : CopySyntax L D) :
    1 ≤ distBases.getD p.distanceSymbol 0 + p.distanceValue ∧
    distBases.getD p.distanceSymbol 0 + p.distanceValue ≤ 32768 := by
  have valueBound := readBits_value_bound p.distanceRead
  obtain ⟨lo, _width, budget⟩ := distance_base_extra_bounds p.distanceSymbol p.distanceUpper
  omega

/-- The real retained dictionary suffices for every independently valid
format distance. Its actual-copy bytes equal the logical full-history
bytes. This includes arbitrary current output prefixes and overlapping
copies; old logical bytes are restored on the left of the equality. -/
theorem protocol_copy_history {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {log : DataLog} {L D : List Nat} (p : CopySyntax L D)
    (allowed : AllowedInflateProtocol 15 r h log)
    (scope : ProtocolWindow.PlatformScope allowed.choose_spec)
    (good : Good h r zs z s) (active : s.mode < CHECK)
    (current : List UInt8) (made : Nat)
    (validDistance : distBases.getD p.distanceSymbol 0 + p.distanceValue ≤
      (log.dictionary ++ log.output ++ current).length) :
    let saved := (log.dictionary ++ log.output).drop ((log.dictionary ++ log.output).length - 32768)
    let distance := distBases.getD p.distanceSymbol 0 + p.distanceValue
    InflateDictionary h s saved ∧ distance ≤ saved.length + current.length ∧
      copyBack log.dictionary distance made (log.output ++ current) =
        log.output ++ copyBack saved distance made current := by
  dsimp only
  obtain ⟨_invariant, _allocator, physical⟩ := protocol_saved_dictionary allowed scope good active
  have distanceBounds := p.distance_bounds
  have checks := window_distance_check_agrees log.dictionary log.output current 32768
    (distBases.getD p.distanceSymbol 0 + p.distanceValue) distanceBounds.2
  have fits : distBases.getD p.distanceSymbol 0 + p.distanceValue ≤
      ((log.dictionary ++ log.output).drop ((log.dictionary ++ log.output).length - 32768)).length + current.length := by
    apply Classical.byContradiction
    intro over
    have unavailable : (((log.dictionary ++ log.output).drop ((log.dictionary ++ log.output).length - 32768)) ++ current).length <
        distBases.getD p.distanceSymbol 0 + p.distanceValue := by simpa only [List.length_append] using Nat.lt_of_not_ge over
    have impossible := checks.mp unavailable
    omega
  refine ⟨physical, fits, ?_⟩
  exact retained_history_agrees _ _ _ _ _ _ (List.drop_suffix _ _) (by omega) fits

#print axioms protocol_saved_dictionary
#print axioms CopySyntax.distance_bounds
#print axioms protocol_copy_history
end Zlib.Inflate.Proofs.SlowInputFragment
