import ZlibF.Proof.«inflate.c.whole-epoch-source-routes»
import ZlibF.Proof.«inflate.c.whole-epoch-dictionary-transition-v4»
namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs
set_option autoImplicit false

/-- Actual dictionary requests retain the source routing envelope. Refusals
reuse the same phase; success and allocation failure construct DICT/MEM,
whose routing is unrestricted by definition. -/
theorem SourceInvariant.dictionary
    {h after : Heap} {r : ZStreamRef} {log : DataLog} {pending : Bool}
    {source : BPtr} {len : UInt32} {bytes : List UInt8} {rc : Int32}
    (before : SourceInvariant h r log)
    (trace : InflateProtocolTrace 15 r h log pending) (scope : ProtocolWindow.PlatformScope trace)
    (range : CallerRange h r source len.toNat false) (input : Bytes h source len.toNat bytes)
    (actual : C.run (inflateSetDictionary (some r) source len) h = .ok (rc, after))
    (allowed : rc ≠ Z_OK ∨ pending = true) :
    Nonempty (SourceInvariant after r {log with dictionary := if rc = Z_OK then bytes else log.dictionary}) := by
  let previous := before.core
  have wrapped := previous.wrapperOrigins.wrapped
  obtain ⟨code, heap, state, run, current, outcomes⟩ :=
    inflateSetDictionary_source_frame previous.origin previous.allocator range input
  have pair := Except.ok.inj (run.symm.trans actual)
  cases pair
  rcases outcomes with refused | failed | success
  · obtain ⟨codeError, heapEq, stateEq⟩ := refused
    subst after
    have notOK : rc ≠ Z_OK := by rcases codeError with rfl | rfl <;> decide
    simpa only [ite_eq_right notOK] using (show Nonempty (SourceInvariant h r log) from ⟨before⟩)
  · obtain ⟨memory, stateEq⟩ := failed
    subst rc
    have notOK : Z_MEM_ERROR ≠ Z_OK := by decide
    simp only [ite_eq_right notOK]
    have notMemory : previous.source.point.state.mode ≠ MEM := by
      intro mode
      have denied := inflateSetDictionary_refused_any previous.source.point.good.live source len
        (Or.inr ⟨by rw [wrapped]; decide, by rw [mode]; decide⟩)
      have impossible := (Prod.mk.inj (Except.ok.inj (run.symm.trans denied))).1
      exact (by decide : Z_MEM_ERROR ≠ Z_STREAM_ERROR) impossible
    let point : CausalInput.AtPublic after r log previous.source.wire :=
      ⟨previous.source.point.zs, previous.source.point.z, state, current.good,
        by rw [stateEq]; exact previous.source.point.source⟩
    let observed : AtPublic4 after r log :=
      ⟨previous.source.wire, point, .memory previous.source.point.state previous.source.phase notMemory stateEq, True.intro⟩
    refine ⟨⟨⟨observed, current, previous.allocator, ?_, ?_, ?_, ?_⟩, by
      apply SourcePhase4.routed_of_not_codes
      change state.mode ≠ CODELENS
      rw [stateEq]
      change MEM ≠ CODELENS
      decide⟩⟩
    · trivial
    · intro active
      change state.mode < CHECK at active
      rw [stateEq] at active
      exact False.elim ((by decide : ¬ MEM < CHECK) active)
    · intro _lower upper
      change state.mode ≤ DONE at upper
      rw [stateEq] at upper
      exact False.elim ((by decide : ¬ MEM ≤ DONE) upper)
    · change WrapperOrigins state
      rw [stateEq]
      refine ⟨previous.wrapperOrigins.wrapped, ?_, ?_⟩
      · intro mode
        rcases mode with mode | mode <;> change MEM = _ at mode <;> contradiction
      · intro mode
        rcases mode with mode | mode | mode <;> change MEM = _ at mode <;> contradiction
  · obtain ⟨ok, _nonnull, modeAllowed, frame, checked⟩ := success
    subst rc
    simp only [ite_true]
    have dict : previous.source.point.state.mode = DICT :=
      modeAllowed.resolve_left (by rw [wrapped]; decide)
    obtain ⟨w, identifier, flagged, anchor, empty, bits, check, _installed⟩ :=
      previous.source.phase.dictionary_fields dict
    have idEq : identifier = adler32 bytes := by
      apply UInt32.toNat_inj.mp
      have equal : identifier.toUInt64 = (adler32 bytes).toUInt64 := check.symm.trans (checked dict).symm
      simpa using congrArg UInt64.toNat equal
    let nextLog : DataLog := {log with dictionary := bytes}
    let nextWrapper : Wrapper nextLog.dictionary :=
      ⟨w.cmf, w.flg, w.valid, fun plain => False.elim (by rw [flagged] at plain; contradiction)⟩
    let point : CausalInput.AtPublic after r nextLog previous.source.wire :=
      ⟨previous.source.point.zs, previous.source.point.z, state, current.good,
        by rw [frame]; exact previous.source.point.source⟩
    let nextPhase : SourcePhase4 (sourceLog nextLog) state previous.source.wire :=
      .legacy (.dictionary nextWrapper identifier (by rw [frame]; exact dict) flagged anchor empty
        (by rw [frame]; exact bits) (by rw [frame]; exact check) (fun _ => idEq))
    let observed : AtPublic4 after r nextLog := ⟨previous.source.wire, point, nextPhase, True.intro⟩
    have arguments : StreamArguments h r (.inflateSetDictionary (some r) source len) := range
    have permission : (15 : Int32).toInt < 0 ∨ Z_OK ≠ Z_OK ∨ pending = true :=
      Or.inr (Or.inr (allowed.resolve_left (by intro no; exact no rfl)))
    have generated := trace.dictionary arguments input run permission
    have generatedScope : ProtocolWindow.PlatformScope generated :=
      .dictionary (arguments := arguments) (input := input) (actual := run) (allowed := permission) scope
    have saved := (protocol_fields_at_point point (by simpa using generated)
      (by simpa using generatedScope)).2
    refine ⟨⟨⟨observed, current, previous.allocator, ?_, saved, ?_, ?_⟩, by
      apply SourcePhase4.routed_of_not_codes
      change state.mode ≠ CODELENS
      rw [frame]
      change previous.source.point.state.mode ≠ CODELENS
      rw [dict]
      decide⟩⟩
    · exact ⟨True.intro, True.intro⟩
    · intro lower _upper
      change TYPE ≤ state.mode at lower
      rw [frame] at lower
      change TYPE ≤ previous.source.point.state.mode at lower
      rw [dict] at lower
      exact False.elim ((by decide : ¬ TYPE ≤ DICT) lower)
    · change WrapperOrigins state
      rw [frame]
      refine ⟨previous.wrapperOrigins.wrapped, ?_, ?_⟩
      · intro mode
        change previous.source.point.state.mode = HEAD ∨ previous.source.point.state.mode = DICTID at mode
        rw [dict] at mode
        rcases mode with mode | mode <;> contradiction
      · intro _mode
        exact previous.wrapperOrigins.last (Or.inr (Or.inr dict))

#print axioms SourceInvariant.dictionary
end Zlib.Inflate.Proofs.WholeEpoch
