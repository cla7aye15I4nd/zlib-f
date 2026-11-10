import ZlibF.Proof.«inflate.c.whole-epoch-source-spine-v4»
import ZlibF.Proof.«inflate.c.whole-epoch-dictionary-transition»
import ZlibF.Proof.«inflate.c.dictionary-install-source-frame»
namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs
set_option autoImplicit false

/-- Only the existing DICT phase can justify wrapped installation. New
unchecked MATCH and memory snapshots do not manufacture a legacy phase. -/
theorem SourcePhase4.dictionary_fields {log : DataLog} {s : InflateState} {wire : List Bool}
    (phase : SourcePhase4 log s wire) (mode : s.mode = DICT) : DictionaryPhase log s wire := by
  cases phase with
  | legacy previous => exact previous.dictionary_fields mode
  | _ => simp_all [STORED, MATCH, MEM, DICT]

/-- Successful wrapped dictionary installation consumes a protocol token
and preserves the exact source spine. Refusals and real allocation failure
are also retained. No format or callee specification is assumed. -/
theorem Invariant4.dictionary
    {h after : Heap} {r : ZStreamRef} {log : DataLog} {pending : Bool}
    {source : BPtr} {len : UInt32} {bytes : List UInt8} {rc : Int32}
    (before : Invariant4 h r log)
    (trace : InflateProtocolTrace 15 r h log pending) (scope : ProtocolWindow.PlatformScope trace)
    (range : CallerRange h r source len.toNat false) (input : Bytes h source len.toNat bytes)
    (actual : C.run (inflateSetDictionary (some r) source len) h = .ok (rc, after))
    (allowed : rc ≠ Z_OK ∨ pending = true) :
    Nonempty (Invariant4 after r {log with dictionary := if rc = Z_OK then bytes else log.dictionary}) := by
  have wrapped := before.wrapperOrigins.wrapped
  obtain ⟨code, heap, state, run, current, outcomes⟩ :=
    inflateSetDictionary_source_frame before.origin before.allocator range input
  have pair := Except.ok.inj (run.symm.trans actual)
  cases pair
  rcases outcomes with refused | failed | success
  · obtain ⟨codeError, heapEq, stateEq⟩ := refused
    subst after
    have notOK : rc ≠ Z_OK := by rcases codeError with rfl | rfl <;> decide
    simpa only [ite_eq_right notOK] using (show Nonempty (Invariant4 h r log) from ⟨before⟩)
  · obtain ⟨memory, stateEq⟩ := failed
    subst rc
    have notOK : Z_MEM_ERROR ≠ Z_OK := by decide
    simp only [ite_eq_right notOK]
    have notMemory : before.source.point.state.mode ≠ MEM := by
      intro mode
      have denied := inflateSetDictionary_refused_any before.source.point.good.live source len
        (Or.inr ⟨by rw [wrapped]; decide, by rw [mode]; decide⟩)
      have impossible := (Prod.mk.inj (Except.ok.inj (run.symm.trans denied))).1
      exact (by decide : Z_MEM_ERROR ≠ Z_STREAM_ERROR) impossible
    let point : CausalInput.AtPublic after r log before.source.wire :=
      ⟨before.source.point.zs, before.source.point.z, state, current.good,
        by rw [stateEq]; exact before.source.point.source⟩
    let observed : AtPublic4 after r log :=
      ⟨before.source.wire, point, .memory before.source.point.state before.source.phase notMemory stateEq, True.intro⟩
    refine ⟨⟨observed, current, before.allocator, ?_, ?_, ?_, ?_⟩⟩
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
      refine ⟨before.wrapperOrigins.wrapped, ?_, ?_⟩
      · intro mode
        rcases mode with mode | mode <;> change MEM = _ at mode <;> contradiction
      · intro mode
        rcases mode with mode | mode | mode <;> change MEM = _ at mode <;> contradiction
  · obtain ⟨ok, _nonnull, modeAllowed, frame, checked⟩ := success
    subst rc
    simp only [ite_true]
    have dict : before.source.point.state.mode = DICT :=
      modeAllowed.resolve_left (by rw [wrapped]; decide)
    obtain ⟨w, identifier, flagged, anchor, empty, bits, check, _installed⟩ :=
      before.source.phase.dictionary_fields dict
    have idEq : identifier = adler32 bytes := by
      apply UInt32.toNat_inj.mp
      have equal : identifier.toUInt64 = (adler32 bytes).toUInt64 := check.symm.trans (checked dict).symm
      simpa using congrArg UInt64.toNat equal
    let nextLog : DataLog := {log with dictionary := bytes}
    let nextWrapper : Wrapper nextLog.dictionary :=
      ⟨w.cmf, w.flg, w.valid, fun plain => False.elim (by rw [flagged] at plain; contradiction)⟩
    let point : CausalInput.AtPublic after r nextLog before.source.wire :=
      ⟨before.source.point.zs, before.source.point.z, state, current.good,
        by rw [frame]; exact before.source.point.source⟩
    let nextPhase : SourcePhase4 (sourceLog nextLog) state before.source.wire :=
      .legacy (.dictionary nextWrapper identifier (by rw [frame]; exact dict) flagged anchor empty
        (by rw [frame]; exact bits) (by rw [frame]; exact check) (fun _ => idEq))
    let observed : AtPublic4 after r nextLog := ⟨before.source.wire, point, nextPhase, True.intro⟩
    have arguments : StreamArguments h r (.inflateSetDictionary (some r) source len) := range
    have permission : (15 : Int32).toInt < 0 ∨ Z_OK ≠ Z_OK ∨ pending = true :=
      Or.inr (Or.inr (allowed.resolve_left (by intro no; exact no rfl)))
    have generated := trace.dictionary arguments input run permission
    have generatedScope : ProtocolWindow.PlatformScope generated :=
      .dictionary (arguments := arguments) (input := input) (actual := run) (allowed := permission) scope
    have saved := (protocol_fields_at_point point (by simpa using generated)
      (by simpa using generatedScope)).2
    refine ⟨⟨observed, current, before.allocator, ?_, saved, ?_, ?_⟩⟩
    · exact ⟨True.intro, True.intro⟩
    · intro lower _upper
      change TYPE ≤ state.mode at lower
      rw [frame] at lower
      change TYPE ≤ before.source.point.state.mode at lower
      rw [dict] at lower
      exact False.elim ((by decide : ¬ TYPE ≤ DICT) lower)
    · change WrapperOrigins state
      rw [frame]
      refine ⟨before.wrapperOrigins.wrapped, ?_, ?_⟩
      · intro mode
        change before.source.point.state.mode = HEAD ∨ before.source.point.state.mode = DICTID at mode
        rw [dict] at mode
        rcases mode with mode | mode <;> contradiction
      · intro _mode
        exact before.wrapperOrigins.last (Or.inr (Or.inr dict))


#print axioms SourcePhase4.dictionary_fields
#print axioms Invariant4.dictionary
end Zlib.Inflate.Proofs.WholeEpoch
