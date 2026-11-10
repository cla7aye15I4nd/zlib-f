import ZlibF.Proof.«inflate.c.whole-epoch-source-spine»
import ZlibF.Proof.«inflate.c.dictionary-install-source-frame»
namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs
set_option autoImplicit false

def DictionaryPhase (log : DataLog) (s : InflateState) (wire : List Bool) : Prop :=
  ∃ (w : Wrapper log.dictionary) (identifier : UInt32),
    w.flg.toNat / 32 % 2 = 1 ∧
    wire = bytesBits ([w.cmf, w.flg] ++ be32 identifier.toNat) ∧ log.output = [] ∧
    s.bits = 0 ∧ s.check = identifier.toUInt64 ∧
    (s.havedict ≠ 0 → identifier = adler32 log.dictionary)

theorem SourcePhase.dictionary_fields {log : DataLog} {s : InflateState} {wire : List Bool}
    (phase : SourcePhase log s wire) (mode : s.mode = DICT) : DictionaryPhase log s wire := by
  cases phase with
  | dictionary w identifier _ flagged anchor empty bits check installed =>
    exact ⟨w, identifier, flagged, anchor, empty, bits, check, installed⟩
  | memory prior previous notMemory frame =>
    rw [frame] at mode
    change MEM = DICT at mode
    exact False.elim ((by decide : MEM ≠ DICT) mode)
  | _ => simp_all [HEAD, DICTID, DICT, TYPE, TYPEDO, TABLE, LENLENS, CODELENS, STORED,
      COPY_, COPY, LEN_, LEN, LENEXT, DIST, DISTEXT, LIT, MATCH, CHECK, LENGTH, DONE, BAD]

/-- Existing actual protocol history supplies the configured wrap and
saved window on exactly this observed state. It supplies no functional
parser or desired output assertion. -/
theorem protocol_fields_at_point {h : Heap} {r : ZStreamRef} {log : DataLog} {pending : Bool}
    {wire : List Bool} (point : CausalInput.AtPublic h r log wire)
    (trace : InflateProtocolTrace 15 r h log pending) (scope : ProtocolWindow.PlatformScope trace) :
    point.state.wrap = 5 ∧
      (point.state.mode < CHECK → InflateDictionary h point.state
        ((log.dictionary ++ log.output).drop
          ((log.dictionary ++ log.output).length - 2 ^ point.state.wbits.toNat))) := by
  obtain ⟨physical, history, exactHistory, _rest⟩ := ProtocolWindow.exact_physical_history trace scope
  obtain ⟨zs, z, s, current, _allocator, stored⟩ := history.invariant
  have zEq : z = point.z := Option.some.inj (current.good.live.hz.symm.trans point.good.live.hz)
  subst z
  have index : zs = point.zs := by simpa using current.good.live.zst.symm.trans point.good.live.zst
  subst zs
  have state : s = point.state := Option.some.inj (current.good.live.hs.symm.trans point.good.live.hs)
  subst s
  have wrap := (ProtocolWindow.history_header_fields history current).1
  exact ⟨wrap, fun active => by simpa only [exactHistory] using stored active⟩

/-- Successful wrapped dictionary installation consumes a protocol token
and preserves the exact source spine. Refusals and real allocation failure
are also retained. No format or callee specification is assumed. -/
theorem Invariant.dictionary
    {h after : Heap} {r : ZStreamRef} {log : DataLog} {pending : Bool}
    {source : BPtr} {len : UInt32} {bytes : List UInt8} {rc : Int32}
    (before : Invariant h r log)
    (trace : InflateProtocolTrace 15 r h log pending) (scope : ProtocolWindow.PlatformScope trace)
    (range : CallerRange h r source len.toNat false) (input : Bytes h source len.toNat bytes)
    (actual : C.run (inflateSetDictionary (some r) source len) h = .ok (rc, after))
    (allowed : rc ≠ Z_OK ∨ pending = true) :
    Nonempty (Invariant after r {log with dictionary := if rc = Z_OK then bytes else log.dictionary}) := by
  have wrapped := (protocol_fields_at_point before.source.point trace scope).1
  obtain ⟨code, heap, state, run, current, outcomes⟩ :=
    inflateSetDictionary_source_frame before.origin before.allocator range input
  have pair := Except.ok.inj (run.symm.trans actual)
  cases pair
  rcases outcomes with refused | failed | success
  · obtain ⟨codeError, heapEq, stateEq⟩ := refused
    subst after
    have notOK : rc ≠ Z_OK := by rcases codeError with rfl | rfl <;> decide
    simpa only [ite_eq_right notOK] using (show Nonempty (Invariant h r log) from ⟨before⟩)
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
    let observed : AtPublic after r log :=
      ⟨before.source.wire, point, .memory before.source.point.state before.source.phase notMemory stateEq⟩
    refine ⟨⟨observed, current, before.allocator, ?_, ?_, ?_⟩⟩
    · trivial
    · intro active
      change state.mode < CHECK at active
      rw [stateEq] at active
      exact False.elim ((by decide : ¬ MEM < CHECK) active)
    · intro _lower upper
      change state.mode ≤ DONE at upper
      rw [stateEq] at upper
      exact False.elim ((by decide : ¬ MEM ≤ DONE) upper)
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
    let nextPhase : SourcePhase (sourceLog nextLog) state before.source.wire :=
      .dictionary nextWrapper identifier (by rw [frame]; exact dict) flagged anchor empty
        (by rw [frame]; exact bits) (by rw [frame]; exact check) (fun _ => idEq)
    let observed : AtPublic after r nextLog := ⟨before.source.wire, point, nextPhase⟩
    have arguments : StreamArguments h r (.inflateSetDictionary (some r) source len) := range
    have permission : (15 : Int32).toInt < 0 ∨ Z_OK ≠ Z_OK ∨ pending = true :=
      Or.inr (Or.inr (allowed.resolve_left (by intro no; exact no rfl)))
    have generated := trace.dictionary arguments input run permission
    have generatedScope : ProtocolWindow.PlatformScope generated :=
      .dictionary (arguments := arguments) (input := input) (actual := run) (allowed := permission) scope
    have saved := (protocol_fields_at_point point (by simpa using generated)
      (by simpa using generatedScope)).2
    refine ⟨⟨observed, current, before.allocator, ?_, saved, ?_⟩⟩
    · trivial
    · intro lower _upper
      change TYPE ≤ state.mode at lower
      rw [frame] at lower
      change TYPE ≤ before.source.point.state.mode at lower
      rw [dict] at lower
      exact False.elim ((by decide : ¬ TYPE ≤ DICT) lower)

#print axioms protocol_fields_at_point
#print axioms Invariant.dictionary
#print axioms SourcePhase.dictionary_fields
end Zlib.Inflate.Proofs.WholeEpoch
