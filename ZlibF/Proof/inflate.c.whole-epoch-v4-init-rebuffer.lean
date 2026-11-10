import ZlibF.Proof.«inflate.c.whole-epoch-source-spine-v4»
namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs
set_option autoImplicit false

/-- Lift actual previously checked public state data; the inverse parser
context remains an explicit internal proof obligation in CODELENS. -/
def ScopedInvariant.upgrade {h : Heap} {r : ZStreamRef} {log : DataLog}
    (before : ScopedInvariant h r log) (reversible : before.core.source.phase.Reversible) :
    Invariant4 h r log :=
  { source := { wire := before.core.source.wire, point := before.core.source.point
                phase := .legacy before.core.source.phase, saved := True.intro }
    origin := before.core.origin
    allocator := before.core.allocator
    materialized := ⟨before.core.tables, reversible⟩
    window := before.core.window
    checksum := before.core.checksum
    wrapperOrigins := before.wrapperOrigins }

/-- Successful default initialization supplies the new joint invariant.
It is HEAD, so no inverse CODE parser obligation is assumed. -/
theorem Invariant4.init {before after : Heap} {r : ZStreamRef} {version : BPtr}
    (domain : InitDomain before r version)
    (platform : ZlibF.PlatformMemory.ByteObjectsFit before)
    (actual : C.run (inflateInit2_ (some r) 15 version 112) before = .ok (Z_OK, after)) :
    Nonempty (Invariant4 after r {}) := by
  obtain ⟨initial⟩ := ScopedInvariant.init domain platform actual
  obtain ⟨point, _index, mode, _bits, _hold⟩ := CausalInput.AtPublic.init domain platform actual
  have state := observed_state_unique initial.core.source.point.good point.good
  have initialMode : initial.core.source.point.state.mode = HEAD := by rw [state]; exact mode
  apply Nonempty.intro (initial.upgrade ?_)
  cases phase : initial.core.source.phase with
  | codes codes data =>
    rw [initialMode] at codes
    exact False.elim ((by decide : HEAD ≠ CODELENS) codes)
  | _ => trivial

/-- Caller edits preserve source fields, real tables and inverse parser
metadata because the private decoder state is unchanged. -/
theorem SourcePhase4.Materialized.rebuffer
    {h after : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {log : DataLog} {wire : List Bool} (phase : SourcePhase4 log s wire)
    (materialized : phase.Materialized h) (good : Good h r zs z s)
    (edit : Rebuffer h after r) : phase.Materialized after := by
  cases phase with
  | legacy previous => exact ⟨SourcePhase.Materialized.rebuffer previous materialized.1 good edit, materialized.2⟩
  | uncheckedMatch _ data => exact TableBinding.rebuffer materialized good edit
  | _ => trivial

/-- Actual rebuffering preserves the new joint public state, including a
fully parsed but not yet distance-checked MATCH. -/
theorem Invariant4.rebuffer {h after : Heap} {r : ZStreamRef} {log : DataLog}
    (before : Invariant4 h r log) (edit : Rebuffer h after r)
    (platform : ZlibF.PlatformMemory.ByteObjectsFit after) : Nonempty (Invariant4 after r log) := by
  obtain ⟨stream, fields, good⟩ := rebuffer_inflate_good before.source.point.good edit
  obtain ⟨sameStream, origin⟩ := rebuffer_default_origin before.origin edit platform
  have streamEq : sameStream = stream := Option.some.inj (origin.good.live.hz.symm.trans good.live.hz)
  subst sameStream
  let point : CausalInput.AtPublic after r log before.source.wire :=
    ⟨before.source.point.zs, stream, before.source.point.state, good, before.source.point.source⟩
  let source : AtPublic4 after r log :=
    ⟨before.source.wire, point, before.source.phase, before.source.saved⟩
  refine ⟨⟨source, origin, ?_, ?_, ?_, ?_, before.wrapperOrigins⟩⟩
  · change DefAlloc stream
    rw [fields]
    exact before.allocator
  · exact SourcePhase4.Materialized.rebuffer before.source.phase before.materialized before.source.point.good edit
  · intro active
    exact WindowHistory.rebuffer_dictionary before.source.point.good edit (before.window active)
  · intro lower upper
    change WrapperGlue.AdlerCredit stream before.source.point.state log.output
    rw [fields]
    exact before.checksum lower upper

#print axioms ScopedInvariant.upgrade
#print axioms Invariant4.init
#print axioms SourcePhase4.Materialized.rebuffer
#print axioms Invariant4.rebuffer
end Zlib.Inflate.Proofs.WholeEpoch
