import ZlibF.Proof.«inflate.c.whole-epoch-public-entry-all-v4»
namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs
set_option autoImplicit false

/-- Ordinary CODELENS is disjoint from the actual all-zero alphabet route.
The latter already has EmptyCodeHeader with its exact zero-length prefix.
This is proof-side source provenance, not a public caller condition. -/
def SourcePhase4.Routed {log : DataLog} {s : InflateState} {wire : List Bool}
    (phase : SourcePhase4 log s wire) : Prop := by
  cases phase with
  | legacy previous =>
    cases previous with
    | codes _ data => exact ∃ n ∈ data.alphabet, n ≠ 0
    | _ => exact True
  | _ => exact True

theorem SourcePhase4.routed_of_not_codes {log : DataLog} {s : InflateState} {wire : List Bool}
    (phase : SourcePhase4 log s wire) (mode : s.mode ≠ CODELENS) : phase.Routed := by
  cases phase with
  | legacy previous =>
    cases previous with
    | codes actual _ => exact False.elim (mode actual)
    | _ => trivial
  | _ => trivial

/-- The complete source envelope retains alphabet routing alongside the
frozen v4 joint invariant. Its generic actual DataStep preservation is
still a separate, unproved obligation. -/
structure SourceInvariant (h : Heap) (r : ZStreamRef) (log : DataLog) where
  core : Invariant4 h r log
  routed : core.source.phase.Routed

structure SourceCallCut (c : Ctx) (entryHeap h : Heap) (r : ZStreamRef) (zs : Nat)
    (entryZ z : ZStream) (s : InflateState) (l : IL) (base : DataLog) (raw : List UInt8) where
  core : EpochCallCut4 c entryHeap h r zs entryZ z s l base raw
  routed : core.phase.Routed

structure SourceCallExit (c : Ctx) (entryHeap h : Heap) (r : ZStreamRef) (zs : Nat)
    (entryZ z : ZStream) (s : InflateState) (l : IL) (base : DataLog) (raw : List UInt8) (exit : Ex) where
  core : EpochCallExit4 c entryHeap h r zs entryZ z s l base raw exit
  routed : core.phase.Routed

def DispatchResult4.Routed
    {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat}
    {entryZ z : ZStream} {s : InflateState} {l : IL} {base : DataLog} {raw : List UInt8}
    {before : EpochCallCut4 c entryHeap h r zs entryZ z s l base raw}
    (result : DispatchResult4 before) : Prop := by
  cases result with
  | progress _ _ _ _ _ next => exact next.phase.Routed
  | stopped _ _ _ _ _ _ next => exact next.phase.Routed

structure SourceDispatch
    {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat}
    {entryZ z : ZStream} {s : InflateState} {l : IL} {base : DataLog} {raw : List UInt8}
    (before : SourceCallCut c entryHeap h r zs entryZ z s l base raw) where
  result : DispatchResult4 before.core
  routed : result.Routed

/-- Real default initialization is HEAD and hence establishes routing;
no CODE nonzero premise is supplied by the caller. -/
theorem SourceInvariant.init {before after : Heap} {r : ZStreamRef} {version : BPtr}
    (domain : InitDomain before r version)
    (platform : ZlibF.PlatformMemory.ByteObjectsFit before)
    (actual : C.run (inflateInit2_ (some r) 15 version 112) before = .ok (Z_OK, after)) :
    Nonempty (SourceInvariant after r {}) := by
  obtain ⟨core⟩ := Invariant4.init domain platform actual
  obtain ⟨point, _index, mode, _bits, _hold⟩ := CausalInput.AtPublic.init domain platform actual
  have state := observed_state_unique core.source.point.good point.good
  have noCodes : core.source.point.state.mode ≠ CODELENS := by rw [state, mode]; decide
  exact ⟨core, core.source.phase.routed_of_not_codes noCodes⟩

/-- Caller rebuffering preserves the exact same routed source witness,
including ordinary CODE and its parser inverse. -/
theorem SourceInvariant.rebuffer {h after : Heap} {r : ZStreamRef} {log : DataLog}
    (before : SourceInvariant h r log) (edit : Rebuffer h after r)
    (platform : ZlibF.PlatformMemory.ByteObjectsFit after) : Nonempty (SourceInvariant after r log) := by
  let previous := before.core
  obtain ⟨stream, fields, good⟩ := rebuffer_inflate_good previous.source.point.good edit
  obtain ⟨sameStream, origin⟩ := rebuffer_default_origin previous.origin edit platform
  have streamEq : sameStream = stream := Option.some.inj (origin.good.live.hz.symm.trans good.live.hz)
  subst sameStream
  let point : CausalInput.AtPublic after r log previous.source.wire :=
    ⟨previous.source.point.zs, stream, previous.source.point.state, good, previous.source.point.source⟩
  let source : AtPublic4 after r log :=
    ⟨previous.source.wire, point, previous.source.phase, previous.source.saved⟩
  let core : Invariant4 after r log := {
    source := source
    origin := origin
    allocator := by change DefAlloc stream; rw [fields]; exact previous.allocator
    materialized := SourcePhase4.Materialized.rebuffer previous.source.phase previous.materialized previous.source.point.good edit
    window := fun active => WindowHistory.rebuffer_dictionary previous.source.point.good edit (previous.window active)
    checksum := by
      intro lower upper
      change WrapperGlue.AdlerCredit stream previous.source.point.state log.output
      rw [fields]
      exact previous.checksum lower upper
    wrapperOrigins := previous.wrapperOrigins }
  exact ⟨core, before.routed⟩

#print axioms SourcePhase4.routed_of_not_codes
#print axioms SourceInvariant.init
#print axioms SourceInvariant.rebuffer
end Zlib.Inflate.Proofs.WholeEpoch
