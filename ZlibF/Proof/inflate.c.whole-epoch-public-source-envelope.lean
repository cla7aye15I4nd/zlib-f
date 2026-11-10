import ZlibF.Proof.«inflate.c.whole-epoch-source-routes»
namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs
set_option autoImplicit false

/-- The functional source observations produced when an actual call is
published. Safety, allocator and saved-window facts are recovered from
the independent actual protocol-history theorem on this same heap. -/
structure PublicSource (h : Heap) (r : ZStreamRef) (log : DataLog) where
  source : AtPublic4 h r log
  materialized : source.phase.Materialized h
  routed : source.phase.Routed
  checksum : TYPE ≤ source.point.state.mode → source.point.state.mode ≤ DONE →
    WrapperGlue.AdlerCredit source.point.z source.point.state log.output
  wrapperOrigins : WrapperOrigins source.point.state

/-- This uses actual protocol history only for its independently proved
physical/safety envelope. No source parser or output premise is obtained
from history, and no functional fact is added to its constructors. -/
theorem PublicSource.with_protocol
    {h : Heap} {r : ZStreamRef} {log : DataLog} {pending : Bool}
    (observed : PublicSource h r log)
    (trace : InflateProtocolTrace 15 r h log pending) (scope : ProtocolWindow.PlatformScope trace) :
    Nonempty (SourceInvariant h r log) := by
  obtain ⟨zs, z, s, origin, allocator⟩ := FunctionalEpoch.protocol_origin trace scope
  have zEq : z = observed.source.point.z :=
    Option.some.inj (origin.good.live.hz.symm.trans observed.source.point.good.live.hz)
  subst z
  have index : zs = observed.source.point.zs := by
    simpa using origin.good.live.zst.symm.trans observed.source.point.good.live.zst
  subst zs
  have state : s = observed.source.point.state :=
    Option.some.inj (origin.good.live.hs.symm.trans observed.source.point.good.live.hs)
  subst s
  have saved := (protocol_fields_at_point observed.source.point trace scope).2
  exact ⟨⟨{
    source := observed.source
    origin := origin
    allocator := allocator
    materialized := observed.materialized
    window := saved
    checksum := observed.checksum
    wrapperOrigins := observed.wrapperOrigins }, observed.routed⟩⟩

#print axioms PublicSource.with_protocol
end Zlib.Inflate.Proofs.WholeEpoch
