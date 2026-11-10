import ZlibF.Proof.«inflate.c.header-actual-accepted-packet»
namespace Zlib.Inflate.Proofs.ActualHeader
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs
open Zlib.Inftrees.Spec.DecodeTableStability
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem AcceptedPacket.table_meanings
    {c : Ctx} {h callHeap : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8} {alphabet : List Nat} {credited history : List UInt8}
    (p : AcceptedPacket c h callHeap r zs z s l bs alphabet credited history) :
    Zlib.Inftrees.Spec.DecodeTableInvariant.Inv LENS p.ready.tables.state.codes 0 p.ready.tables.state.lenbits.toNat p.ready.tables.offset
      ((actualLengthPrefix p.observation.state).take p.observation.state.nlen.toNat) ∧
    Zlib.Inftrees.Spec.DecodeTableInvariant.Inv DISTS p.ready.tables.state.codes p.ready.tables.offset p.ready.tables.state.distbits.toNat p.ready.tables.used
      ((actualLengthPrefix p.observation.state).drop p.observation.state.nlen.toNat) ∧
    StableQuery LENS p.ready.tables.state.codes 0 p.ready.tables.state.lenbits.toNat ∧
    StableQuery DISTS p.ready.tables.state.codes p.ready.tables.offset p.ready.tables.state.distbits.toNat := by
  have complete : p.observation.state.«have».toNat = p.observation.state.nlen.toNat + p.observation.state.ndist.toNat := by
    rcases p.observation.complete p.normal with bad | done
    · rw [p.mode] at bad; cases bad
    · exact done
  have slices := PayloadTables.actualLengthPrefix_payload_slices p.observation.state complete
  have lens := p.ready.tables.lens
  have dists := p.ready.tables.dists
  rw [← slices.1] at lens
  rw [← slices.2] at dists
  exact ⟨lens, dists, p.ready.tables.stableL, p.ready.tables.stableD⟩

/-- Physical same-heap consumer endpoint. Output cursors may already
contain output from earlier blocks in this call. -/
theorem AcceptedPacket.geometry
    {c : Ctx} {h callHeap : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8} {alphabet : List Nat} {credited history : List UInt8}
    (p : AcceptedPacket c h callHeap r zs z s l bs alphabet credited history) :
    let heap := setI p.observation.heap zs p.ready.tables.state
    let regs := {p.observation.regs with ret := 0}
    DefaultOriginState heap r zs p.observation.streamZ p.ready.tables.state ∧
      DispatchBuffers heap r regs (bs.drop p.observation.used) ∧
      Space.get heap (CodeRef.istate_codes zs) = some p.ready.tables.state.codes ∧
      regs.next = inputAdvance l.next p.observation.used ∧ regs.have_.toNat + p.observation.used = l.have_.toNat ∧
      regs.put = l.put ∧ regs.left = l.left ∧ regs.out_ = l.out_ ∧ regs.in_ = l.in_ ∧
      regs.bits.toNat ≤ 39 ∧ p.ready.tables.state.mode = LEN_ := by
  dsimp only
  refine ⟨p.ready.origin, p.ready.buffers, CodeRef.get_istate_codes p.ready.origin.good.live.hs,
    p.observation.cursor, p.observation.count, p.observation.put, p.observation.left, p.observation.out, ?_,
    p.liveBits, p.ready.tables.mode⟩
  obtain ⟨_state, _used, _get, _bound, _B, frame, _rest⟩ := p.observation.full.1
  change p.observation.regs.in_ = l.in_
  rw [frame]

#print axioms AcceptedPacket.table_meanings
#print axioms AcceptedPacket.geometry
end Zlib.Inflate.Proofs.ActualHeader
