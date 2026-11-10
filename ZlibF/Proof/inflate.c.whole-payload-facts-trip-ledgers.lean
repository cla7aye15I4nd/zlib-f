import ZlibF.Proof.«inflate.c.whole-payload-facts-trip»
namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs
set_option autoImplicit false

private theorem byte_put_allocOk (h : Heap) (dest : BRef) (array : Array UInt8) :
    (Space.put h dest array).allocOk = h.allocOk := by
  cases dest with
  | blk _ => rfl
  | str _ => rfl
  | dstate_depth i =>
    change (match h.dstates i with | some state => _ | none => h).allocOk = h.allocOk
    cases h.dstates i <;> rfl
  | st_dist_code => rfl
  | st_length_code => rfl

private theorem restore_allocOk (h after : Heap) (pointer : BPtr) (made : Nat) :
    (restoreRegions h after [⟨pointer, made⟩]).allocOk = after.allocOk := by
  unfold restoreRegions
  simp only [List.foldl_cons, List.foldl_nil]
  cases pointer with
  | null => rfl
  | ref dest off =>
    change (match (Space.get h dest : Option (Array UInt8)) with
      | none => after | some array => Space.put after dest array).allocOk = after.allocOk
    cases Space.get h dest with
    | none => rfl
    | some array => exact byte_put_allocOk after dest array

/-- The allocation oracle is immutable even for the full general-buffer
fast branch. This follows from its produced exact output frame. -/
theorem PayloadTrip4.allocationOracle
    {c : Ctx} {entryHeap h after : Heap} {r : ZStreamRef} {zs : Nat}
    {entryZ z : ZStream} {s : InflateState} {l regs : IL} {base : DataLog} {raw : List UInt8}
    {outcome : Except Ex Unit} {before : CallFacts c entryHeap h r zs entryZ z s l base raw}
    (trip : PayloadTrip4 before after regs outcome) : after.allocOk = entryHeap.allocOk := by
  have oracle := trip.outputFrame.1.2.1
  rw [restore_allocOk] at oracle
  exact oracle.symm.trans before.allocationOracle

/-- Physical cursor/count advancement is indexed in the original public
call, rather than only the current local dispatcher suffix. -/
theorem PayloadTrip4.public_ledgers
    {c : Ctx} {entryHeap h after : Heap} {r : ZStreamRef} {zs : Nat}
    {entryZ z : ZStream} {s : InflateState} {l regs : IL} {base : DataLog} {raw : List UInt8}
    {outcome : Except Ex Unit} {before : CallFacts c entryHeap h r zs entryZ z s l base raw}
    (trip : PayloadTrip4 before after regs outcome) :
    before.used + trip.used ≤ raw.length ∧
    regs.next = inputAdvance entryZ.next_in (before.used + trip.used) ∧
    regs.have_.toNat + (before.used + trip.used) = entryZ.avail_in.toNat ∧
    regs.put = inputAdvance entryZ.next_out (before.emitted.length + trip.made) ∧
    regs.left.toNat + (before.emitted.length + trip.made) = entryZ.avail_out.toNat := by
  have bound := trip.usedBound
  rw [List.length_drop] at bound
  have oldBound := before.usedBound
  refine ⟨by omega, ?_, ?_, ?_, ?_⟩
  · rw [trip.next, before.next, inputAdvance_add]
  · have old := before.haveCount
    have new := trip.haveCount
    omega
  · rw [trip.put, before.put, inputAdvance_add]
  · have old := before.leftCount
    have new := trip.leftCount
    omega

#print axioms PayloadTrip4.allocationOracle
#print axioms PayloadTrip4.public_ledgers
end Zlib.Inflate.Proofs.WholeEpoch
