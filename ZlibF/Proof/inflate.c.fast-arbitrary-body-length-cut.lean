import ZlibF.Proof.«inflate.c.fast-arbitrary-length-selection»
import ZlibF.Proof.«inflate.c.fast-view-entry-six-invariant»
namespace Zlib.Inflate.Proofs.FastArbitraryBody
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inffast.Spec Zlib.Inftrees
open Zlib.Inftrees.Spec.DecodeSemantics Zlib.Inftrees.Spec.DecodeSoundness
open Zlib.Inftrees.Spec.DecodeTableInvariant Zlib.Inftrees.Spec.DecodeTableStability
open Zlib.Inffast.Proofs
set_option autoImplicit false
set_option maxRecDepth 8192

/-- The real zero/two input pulls and root/link passes expose one fitted
leaf. Raw cursor advance is separate from logical code consumption. -/
structure BodyLengthCut (h : Heap) (r : ZStreamRef) (c : Zlib.Inffast.Ctx)
    (codeRef : CodeRef) (codes : Array Code) (offset root : Nat)
    (initialSlow : IL) (initialFast : Zlib.Inffast.L) (bs : List UInt8) where
  initialCursor : initialFast.in_ = initialSlow.next
  preparedSlow : IL
  preparedFast : Zlib.Inffast.L
  used : Nat
  usedBound : used ≤ 2
  usedInput : used ≤ bs.length
  source : stream preparedSlow (bs.drop used) = stream initialSlow bs
  out : preparedFast.out = initialFast.out
  cursor : preparedSlow.next = inputAdvance initialSlow.next used
  fields : preparedSlow.put = initialSlow.put ∧ preparedSlow.left = initialSlow.left
  held : 15 ≤ preparedSlow.bits.toNat
  bitBound : preparedSlow.bits.toNat ≤ 30
  selection : LengthLeafCut h r c codeRef codes offset root preparedSlow preparedFast (bs.drop used)
  bodyResume : ∀ result after,
    C.run (Zlib.Inffast.dolen c selection.fast) h = .ok (result, after) → result.againL = false →
    C.run (Zlib.Inffast.inflate_fast_body c initialFast) h = .ok (result, after)

/-- Every safety-ready fast input exposes an actual root/link leaf before
classifying arbitrary bytes. No logical token, future source or distinct
input/output object is assumed. -/
theorem body_length_source_cut
    {h : Heap} {slow : IL} {bs : List UInt8} {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {codeRef : CodeRef} {codes : Array Code} {offset root extent : Nat} {L : List Nat}
    (packet : FastInputPacket h slow bs l) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs) (margin : 6 ≤ slow.have_.toNat) (bits : slow.bits.toNat ≤ 30)
    (lcodePtr : c.lcode = .ref codeRef offset) (get : Space.get h codeRef = some codes)
    (safe : LenTableSafe codes offset root) (inv : Inv LENS codes offset root extent L)
    (stable : StableQuery LENS codes offset root)
    (mask : c.lmask.toUInt64.toNat = 2 ^ root - 1) :
    Nonempty (BodyLengthCut h r c codeRef codes offset root slow l bs) := by
  obtain ⟨first, second, third, fourth, fifth, sixth, tail, rfl⟩ := packet.six_unread margin
  by_cases small : slow.bits.toNat < 15
  · obtain ⟨next, fast, selected, rootSlice, prefixRun, selectedEq, nextPacket, nextBuffers, _current,
      source, out, _hold, put, left, cursor, _bitCount, held, bitBound, rootEq, _rootBound⟩ :=
      packet.two_pull_root_prefix invariant buffers small lcodePtr get safe mask
    have fastHold : fast.hold = next.hold := by
      have same : selected.hold = fast.hold := by rw [selectedEq]
      exact same.symm.trans nextPacket.hold
    have rootMath : rootSlice = next.hold.toNat % 2 ^ root := by
      rw [rootEq, u64_and_mask mask, fastHold]
    have pointer : selected.here = .ref codeRef (offset + next.hold.toNat % 2 ^ root) := by
      rw [selectedEq, rootMath]
    obtain ⟨cut⟩ := length_leaf_source_cut nextPacket invariant nextBuffers (by omega) pointer lcodePtr get safe inv stable
    have needsPull : l.bits < 15 := by
      rw [packet.bits]
      exact UInt32.lt_iff_toNat_lt.mpr small
    exact ⟨{ initialCursor := packet.cursor, preparedSlow := next, preparedFast := selected, used := 2, usedBound := by omega, usedInput := by simp, source := source, out := out, cursor := cursor, fields := ⟨put, left⟩, held := by omega, bitBound := bitBound, selection := cut, bodyResume := fun result after actual noAgain => body_from_two_pull_root needsPull prefixRun (cut.resume result after actual noAgain) }⟩
  · have held : 15 ≤ slow.bits.toNat := by omega
    let rootSlice := (l.hold &&& c.lmask.toUInt64).toNat
    let selected := {l with here := .ref codeRef (offset + rootSlice)}
    have rootMath : rootSlice = slow.hold.toNat % 2 ^ root := by dsimp only [rootSlice]; rw [u64_and_mask mask, packet.hold]
    obtain ⟨rootBound, _addRun, selectedPacket⟩ := packet.fast_body_root_lookup lcodePtr get safe mask
    have pointer : selected.here = .ref codeRef (offset + slow.hold.toNat % 2 ^ root) := by simp only [selected, rootMath]
    obtain ⟨cut⟩ := length_leaf_source_cut selectedPacket invariant buffers held pointer lcodePtr get safe inv stable
    have noPull : ¬ l.bits < 15 := by
      intro below
      have lt : slow.bits.toNat < 15 := by rw [← packet.bits]; exact UInt32.lt_iff_toNat_lt.mp below
      omega
    have bound : offset + rootSlice < codes.size := by have := safe.2.1; omega
    exact ⟨{ initialCursor := packet.cursor, preparedSlow := slow, preparedFast := selected, used := 0, usedBound := by omega, usedInput := by omega, source := by simp, out := rfl, cursor := by cases slow.next <;> simp [inputAdvance], fields := ⟨rfl, rfl⟩, held := held, bitBound := bits, selection := cut, bodyResume := fun result after actual noAgain => body_from_no_pull_root noPull lcodePtr get bound rfl rfl (cut.resume result after actual noAgain) }⟩

#print axioms body_length_source_cut
end Zlib.Inflate.Proofs.FastArbitraryBody
