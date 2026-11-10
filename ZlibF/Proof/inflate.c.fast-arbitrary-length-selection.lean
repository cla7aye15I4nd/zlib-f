import ZlibF.Proof.«inflate.c.fast-arbitrary-length-query»
namespace Zlib.Inflate.Proofs.FastArbitraryBody
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inffast.Spec Zlib.Inftrees
open Zlib.Inftrees.Spec.DecodeSemantics Zlib.Inftrees.Spec.DecodeSoundness
open Zlib.Inftrees.Spec.DecodeTableInvariant Zlib.Inftrees.Spec.DecodeTableStability
open Zlib.Inftrees.Spec.Subtable Zlib.Inffast.Proofs
set_option autoImplicit false
set_option maxRecDepth 8192

/-- A source cut at the actual first or second-level leaf. The continuation
is proved from the translated one/two-pass loop; it is not an assumed
callee contract. No source bytes have been emitted or forgotten. -/
structure LengthLeafCut (h : Heap) (r : ZStreamRef) (c : Zlib.Inffast.Ctx)
    (codeRef : CodeRef) (codes : Array Code) (offset root : Nat)
    (initialSlow : IL) (initialFast : Zlib.Inffast.L) (bs : List UInt8) where
  slow : IL
  fast : Zlib.Inffast.L
  index : Nat
  skipped : Nat
  bound : index < codes.size
  leaf : LenLeaf skipped (codes.getD index default)
  width : skipped + (codes.getD index default).bits.toNat ≤ 15
  fits : (codes.getD index default).bits.toNat ≤ slow.bits.toNat
  packet : FastInputPacket h slow bs fast
  buffers : DispatchBuffers h r slow bs
  here : fast.here = .ref codeRef index
  slowFields : slow.next = initialSlow.next ∧ slow.have_ = initialSlow.have_ ∧
    slow.put = initialSlow.put ∧ slow.left = initialSlow.left ∧ slow.out_ = initialSlow.out_
  fastFields : fast.out = initialFast.out ∧ fast.len = initialFast.len
  source : stream slow bs = (stream initialSlow bs).drop skipped
  bitCount : slow.bits.toNat + skipped = initialSlow.bits.toNat
  query : tableRead LENS codes offset root
    (Zlib.Inftrees.Spec.DecodeShort.padded (bitsOfNat initialSlow.hold.toNat initialSlow.bits.toNat)) =
      some (codes.getD index default, skipped + (codes.getD index default).bits.toNat)
  resume : ∀ result after,
    C.run (Zlib.Inffast.dolen c fast) h = .ok (result, after) → result.againL = false →
    C.run (cdoWhile (Zlib.Inffast.dolen c) (fun current => pure (current.againL, current)) initialFast) h =
      .ok (result, after)

/-- Root/link selection yields an actual fitted leaf source cut on
arbitrary current input. Both a direct root and a genuine second pass are
kept; selecting the subtable consumes only the root bits in the source. -/
theorem length_leaf_source_cut
    {h : Heap} {slow : IL} {bs : List UInt8} {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {codeRef : CodeRef} {codes : Array Code} {offset root extent : Nat} {L : List Nat}
    (packet : FastInputPacket h slow bs l) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    (held : 15 ≤ slow.bits.toNat)
    (pointer : l.here = .ref codeRef (offset + slow.hold.toNat % 2 ^ root))
    (lcodePtr : c.lcode = .ref codeRef offset) (get : Space.get h codeRef = some codes)
    (safe : LenTableSafe codes offset root) (inv : Inv LENS codes offset root extent L)
    (stable : StableQuery LENS codes offset root) :
    Nonempty (LengthLeafCut h r c codeRef codes offset root slow l bs) := by
  obtain ⟨index, skipped, bound, leaf, width, query, selected, _meaning⟩ :=
    length_selected_query buffers.bits held safe inv stable
  let first := codes.getD (offset + slow.hold.toNat % 2 ^ root) default
  rcases selected with ⟨zero, atRoot, nonlink⟩ | ⟨link, skippedEq, indexEq⟩
  · subst skipped
    subst index
    exact ⟨{ slow := slow, fast := l, index := offset + slow.hold.toNat % 2 ^ root, skipped := 0,       bound := bound, leaf := leaf, width := width, fits := by omega,       packet := packet, buffers := buffers, here := pointer,       slowFields := ⟨rfl, rfl, rfl, rfl, rfl⟩, fastFields := ⟨rfl, rfl⟩,       source := by simp only [List.drop_zero], bitCount := by omega,       query := query, resume := fun _ _ actual noAgain => dolen_loop_one actual noAgain }⟩
  · change skipped = first.bits.toNat at skippedEq
    have rootBound : slow.hold.toNat % 2 ^ root < 2 ^ root := Nat.mod_lt _ (Nat.two_pow_pos _)
    have rootWidth : first.bits.toNat ≤ 15 := by
      have shape := safe.2.2 _ rootBound
      change (if LenLink first then LinkOK LenLeaf codes offset first else LenLeaf 0 first) at shape
      rw [ite_eq_left link] at shape
      exact shape.1
    have actualPointer : l.here = .ref codeRef (offset + slow.hold.toNat % 2 ^ root) := pointer
    obtain ⟨linked, slice, actual, sliceEq, here, again, broke, out, len, nextPacket, nextBuffers, source⟩ :=
      packet.dolen_root_link_actual_slow_frame invariant buffers actualPointer lcodePtr get safe rootBound link held
    have shift : (l.hold >>> first.bits.toUInt32.toUInt64).toNat =
        slow.hold.toNat / 2 ^ first.bits.toNat := by
      rw [packet.hold]
      simpa only [toNat32] using (u64_shr (x := slow.hold) (n := first.bits.toUInt32)
        (by simpa only [toNat32] using (show first.bits.toNat < 64 by omega)))
    have sliceNat : slice = (slow.hold.toNat / 2 ^ first.bits.toNat) % 2 ^ first.op.toNat := by
      change slice = (l.hold >>> first.bits.toUInt32.toUInt64).toNat % 2 ^ first.op.toNat at sliceEq
      rw [shift] at sliceEq
      exact sliceEq
    have hereEq : linked.here = .ref codeRef index := by
      rw [indexEq]
      change linked.here = .ref codeRef (offset + first.val.toNat + _)
      change linked.here = .ref codeRef (offset + first.val.toNat + slice) at here
      rw [sliceNat] at here
      exact here
    let nextSlow := {slow with hold := slow.hold >>> first.bits.toUInt32.toUInt64, bits := slow.bits - first.bits.toUInt32}
    have bitCount : nextSlow.bits.toNat + skipped = slow.bits.toNat := by
      change (slow.bits - first.bits.toUInt32).toNat + skipped = slow.bits.toNat
      rw [u32_toNat_sub (by simpa only [toNat32] using (show first.bits.toNat ≤ slow.bits.toNat by omega)), toNat32]
      rw [skippedEq]
      omega
    have loop (result : Zlib.Inffast.L) (after : Heap)
        (second : C.run (Zlib.Inffast.dolen c linked) h = .ok (result, after))
        (noAgain : result.againL = false) :
        C.run (cdoWhile (Zlib.Inffast.dolen c) (fun current => pure (current.againL, current)) l) h =
          .ok (result, after) := by
      exact cdoWhile_two actual (by simp only [again, pure]) second (by simp only [noAgain, pure])
    refine ⟨{ slow := nextSlow, fast := linked, index := index, skipped := skipped,       bound := bound, leaf := leaf, width := width, fits := by omega,       packet := nextPacket, buffers := nextBuffers, here := hereEq,       slowFields := ⟨rfl, rfl, rfl, rfl, rfl⟩, fastFields := ⟨out, len⟩,       source := ?_, bitCount := bitCount, query := query, resume := loop }⟩
    rw [skippedEq]
    exact source

#print axioms length_leaf_source_cut
end Zlib.Inflate.Proofs.FastArbitraryBody
