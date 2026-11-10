import ZlibF.Proof.«inflate.c.payload-eob-twopull-decoded-cursor-stage»
namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
set_option autoImplicit false
theorem linked_eob_body_two_pull_indexed_generic_cursor
    {h : Heap} {slow : IL}
    {first second third fourth fifth sixth : UInt8}
    {rest : List UInt8} {l : Zlib.Inffast.L}
    {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow
      (first :: second :: third :: fourth :: fifth :: sixth :: rest) l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow
      (first :: second :: third :: fourth :: fifth :: sixth :: rest))
    (small : slow.bits.toNat < 15)
    (statePtr : c.state = some (.tab zs))
    (mode : DataTableMode s.mode)
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff rootWidth : Nat}
    (lcodePtr : c.lcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : LenTableSafe codes baseOff rootWidth)
    (mask : c.lmask.toUInt64.toNat = 2 ^ rootWidth - 1)
    (rootLink : ∀ k, k < 2 ^ rootWidth →
      (k = (((l.hold +
        (first.toUInt64 <<< l.bits.toUInt64)) +
        (second.toUInt64 <<< (l.bits + 8).toUInt64)) &&&
          c.lmask.toUInt64).toNat) →
      LenLink (codes.getD (baseOff + k) default))
    {L D : List Nat} {dict history : List UInt8} :
    ∃ (slowPrefix : IL) (selected linked : Zlib.Inffast.L)
      (rootSlice slice : Nat),
      C.run (Zlib.Inffast.dolen c selected) h = .ok (linked, h) ∧
      linked.againL = true ∧
      let rootEntry := codes.getD (baseOff + rootSlice) default
      selected.here = .ref codeRef (baseOff + rootSlice) ∧
      rootSlice = (((l.hold + (first.toUInt64 <<< l.bits.toUInt64)) +
        (second.toUInt64 <<< (l.bits + 8).toUInt64)) &&& c.lmask.toUInt64).toNat ∧
      selected.hold = (l.hold + (first.toUInt64 <<< l.bits.toUInt64)) +
        (second.toUInt64 <<< (l.bits + 8).toUInt64) ∧
      FastInputPacket h slowPrefix (third :: fourth :: fifth :: sixth :: rest) selected ∧
      DispatchBuffers h r slowPrefix (third :: fourth :: fifth :: sixth :: rest) ∧
      stream slowPrefix (third :: fourth :: fifth :: sixth :: rest) =
        stream slow (first :: second :: third :: fourth :: fifth :: sixth :: rest) ∧
      15 ≤ slowPrefix.bits.toNat ∧
      linked.here = .ref codeRef (baseOff + rootEntry.val.toNat + slice) ∧
      let target := codes.getD
        (baseOff + rootEntry.val.toNat + slice) default
      (target.op ≠ 0 ∧
        (target.op.toUInt32 &&& 16 != 0) = false ∧
        (target.op.toUInt32 &&& 64 == 0) = false ∧
        (target.op.toUInt32 &&& 32 != 0) = true) →
      decodeSym L
        (stream slow
          (first :: second :: third :: fourth :: fifth :: sixth :: rest)) =
        some (256,
          (stream slow
            (first :: second :: third :: fourth :: fifth :: sixth :: rest)).drop
            (rootEntry.bits.toNat + target.bits.toNat)) →
      ∃ (result : Zlib.Inffast.L) (after : Heap)
        (slowFinal : IL),
        C.run (Zlib.Inffast.inflate_fast_body c l) h =
          .ok (result, after) ∧
        after = setI h zs { s with mode := TYPE } ∧
        result.broke = true ∧
        FastInputPacket after slowFinal
          (third :: fourth :: fifth :: sixth :: rest) result ∧
        DispatchBuffers after r slowFinal
          (third :: fourth :: fifth :: sixth :: rest) ∧
        ZlibF.Spec.Token.Step L D dict history
          (stream slow
            (first :: second :: third :: fourth :: fifth :: sixth :: rest))
          (stream slowFinal
            (third :: fourth :: fifth :: sixth :: rest))
          history true ∧ result.in_ = inputAdvance l.in_ 2 := by
  obtain ⟨slow2, fast2, selected, rootSlice, prefixRun,
    selectedEq, selectedPacket, buffers2, _, source2,
    _, holdFrame, _, _, nextFrame, _, held2,
    _, rootSliceEq, rootBound⟩ :=
    packet.two_pull_root_prefix invariant buffers small
      lcodePtr codesGet safe mask
  have link : LenLink (codes.getD (baseOff + rootSlice) default) := by
    apply rootLink rootSlice rootBound
    rw [rootSliceEq, holdFrame]
  have herePtr : selected.here =
      .ref codeRef (baseOff + rootSlice) := by
    rw [selectedEq]
  obtain ⟨linked, slice, linkRun, againL, sliceBound, linkedHere, finish⟩ :=
    selectedPacket.dolen_linked_end_default_state
      invariant buffers2 statePtr mode herePtr lcodePtr
      codesGet safe rootBound link (by omega)
  refine ⟨slow2, selected, linked, rootSlice, slice,
    linkRun, againL, herePtr, (by rw [rootSliceEq, holdFrame]),
    (by simpa only [selectedEq] using holdFrame),
    selectedPacket, buffers2, source2, (by omega), linkedHere, ?_⟩
  dsimp only
  intro selectedEnd decoded
  obtain ⟨result, slowFinal, secondRun, loopRun, broke,
    _, finalPacket, _, finalBuffers, _, sourceDrop⟩ :=
    finish selectedEnd
  have needsPull : l.bits < 15 := by
    rw [packet.bits]
    exact UInt32.lt_iff_toNat_lt.mpr small
  have bodyRun := body_from_two_pull_root needsPull prefixRun loopRun
  have token : ZlibF.Spec.Token.Step L D dict history
      (stream slow
        (first :: second :: third :: fourth :: fifth :: sixth :: rest))
      (stream slowFinal (third :: fourth :: fifth :: sixth :: rest))
      history true := by
    rw [sourceDrop, source2]
    exact ZlibF.Spec.Token.Step.eob decoded
  refine ⟨result, setI h zs { s with mode := TYPE },
    slowFinal, bodyRun, rfl, broke, finalPacket,
    finalBuffers, token, ?_⟩
  let rootEntry := codes.getD (baseOff + rootSlice) default
  let target := codes.getD (baseOff + rootEntry.val.toNat + slice) default
  have targetBounds := len_table_link_target safe rootBound link sliceBound
  have targetBound : baseOff + rootEntry.val.toNat + slice < codes.size := by
    simpa only [Nat.add_assoc, rootEntry] using targetBounds.1
  have targetWidth : target.bits.toNat ≤ 15 := by
    have leaf : target.bits.toNat + rootEntry.bits.toNat ≤ 15 := by
      simpa only [target, rootEntry] using targetBounds.2.2
    omega
  have loaded : Ptr.load linked.here h = .ok (target, h) := by
    rw [linkedHere]
    have getD : target = codes[baseOff + rootEntry.val.toNat + slice] := by
      simp [target, Array.getD_eq_getD_getElem?, targetBound]
    rw [getD]
    exact Ptr.load_ok codesGet targetBound
  have nobase : (target.op.toUInt32 &&& 16 != 0) = false := selectedEnd.2.1
  have cursor := Zlib.Inffast.Proofs.dolen_two_pass_nobase_input_frame
    linkRun againL loaded targetWidth nobase secondRun
  have selectedCursor : selected.in_ = inputAdvance l.in_ 2 := by
    rw [selectedPacket.cursor, nextFrame, ← packet.cursor]
  rw [cursor, selectedCursor]

#print axioms linked_eob_body_two_pull_indexed_generic_cursor
end Zlib.Inflate.Proofs
