import ZlibF.Proof.«inflate.c.payload-literal-nopull-cursor-stage»
namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec

/-- A no-refill root link whose selected second-level cell ends the block
runs the actual body and preserves the caller's unread same-object view. -/
theorem linked_eob_body_no_pull_indexed_generic_cursor
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow bs l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    (held : ¬ l.bits < 15)
    (statePtr : c.state = some (.tab zs))
    (mode : DataTableMode s.mode)
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff rootWidth : Nat}
    (lcodePtr : c.lcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : LenTableSafe codes baseOff rootWidth)
    (mask : c.lmask.toUInt64.toNat = 2 ^ rootWidth - 1)
    (rootLink : LenLink (codes.getD
      (baseOff + (l.hold &&& c.lmask.toUInt64).toNat) default))
    {L D : List Nat} {dict history : List UInt8} :
    ∃ (selected linked : Zlib.Inffast.L)
      (rootSlice slice : Nat),
      C.run (Zlib.Inffast.dolen c selected) h = .ok (linked, h) ∧
      linked.againL = true ∧
      selected.here = .ref codeRef (baseOff + rootSlice) ∧
      rootSlice = (l.hold &&& c.lmask.toUInt64).toNat ∧
      FastInputPacket h slow bs selected ∧
      linked.here = .ref codeRef
        (baseOff + (codes.getD (baseOff + rootSlice) default).val.toNat + slice) ∧
      let rootEntry := codes.getD (baseOff + rootSlice) default
      let target := codes.getD
        (baseOff + rootEntry.val.toNat + slice) default
      (target.op ≠ 0 ∧
        (target.op.toUInt32 &&& 16 != 0) = false ∧
        (target.op.toUInt32 &&& 64 == 0) = false ∧
        (target.op.toUInt32 &&& 32 != 0) = true) →
      decodeSym L (stream slow bs) =
        some (256, (stream slow bs).drop
          (rootEntry.bits.toNat + target.bits.toNat)) →
      ∃ (result : Zlib.Inffast.L) (after : Heap)
        (slowFinal : IL),
        C.run (Zlib.Inffast.inflate_fast_body c l) h =
          .ok (result, after) ∧
        after = setI h zs { s with mode := TYPE } ∧
        result.broke = true ∧
        FastInputPacket after slowFinal bs result ∧
        DispatchBuffers after r slowFinal bs ∧
        (bs ≠ [] → Bytes after slowFinal.next
          slowFinal.have_.toNat bs) ∧
        ZlibF.Spec.Token.Step L D dict history
          (stream slow bs) (stream slowFinal bs)
          history true ∧ result.in_ = l.in_ := by
  obtain ⟨rootBound, _, selectedPacket⟩ :=
    packet.fast_body_root_lookup lcodePtr codesGet safe mask
  let rootSlice := (l.hold &&& c.lmask.toUInt64).toNat
  let selected : Zlib.Inffast.L :=
    { l with here := .ref codeRef (baseOff + rootSlice) }
  have herePtr : selected.here =
      .ref codeRef (baseOff + rootSlice) := rfl
  have heldNat : 15 ≤ slow.bits.toNat := by
    have : ¬ slow.bits.toNat < 15 := by
      intro hsmall
      apply held
      apply UInt32.lt_iff_toNat_lt.mpr
      simpa only [← packet.bits, UInt32.toNat_ofNat] using hsmall
    omega
  obtain ⟨linked, slice, linkRun, againL,
    sliceBound, linkedHere, finish⟩ :=
    selectedPacket.dolen_linked_end_default_state
      invariant buffers statePtr mode herePtr lcodePtr
      codesGet safe rootBound rootLink heldNat
  refine ⟨selected, linked, rootSlice, slice,
    linkRun, againL, herePtr, rfl, selectedPacket,
    linkedHere, ?_⟩
  dsimp only
  intro selectedEnd decoded
  obtain ⟨result, slowFinal, secondRun, loopRun, broke,
    _, finalPacket, _, finalBuffers, _, sourceDrop⟩ :=
    finish selectedEnd
  have rootIndexBound : baseOff + rootSlice < codes.size := by
    have rootSize := safe.2.1
    omega
  have bodyRun := body_from_no_pull_root held lcodePtr
    codesGet rootIndexBound rfl rfl loopRun
  have read : bs ≠ [] → Bytes
      (setI h zs { s with mode := TYPE })
      slowFinal.next slowFinal.have_.toNat bs := by
    intro nonempty
    have actual := finalPacket.source.input_slice_of_nonempty nonempty
    simpa only [finalPacket.cursor] using actual
  have token : ZlibF.Spec.Token.Step L D dict history
      (stream slow bs) (stream slowFinal bs) history true := by
    rw [sourceDrop]
    exact ZlibF.Spec.Token.Step.eob decoded
  refine ⟨result, _, slowFinal, bodyRun, rfl, broke,
    finalPacket, finalBuffers, read, token, ?_⟩
  have targetBounds := len_table_link_target safe rootBound rootLink sliceBound
  let rootEntry := codes.getD (baseOff + rootSlice) default
  let target := codes.getD (baseOff + rootEntry.val.toNat + slice) default
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
  simpa only [selected] using cursor

#print axioms linked_eob_body_no_pull_indexed_generic_cursor
end Zlib.Inflate.Proofs
