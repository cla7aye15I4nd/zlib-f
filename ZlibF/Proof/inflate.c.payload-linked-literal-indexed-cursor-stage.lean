import ZlibF.Proof.«inflate.c.payload-unified-two-pull-output-cursor-stage-relinked»
import ZlibF.Proof.«inffast.c.dolen-nobase-input-frame»
namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
set_option autoImplicit false
theorem linked_literal_body_no_pull_indexed_generic_with_out_cursor
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow bs l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    (held : ¬ l.bits < 15)
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff rootWidth : Nat}
    (lcodePtr : c.lcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : LenTableSafe codes baseOff rootWidth)
    (mask : c.lmask.toUInt64.toNat = 2 ^ rootWidth - 1)
    (rootLink : LenLink (codes.getD
      (baseOff + (l.hold &&& c.lmask.toUInt64).toNat) default))
    (left : slow.left ≠ 0)
    (avail : 258 ≤ slow.left.toNat)
    {dest : BRef} {output : Array UInt8} {oo j : Nat}
    (outPtr : l.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (endPtr : c.end_ = .ref dest (oo + slow.left.toNat - 257))
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (current : oo ≤ j)
    (guard : C.run (Ptr.lt l.out c.end_) h = .ok (true, h))
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
      ∀ symbol : Nat,
        target.op = 0 →
        decodeSym L (stream slow bs) =
          some (symbol, (stream slow bs).drop
            (rootEntry.bits.toNat + target.bits.toNat)) →
        symbol < 256 → target.val.toNat = symbol →
        ∃ (result : Zlib.Inffast.L) (after : Heap)
          (slowFinal : IL),
          C.run (Zlib.Inffast.inflate_fast_body c l) h =
            .ok (result, after) ∧
          result.out = .ref dest (j + 1) ∧
          Space.get after dest = some
            (output.set! j target.val.toUInt8) ∧
          FastInputPacket after slowFinal bs result ∧
          DispatchBuffers after r slowFinal bs ∧
          (bs ≠ [] → Bytes after slowFinal.next
            slowFinal.have_.toNat bs) ∧
          ZlibF.Spec.Token.Step L D dict history
            (stream slow bs) (stream slowFinal bs)
            (history ++ [target.val.toUInt8]) false ∧
          result.in_ = l.in_ := by
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
  obtain ⟨linked, slice, slowLink, linkRun, againL,
    sliceBound, linkedHere, _, _, linkedSource, finish⟩ :=
    selectedPacket.dolen_linked_literal_default_state
      invariant buffers herePtr lcodePtr codesGet safe
      rootBound rootLink heldNat left avail outPtr outputPtr
      endPtr outputGet outputWrite outputSize current guard
  refine ⟨selected, linked, rootSlice, slice,
    linkRun, againL, herePtr, rfl, selectedPacket,
    linkedHere, ?_⟩
  dsimp only
  intro symbol literal decoded smallSymbol value
  obtain ⟨result, slowFinal, after, secondRun, loopRun, _,
    finalPacket, _, finalBuffers, _, outputAfter,
    _, _, sourceDrop⟩ := finish literal
  have rootIndexBound : baseOff + rootSlice < codes.size := by
    have rootSize := safe.2.1
    omega
  have bodyRun := body_from_no_pull_root held lcodePtr
    codesGet rootIndexBound rfl rfl loopRun
  have selectedOut : selected.out = .ref dest j := by
    simpa only [selected] using outPtr
  have selectedGuard : C.run (Ptr.lt selected.out c.end_) h =
      .ok (true, h) := by
    simpa only [selected] using guard
  have outAdvance : result.out = .ref dest (j + 1) :=
    selectedPacket.dolen_linked_literal_progress
      invariant buffers herePtr lcodePtr codesGet safe
      (by simpa only [rootSlice] using rootBound) rootLink heldNat
      linkRun linkedHere sliceBound literal left avail
      selectedOut outputPtr endPtr outputGet outputWrite
      outputSize current selectedGuard loopRun
  have byte : (codes.getD
      (baseOff + (codes.getD (baseOff + rootSlice) default).val.toNat + slice)
        default).val.toUInt8 = symbol.toUInt8 := by
    apply UInt8.toNat_inj.mp
    simp only [UInt16.toNat_toUInt8, UInt8.toNat_ofNat']
    rw [value]
  have token : ZlibF.Spec.Token.Step L D dict history
      (stream slow bs) (stream slowFinal bs)
      (history ++ [(codes.getD
        (baseOff + (codes.getD (baseOff + rootSlice) default).val.toNat + slice)
          default).val.toUInt8]) false := by
    rw [sourceDrop, byte]
    exact ZlibF.Spec.Token.Step.literal decoded smallSymbol
  have read : bs ≠ [] → Bytes after
      slowFinal.next slowFinal.have_.toNat bs := by
    intro nonempty
    have actual := finalPacket.source.input_slice_of_nonempty nonempty
    simpa only [finalPacket.cursor] using actual
  refine ⟨result, after, slowFinal, bodyRun, outAdvance, outputAfter,
    finalPacket, finalBuffers, read, token, ?_⟩
  let rootEntry := codes.getD (baseOff + rootSlice) default
  let target := codes.getD (baseOff + rootEntry.val.toNat + slice) default
  have targetBounds := len_table_link_target safe rootBound rootLink sliceBound
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
  have nobase : (target.op.toUInt32 &&& 16 != 0) = false := by
    rw [literal]
    simp
  have cursor := Zlib.Inffast.Proofs.dolen_two_pass_nobase_input_frame
    linkRun againL loaded targetWidth nobase secondRun
  simpa only [selected] using cursor

#print axioms linked_literal_body_no_pull_indexed_generic_with_out_cursor
end Zlib.Inflate.Proofs
