import ZlibF.Proof.«inflate.c.payload-valid-nopull-cursor-stage»
namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
set_option autoImplicit false
theorem linked_literal_body_two_pull_indexed_generic_with_out_cursor
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
    (left : slow.left ≠ 0)
    (avail : 258 ≤ slow.left.toNat)
    {dest : BRef} {output : Array UInt8}
    {oo j : Nat}
    (outPtr : l.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (endPtr : c.end_ = .ref dest (oo + slow.left.toNat - 257))
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (current : oo ≤ j)
    (guard : C.run (Ptr.lt l.out c.end_) h = .ok (true, h))
    {L D : List Nat} {dict history : List UInt8} :
    ∃ (slowPrefix : IL) (selected : Zlib.Inffast.L)
      (rootSlice : Nat) (linked : Zlib.Inffast.L)
      (slice : Nat),
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
      ∀ symbol : Nat,
        target.op = 0 →
        decodeSym L
          (stream slow
            (first :: second :: third :: fourth :: fifth :: sixth :: rest)) =
          some (symbol,
            (stream slow
              (first :: second :: third :: fourth :: fifth :: sixth :: rest)).drop
              (rootEntry.bits.toNat + target.bits.toNat)) →
        symbol < 256 → target.val.toNat = symbol →
        ∃ (result : Zlib.Inffast.L) (after : Heap)
          (slowFinal : IL),
          C.run (Zlib.Inffast.inflate_fast_body c l) h =
            .ok (result, after) ∧
          result.out = .ref dest (j + 1) ∧
          Space.get after dest = some
            (output.set! j target.val.toUInt8) ∧
          FastInputPacket after slowFinal
            (third :: fourth :: fifth :: sixth :: rest) result ∧
          DispatchBuffers after r slowFinal
            (third :: fourth :: fifth :: sixth :: rest) ∧
          ZlibF.Spec.Token.Step L D dict history
            (stream slow
              (first :: second :: third :: fourth :: fifth :: sixth :: rest))
            (stream slowFinal
              (third :: fourth :: fifth :: sixth :: rest))
            (history ++ [target.val.toUInt8]) false ∧
          result.in_ = inputAdvance l.in_ 2 := by
  obtain ⟨slow2, fast2, selected, rootSlice, prefixRun,
    selectedEq, selectedPacket, buffers2, _, source2,
    outFrame, holdFrame, putFrame, leftFrame,
    nextFrame, _, held2, _, rootSliceEq, rootBound⟩ :=
    packet.two_pull_root_prefix invariant buffers small
      lcodePtr codesGet safe mask
  have link : LenLink (codes.getD (baseOff + rootSlice) default) := by
    apply rootLink rootSlice rootBound
    rw [rootSliceEq, holdFrame]
  have herePtr : selected.here =
      .ref codeRef (baseOff + rootSlice) := by
    rw [selectedEq]
  have out2 : selected.out = .ref dest j :=
    outFrame.trans outPtr
  have put2 : slow2.put = .ref dest oo :=
    putFrame.trans outputPtr
  have left2 : slow2.left ≠ 0 := by
    rw [leftFrame]
    exact left
  have avail2 : 258 ≤ slow2.left.toNat := by
    rw [leftFrame]
    exact avail
  have end2 : c.end_ = .ref dest
      (oo + slow2.left.toNat - 257) := by
    rw [leftFrame]
    exact endPtr
  have size2 : oo + slow2.left.toNat ≤ output.size := by
    rw [leftFrame]
    exact outputSize
  have guard2 : C.run (Ptr.lt selected.out c.end_) h =
      .ok (true, h) := by
    rw [out2]
    simpa only [outPtr] using guard
  obtain ⟨linked, slice, slowLink, linkRun, againL,
    sliceBound, linkedHere, _, _, linkedSource, finish⟩ :=
    selectedPacket.dolen_linked_literal_default_state
      invariant buffers2 herePtr lcodePtr codesGet safe
      rootBound link (by omega) left2 avail2 out2 put2 end2
      outputGet outputWrite size2 current guard2
  refine ⟨slow2, selected, rootSlice, linked, slice,
    linkRun, againL, herePtr, (by rw [rootSliceEq, holdFrame]),
    (by simpa only [selectedEq] using holdFrame),
    selectedPacket, buffers2, source2, (by omega),
    linkedHere, ?_⟩
  dsimp only
  intro symbol literal decoded smallSymbol value
  obtain ⟨result, slowFinal, after, secondRun, loopRun, _,
    finalPacket, _, finalBuffers, _, outputAfter,
    _, _, sourceDrop⟩ := finish literal
  have needsPull : l.bits < 15 := by
    rw [packet.bits]
    exact UInt32.lt_iff_toNat_lt.mpr small
  have bodyRun := body_from_two_pull_root needsPull prefixRun loopRun
  have outAdvance : result.out = .ref dest (j + 1) :=
    selectedPacket.dolen_linked_literal_progress
      invariant buffers2 herePtr lcodePtr codesGet safe
      rootBound link (by omega) linkRun linkedHere sliceBound
      literal left2 avail2 out2 put2 end2 outputGet outputWrite
      size2 current guard2 loopRun
  have byte : (codes.getD
      (baseOff + (codes.getD (baseOff + rootSlice) default).val.toNat + slice)
        default).val.toUInt8 = symbol.toUInt8 := by
    apply UInt8.toNat_inj.mp
    simp only [UInt16.toNat_toUInt8, UInt8.toNat_ofNat']
    rw [value]
  have token : ZlibF.Spec.Token.Step L D dict history
      (stream slow
        (first :: second :: third :: fourth :: fifth :: sixth :: rest))
      (stream slowFinal (third :: fourth :: fifth :: sixth :: rest))
      (history ++ [(codes.getD
        (baseOff + (codes.getD (baseOff + rootSlice) default).val.toNat + slice)
          default).val.toUInt8]) false := by
    rw [sourceDrop, source2, byte]
    exact ZlibF.Spec.Token.Step.literal decoded smallSymbol
  refine ⟨result, after, slowFinal, bodyRun, outAdvance, outputAfter,
    finalPacket, finalBuffers, token, ?_⟩
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
  have nobase : (target.op.toUInt32 &&& 16 != 0) = false := by
    rw [literal]
    simp
  have cursor := Zlib.Inffast.Proofs.dolen_two_pass_nobase_input_frame
    linkRun againL loaded targetWidth nobase secondRun
  have selectedCursor : selected.in_ = inputAdvance l.in_ 2 := by
    rw [selectedPacket.cursor, nextFrame, ← packet.cursor]
  rw [cursor, selectedCursor]

#print axioms linked_literal_body_two_pull_indexed_generic_with_out_cursor
end Zlib.Inflate.Proofs
