import ZlibF.Proof.«inflate.c.payload-generic-stage»
import ZlibF.Proof.«inflate.c.fast-view-linked-literal-progress-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
set_option autoImplicit false
theorem linked_literal_body_no_pull_indexed_generic_with_out
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
            (history ++ [target.val.toUInt8]) false := by
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
  obtain ⟨result, slowFinal, after, _, loopRun, _,
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
  exact ⟨result, after, slowFinal, bodyRun, outAdvance, outputAfter,
    finalPacket, finalBuffers, read, token⟩

#print axioms linked_literal_body_no_pull_indexed_generic_with_out
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
open Zlib.Inftrees.Spec Zlib.Inftrees.Spec.DecodeSemantics
open Zlib.Inftrees.Spec.DecodeSoundness Zlib.Inftrees.Spec.DecodeTableInvariant
open Zlib.Inftrees.Spec.Subtable
set_option autoImplicit false
theorem linked_literal_body_no_pull_of_decode_generic_with_out
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
    {used : Nat} {lens : List Nat}
    (meaning : Inv LENS codes baseOff rootWidth used lens)
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
    {D : List Nat} {dict history : List UInt8} {symbol : Nat} {r1 : List Bool}
    (decoded : decodeSym lens (stream slow bs) = some (symbol, r1))
    (smallSymbol : symbol < 256) :
    ∃ (byte : UInt8) (result : Zlib.Inffast.L) (after : Heap)
      (slowFinal : IL),
      C.run (Zlib.Inffast.inflate_fast_body c l) h = .ok (result, after) ∧
      result.out = .ref dest (j + 1) ∧
      Space.get after dest = some (output.set! j byte) ∧
      FastInputPacket after slowFinal bs result ∧
      DispatchBuffers after r slowFinal bs ∧
      ZlibF.Spec.Token.Step lens D dict history
        (stream slow bs) (stream slowFinal bs)
        (history ++ [byte]) false := by
  obtain ⟨selected, linked, rootSlice, slice,
    linkRun, againL, selectedHere, rootSliceEq,
    selectedPacket, linkedHere, finish⟩ :=
    linked_literal_body_no_pull_indexed_generic_with_out
      packet invariant buffers held lcodePtr codesGet safe mask rootLink
      left avail outPtr outputPtr endPtr outputGet outputWrite outputSize
      current guard (L := lens) (D := D) (dict := dict) (history := history)
  let rootEntry := codes.getD (baseOff + rootSlice) default
  have root : rootSlice < 2 ^ rootWidth := by
    rw [rootSliceEq, Zlib.Inffast.Proofs.u64_and_mask mask]
    exact Nat.mod_lt _ (Nat.pow_pos (by omega))
  have link : LenLink rootEntry := by
    simpa only [rootEntry, rootSliceEq] using rootLink
  have queryLink : IsLink LENS rootEntry = true :=
    (len_table_link_query safe root).mp link
  have selectedHold : selected.hold = l.hold := by
    exact selectedPacket.hold.trans packet.hold.symm
  have rootIndex : rootSlice = selected.hold.toNat % 2 ^ rootWidth := by
    rw [rootSliceEq, selectedHold,
      Zlib.Inffast.Proofs.u64_and_mask mask]
  have heldNat : 15 ≤ slow.bits.toNat := by
    have noSmall : ¬ slow.bits.toNat < 15 := by
      intro small
      apply held
      rw [packet.bits]
      exact UInt32.lt_iff_toNat_lt.mpr small
    omega
  obtain ⟨otherLinked, otherSlice, _, otherRun, _,
    otherHere, _, _, otherSliceEq, otherMeaning, otherRest⟩ :=
    selectedPacket.length_selected_link_match_of_decode
      invariant buffers selectedHere lcodePtr codesGet safe meaning
      root rootIndex link queryLink heldNat decoded (by omega)
  have linkedEq : otherLinked = linked := by
    have same := otherRun.symm.trans linkRun
    cases same
    rfl
  have sliceEq : otherSlice = slice := by
    have ptrEq :
        (Ptr.ref codeRef (baseOff + rootEntry.val.toNat + otherSlice) : CodePtr) =
        .ref codeRef (baseOff + rootEntry.val.toNat + slice) := by
      exact otherHere.symm.trans (by rw [linkedEq]; exact linkedHere)
    injection ptrEq with offEq
    omega
  let target := codes.getD (baseOff + rootEntry.val.toNat + slice) default
  have targetMeaning : SymbolEntry LENS symbol target := by
    simpa only [rootEntry, target, sliceEq] using otherMeaning
  obtain ⟨literal, value⟩ :=
    length_literal_entry_fields smallSymbol targetMeaning
  have codeRest : r1 = (stream slow bs).drop
      (rootEntry.bits.toNat + target.bits.toNat) := by
    simpa only [rootEntry, target, sliceEq] using otherRest
  have decodedExact : decodeSym lens (stream slow bs) =
      some (symbol, (stream slow bs).drop
        (rootEntry.bits.toNat + target.bits.toNat)) := by
    rw [← codeRest]
    exact decoded
  obtain ⟨result, after, slowFinal, run, out, get, packetFinal,
    buffersFinal, _, token⟩ :=
    finish symbol literal decodedExact smallSymbol value
  exact ⟨target.val.toUInt8, result, after, slowFinal,
    run, out, get, packetFinal, buffersFinal, token⟩

#print axioms linked_literal_body_no_pull_of_decode_generic_with_out
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
set_option autoImplicit false
theorem linked_literal_body_two_pull_indexed_generic_with_out
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
            (history ++ [target.val.toUInt8]) false := by
  obtain ⟨slow2, fast2, selected, rootSlice, prefixRun,
    selectedEq, selectedPacket, buffers2, _, source2,
    outFrame, holdFrame, putFrame, leftFrame,
    _, _, held2, _, rootSliceEq, rootBound⟩ :=
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
  obtain ⟨result, slowFinal, after, _, loopRun, _,
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
  exact ⟨result, after, slowFinal, bodyRun, outAdvance, outputAfter,
    finalPacket, finalBuffers, token⟩

#print axioms linked_literal_body_two_pull_indexed_generic_with_out
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
open Zlib.Inftrees.Spec Zlib.Inftrees.Spec.DecodeSemantics
open Zlib.Inftrees.Spec.DecodeSoundness Zlib.Inftrees.Spec.DecodeTableInvariant
open Zlib.Inftrees.Spec.Subtable
set_option autoImplicit false
theorem linked_literal_body_two_pull_of_decode_generic_with_out
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
    {used : Nat} {lens : List Nat}
    (meaning : Inv LENS codes baseOff rootWidth used lens)
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
    {D : List Nat} {dict history : List UInt8} {symbol : Nat} {r1 : List Bool}
    (decoded : decodeSym lens
      (stream slow (first :: second :: third :: fourth :: fifth :: sixth :: rest)) =
      some (symbol, r1))
    (smallSymbol : symbol < 256) :
    ∃ (byte : UInt8) (result : Zlib.Inffast.L) (after : Heap)
      (slowFinal : IL),
      C.run (Zlib.Inffast.inflate_fast_body c l) h = .ok (result, after) ∧
      result.out = .ref dest (j + 1) ∧
      Space.get after dest = some (output.set! j byte) ∧
      FastInputPacket after slowFinal
        (third :: fourth :: fifth :: sixth :: rest) result ∧
      DispatchBuffers after r slowFinal
        (third :: fourth :: fifth :: sixth :: rest) ∧
      ZlibF.Spec.Token.Step lens D dict history
        (stream slow (first :: second :: third :: fourth :: fifth :: sixth :: rest))
        (stream slowFinal (third :: fourth :: fifth :: sixth :: rest))
        (history ++ [byte]) false := by
  obtain ⟨slow2, selected, rootSlice, linked, slice,
    linkRun, againL, selectedHere, rootSliceEq,
    selectedHold, selectedPacket, buffers2, source2, held2,
    linkedHere, finish⟩ :=
    linked_literal_body_two_pull_indexed_generic_with_out
      packet invariant buffers small lcodePtr codesGet safe mask
      rootLink left avail outPtr outputPtr endPtr
      outputGet outputWrite outputSize current guard
      (L := lens) (D := D) (dict := dict) (history := history)
  let raw4 := third :: fourth :: fifth :: sixth :: rest
  let rootEntry := codes.getD (baseOff + rootSlice) default
  have root : rootSlice < 2 ^ rootWidth := by
    rw [rootSliceEq, Zlib.Inffast.Proofs.u64_and_mask mask]
    exact Nat.mod_lt _ (Nat.pow_pos (by omega))
  have link : LenLink rootEntry := by
    apply rootLink rootSlice root
    exact rootSliceEq
  have queryLink : IsLink LENS rootEntry = true :=
    (len_table_link_query safe root).mp link
  have rootIndex : rootSlice = selected.hold.toNat % 2 ^ rootWidth := by
    rw [rootSliceEq, selectedHold,
      Zlib.Inffast.Proofs.u64_and_mask mask]
  have decoded2 : decodeSym lens (stream slow2 raw4) =
      some (symbol, r1) := by
    rw [source2]
    exact decoded
  obtain ⟨otherLinked, otherSlice, _, otherRun, _,
    otherHere, _, _, otherSliceEq, otherMeaning, otherRest⟩ :=
    selectedPacket.length_selected_link_match_of_decode
      invariant buffers2
      selectedHere lcodePtr codesGet safe meaning root rootIndex
      link queryLink held2 decoded2 (by omega)
  have linkedEq : otherLinked = linked := by
    have same := otherRun.symm.trans linkRun
    cases same
    rfl
  have sliceEq : otherSlice = slice := by
    have ptrEq :
        (Ptr.ref codeRef (baseOff + rootEntry.val.toNat + otherSlice) : CodePtr) =
        .ref codeRef (baseOff + rootEntry.val.toNat + slice) := by
      exact otherHere.symm.trans (by rw [linkedEq]; exact linkedHere)
    injection ptrEq with offEq
    omega
  have actualSliceEq : slice =
      (selected.hold >>> rootEntry.bits.toUInt32.toUInt64).toNat %
        2 ^ rootEntry.op.toNat := by
    rw [← sliceEq]
    exact otherSliceEq
  let target := codes.getD (baseOff + rootEntry.val.toNat + slice) default
  have targetMeaning : SymbolEntry LENS symbol target := by
    simpa only [rootEntry, target, sliceEq] using otherMeaning
  obtain ⟨literal, value⟩ :=
    length_literal_entry_fields smallSymbol targetMeaning
  have codeRest : r1 = (stream slow
      (first :: second :: third :: fourth :: fifth :: sixth :: rest)).drop
      (rootEntry.bits.toNat + target.bits.toNat) := by
    rw [source2] at otherRest
    simpa only [rootEntry, target, sliceEq] using otherRest
  have decodedExact : decodeSym lens
      (stream slow (first :: second :: third :: fourth :: fifth :: sixth :: rest)) =
      some (symbol, (stream slow
        (first :: second :: third :: fourth :: fifth :: sixth :: rest)).drop
          (rootEntry.bits.toNat + target.bits.toNat)) := by
    rw [← codeRest]
    exact decoded
  obtain ⟨result, after, slowFinal, run, out, get, packetFinal,
    buffersFinal, token⟩ :=
    finish symbol literal decodedExact smallSymbol value
  exact ⟨target.val.toUInt8, result, after, slowFinal,
    run, out, get, packetFinal, buffersFinal, token⟩

#print axioms linked_literal_body_two_pull_of_decode_generic_with_out
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
set_option autoImplicit false
theorem literal_body_no_pull_generic_with_packet
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow bs l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    (held : ¬ l.bits < 15)
    {lenRef : CodeRef} {lenCodes : Array Code}
    {baseOff index : Nat}
    (rootPtr : c.lcode = .ref lenRef baseOff)
    (indexEq : index = baseOff + (l.hold &&& c.lmask.toUInt64).toNat)
    (lenGet : Space.get h lenRef = some lenCodes)
    (indexBound : index < lenCodes.size)
    (codeFits : lenCodes[index].bits.toNat ≤ slow.bits.toNat)
    (codeWidth : lenCodes[index].bits.toNat ≤ 15)
    (literal : lenCodes[index].op = 0)
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
    {L D : List Nat} {dict history : List UInt8} {symbol : Nat}
    (decoded : decodeSym L (stream slow bs) =
      some (symbol, (stream slow bs).drop lenCodes[index].bits.toNat))
    (small : symbol < 256)
    (value : lenCodes[index].val.toNat = symbol) :
    ∃ result after slowNext,
      C.run (Zlib.Inffast.inflate_fast_body c l) h =
        .ok (result, after) ∧
      result.out = .ref dest (j + 1) ∧
      after = Space.put h dest
        (output.set! j lenCodes[index].val.toUInt8) ∧
      SliceEnv h after slow slowNext bs ∧
      FastInputPacket after slowNext bs result ∧
      DispatchBuffers after r slowNext bs ∧
      ZlibF.Spec.Token.Step L D dict history (stream slow bs)
        (stream slowNext bs)
        (history ++ [lenCodes[index].val.toUInt8]) false := by
  let selected : Zlib.Inffast.L :=
    { l with here := .ref lenRef index }
  have selectedPacket : FastInputPacket h slow bs selected :=
    ⟨packet.source, packet.cursor, packet.hold, packet.bits⟩
  have selectedOut : selected.out = .ref dest j := outPtr
  have selectedGuard : C.run (Ptr.lt selected.out c.end_) h =
      .ok (true, h) := guard
  have literalResult := literal_token_view_generic
    (L := L) (D := D) (dict := dict) (history := history) selectedPacket
    invariant buffers (by rfl) lenGet indexBound codeFits codeWidth
    literal left avail selectedOut outputPtr endPtr
    outputGet outputWrite outputSize current selectedGuard
    decoded small value
  dsimp only at literalResult
  obtain ⟨dolenRun, slice, finalBuffers, token⟩ := literalResult
  have loopRun := dolen_loop_one dolenRun (by rfl)
  have addRun : C.run
      (c.lcode.add (l.hold &&& c.lmask.toUInt64).toNat) h =
      .ok ((.ref lenRef index), h) := by
    rw [rootPtr, indexEq]
    exact Ptr.add_nat_ok lenGet (by omega)
  have bodyPrefix : C.run (Zlib.Inffast.inflate_fast_body c l) h =
      C.run (cdoWhile (Zlib.Inffast.dolen c)
        (fun current => pure (current.againL, current)) selected) h := by
    unfold Zlib.Inffast.inflate_fast_body
    simp only [held, ite_false]
    unfold C.run at addRun ⊢
    simp only [bind_app, addRun]
    rfl
  have finalPacket : FastInputPacket
      (Space.put h dest (output.set! j lenCodes[index].val.toUInt8))
      { slow with
        hold := slow.hold >>> lenCodes[index].bits.toUInt32.toUInt64,
        bits := slow.bits - lenCodes[index].bits.toUInt32 } bs
      { selected with
        againL := false, op := lenCodes[index].op.toUInt32,
        hold := selected.hold >>> lenCodes[index].bits.toUInt32.toUInt64,
        bits := selected.bits - lenCodes[index].bits.toUInt32,
        out := .ref dest (j + 1) } := by
    refine ⟨slice.afterBits, ?_, ?_, ?_⟩
    · exact selectedPacket.cursor
    · exact congrArg (fun x : UInt64 =>
        x >>> lenCodes[index].bits.toUInt32.toUInt64) selectedPacket.hold
    · exact congrArg (fun x : UInt32 =>
        x - lenCodes[index].bits.toUInt32) selectedPacket.bits
  exact ⟨_, _, _, bodyPrefix.trans loopRun, rfl, rfl,
    slice, finalPacket, finalBuffers, token⟩

#print axioms literal_body_no_pull_generic_with_packet
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
open Zlib.Inftrees.Spec Zlib.Inftrees.Spec.DecodeSemantics
open Zlib.Inftrees.Spec.DecodeSoundness Zlib.Inftrees.Spec.DecodeTableInvariant
open Zlib.Inftrees.Spec.Subtable
set_option autoImplicit false
theorem literal_body_no_pull_of_decode_generic_with_packet
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow bs l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    (held : ¬ l.bits < 15)
    (heldNat : 15 ≤ slow.bits.toNat)
    {lenRef : CodeRef} {lenCodes : Array Code}
    {baseOff index rootWidth used : Nat} {lens : List Nat}
    (rootPtr : c.lcode = .ref lenRef baseOff)
    (indexEq : index = baseOff + (l.hold &&& c.lmask.toUInt64).toNat)
    (lenGet : Space.get h lenRef = some lenCodes)
    (meaning : Inv LENS lenCodes baseOff rootWidth used lens)
    (mask : c.lmask.toUInt64.toNat = 2 ^ rootWidth - 1)
    (rootFits : rootWidth ≤ slow.bits.toNat)
    (noLink : IsLink LENS
      (lenCodes.getD (baseOff + l.hold.toNat % 2 ^ rootWidth) default) = false)
    (indexBound : index < lenCodes.size)
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
    {D : List Nat} {dict history : List UInt8} {symbol : Nat}
    (decoded : decodeSym lens (stream slow bs) =
      some (symbol, (stream slow bs).drop lenCodes[index].bits.toNat))
    (small : symbol < 256)
    :
    ∃ result after slowNext,
      C.run (Zlib.Inffast.inflate_fast_body c l) h =
        .ok (result, after) ∧
      result.out = .ref dest (j + 1) ∧
      after = Space.put h dest
        (output.set! j lenCodes[index].val.toUInt8) ∧
      SliceEnv h after slow slowNext bs ∧
      FastInputPacket after slowNext bs result ∧
      DispatchBuffers after r slowNext bs ∧
      ZlibF.Spec.Token.Step lens D dict history (stream slow bs)
        (stream slowNext bs)
        (history ++ [lenCodes[index].val.toUInt8]) false := by
  have valid : ValidSymbol LENS symbol := by
    simpa [ValidSymbol] using (show symbol ≤ 285 by omega)
  obtain ⟨_, symbolMeaning, width, _⟩ :=
    packet.length_root_leaf_of_decode meaning rootFits heldNat noLink
      decoded valid
  have maskIndex : (l.hold &&& c.lmask.toUInt64).toNat =
      l.hold.toNat % 2 ^ rootWidth :=
    Zlib.Inffast.Proofs.u64_and_mask mask
  have entryEq :
      lenCodes.getD (baseOff + l.hold.toNat % 2 ^ rootWidth) default =
      lenCodes[index] := by
    rw [← maskIndex, ← indexEq]
    simp [Array.getD_eq_getD_getElem?, indexBound]
  have fields := length_literal_entry_fields small symbolMeaning
  have literal : lenCodes[index].op = 0 := by
    simpa only [entryEq] using fields.1
  have value : lenCodes[index].val.toNat = symbol := by
    simpa only [entryEq] using fields.2
  have codeFits : lenCodes[index].bits.toNat ≤ slow.bits.toNat := by
    have rootEntry := meaning.rootTable.2.2.2
      (l.hold.toNat % 2 ^ rootWidth)
      (Nat.mod_lt _ (Nat.pow_pos (by omega)))
    obtain ⟨entry, get, _, bitsLe⟩ := rootEntry
    have eq : entry = lenCodes[index] := by
      have cell : lenCodes[baseOff + l.hold.toNat % 2 ^ rootWidth]? =
          some lenCodes[index] := by
        rw [← maskIndex, ← indexEq]
        simp [indexBound]
      exact Option.some.inj (get.symm.trans cell)
    rw [eq] at bitsLe
    omega
  have codeWidth : lenCodes[index].bits.toNat ≤ 15 := by
    have rootEntry := meaning.rootTable.2.2.2
      (l.hold.toNat % 2 ^ rootWidth)
      (Nat.mod_lt _ (Nat.pow_pos (by omega)))
    obtain ⟨entry, get, _, bitsLe⟩ := rootEntry
    have eq : entry = lenCodes[index] := by
      have cell : lenCodes[baseOff + l.hold.toNat % 2 ^ rootWidth]? =
          some lenCodes[index] := by
        rw [← maskIndex, ← indexEq]
        simp [indexBound]
      exact Option.some.inj (get.symm.trans cell)
    rw [eq] at bitsLe
    have rootLe := meaning.rootTable.2.1
    omega
  exact literal_body_no_pull_generic_with_packet packet invariant buffers held
    rootPtr indexEq lenGet indexBound codeFits codeWidth literal
    left avail outPtr outputPtr endPtr outputGet outputWrite
    outputSize current guard decoded small value

#print axioms literal_body_no_pull_of_decode_generic_with_packet
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
open Zlib.Inftrees.Spec Zlib.Inftrees.Spec.DecodeSemantics
open Zlib.Inftrees.Spec.DecodeSoundness Zlib.Inftrees.Spec.DecodeTableInvariant
open Zlib.Inftrees.Spec.Subtable
set_option autoImplicit false

/-- One no-refill literal token, whether the actual length root is direct or linked. -/
theorem FastInputPacket.fast_body_no_pull_literal_of_decode_generic
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow bs l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    (held : ¬ l.bits < 15)
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff rootWidth used : Nat} {lens : List Nat}
    (lcodePtr : c.lcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : LenTableSafe codes baseOff rootWidth)
    (meaning : Inv LENS codes baseOff rootWidth used lens)
    (mask : c.lmask.toUInt64.toNat = 2 ^ rootWidth - 1)
    (rootFits : rootWidth ≤ slow.bits.toNat)
    (left : slow.left ≠ 0) (avail : 258 ≤ slow.left.toNat)
    {dest : BRef} {output : Array UInt8} {oo j : Nat}
    (outPtr : l.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (endPtr : c.end_ = .ref dest (oo + slow.left.toNat - 257))
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (current : oo ≤ j)
    (guard : C.run (Ptr.lt l.out c.end_) h = .ok (true, h))
    {D : List Nat} {dict history : List UInt8}
    {symbol : Nat} {r1 : List Bool}
    (decoded : decodeSym lens (stream slow bs) = some (symbol, r1))
    (smallSymbol : symbol < 256) :
    ∃ (byte : UInt8) (result : Zlib.Inffast.L) (after : Heap)
      (slowFinal : IL),
      C.run (Zlib.Inffast.inflate_fast_body c l) h = .ok (result, after) ∧
      result.out = .ref dest (j + 1) ∧
      Space.get after dest = some (output.set! j byte) ∧
      FastInputPacket after slowFinal bs result ∧
      DispatchBuffers after r slowFinal bs ∧
      ZlibF.Spec.Token.Step lens D dict history
        (stream slow bs) (stream slowFinal bs)
        (history ++ [byte]) false := by
  let rootSlice := (l.hold &&& c.lmask.toUInt64).toNat
  have maskIndex : rootSlice = l.hold.toNat % 2 ^ rootWidth :=
    Zlib.Inffast.Proofs.u64_and_mask mask
  have root : rootSlice < 2 ^ rootWidth := by
    rw [maskIndex]
    exact Nat.mod_lt _ (Nat.pow_pos (by omega))
  by_cases link : LenLink (codes.getD (baseOff + rootSlice) default)
  · exact linked_literal_body_no_pull_of_decode_generic_with_out
      packet invariant buffers held lcodePtr codesGet safe meaning
      mask link left avail outPtr outputPtr endPtr outputGet outputWrite
      outputSize current guard decoded smallSymbol
  · have noLink : IsLink LENS
        (codes.getD (baseOff + l.hold.toNat % 2 ^ rootWidth) default) = false := by
      cases hq : IsLink LENS (codes.getD (baseOff + rootSlice) default) with
      | false => simpa only [← maskIndex] using hq
      | true => exact False.elim (link ((len_table_link_query safe root).mpr hq))
    have heldNat : 15 ≤ slow.bits.toNat := by
      have noSmall : ¬ slow.bits.toNat < 15 := by
        intro small
        apply held
        rw [packet.bits]
        exact UInt32.lt_iff_toNat_lt.mpr small
      omega
    have valid : ValidSymbol LENS symbol := by
      simpa [ValidSymbol] using (show symbol ≤ 285 by omega)
    obtain ⟨_, _, _, restEq⟩ :=
      packet.length_root_leaf_of_decode meaning rootFits heldNat
        noLink decoded valid
    let index := baseOff + rootSlice
    have indexBound : index < codes.size := by
      have rootSize := safe.2.1
      omega
    have entryEq : codes.getD (baseOff + l.hold.toNat % 2 ^ rootWidth)
        default = codes[index] := by
      rw [← maskIndex]
      simp [index, Array.getD_eq_getD_getElem?, indexBound]
    have decodedExact : decodeSym lens (stream slow bs) =
        some (symbol, (stream slow bs).drop codes[index].bits.toNat) := by
      rw [entryEq] at restEq
      rw [← restEq]
      exact decoded
    obtain ⟨result, after, slowFinal, run, out, afterEq,
      _, finalPacket, finalBuffers, token⟩ :=
      literal_body_no_pull_of_decode_generic_with_packet
        packet invariant buffers held heldNat lcodePtr rfl codesGet
        meaning mask rootFits noLink indexBound left avail outPtr
        outputPtr endPtr outputGet outputWrite outputSize current guard
        decodedExact smallSymbol
    have get : Space.get after dest = some
        (output.set! j codes[index].val.toUInt8) := by
      rw [afterEq]
      exact byte_view_get_put outputGet outputWrite _
    exact ⟨codes[index].val.toUInt8, result, after, slowFinal,
      run, out, get, finalPacket, finalBuffers, token⟩

#print axioms FastInputPacket.fast_body_no_pull_literal_of_decode_generic
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
set_option autoImplicit false
theorem eob_body_no_pull_generic_with_packet
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
    {baseOff index : Nat}
    (rootPtr : c.lcode = .ref codeRef baseOff)
    (indexEq : index = baseOff + (l.hold &&& c.lmask.toUInt64).toNat)
    (codesGet : Space.get h codeRef = some codes)
    (indexBound : index < codes.size)
    (codeFits : codes[index].bits.toNat ≤ slow.bits.toNat)
    (codeWidth : codes[index].bits.toNat ≤ 15)
    (nonzero : codes[index].op ≠ 0)
    (notBase : (codes[index].op.toUInt32 &&& 16 != 0) = false)
    (notLink : (codes[index].op.toUInt32 &&& 64 == 0) = false)
    (endCode : (codes[index].op.toUInt32 &&& 32 != 0) = true)
    {L D : List Nat} {dict history : List UInt8}
    (decoded : decodeSym L (stream slow bs) =
      some (256, (stream slow bs).drop codes[index].bits.toNat)) :
    ∃ result after slowNext,
      C.run (Zlib.Inffast.inflate_fast_body c l) h =
        .ok (result, after) ∧
      after = setI h zs { s with mode := TYPE } ∧
      result.broke = true ∧ result.out = l.out ∧
      SliceEnv h after slow slowNext bs ∧
      FastInputPacket after slowNext bs result ∧
      DispatchBuffers after r slowNext bs ∧
      ZlibF.Spec.Token.Step L D dict history
        (stream slow bs) (stream slowNext bs) history true := by
  let selected : Zlib.Inffast.L :=
    { l with here := .ref codeRef index }
  have selectedPacket : FastInputPacket h slow bs selected :=
    ⟨packet.source, packet.cursor, packet.hold, packet.bits⟩
  obtain ⟨result, slowNext, dolenRun, broke,
    noAgain, inputFrame, outputFrame, finalPacket, _,
    finalBuffers, _, sourceDrop⟩ :=
    selectedPacket.dolen_end_leaf_default_state
      invariant buffers statePtr mode (by rfl) codesGet
      indexBound codeFits codeWidth nonzero notBase notLink endCode
  have addRun : C.run
      (c.lcode.add (l.hold &&& c.lmask.toUInt64).toNat) h =
      .ok ((.ref codeRef index), h) := by
    rw [rootPtr, indexEq]
    exact Ptr.add_nat_ok codesGet (by omega)
  have bodyPrefix : C.run (Zlib.Inffast.inflate_fast_body c l) h =
      C.run (cdoWhile (Zlib.Inffast.dolen c)
        (fun current => pure (current.againL, current)) selected) h := by
    unfold Zlib.Inffast.inflate_fast_body
    simp only [held, ite_false]
    unfold C.run at addRun ⊢
    simp only [bind_app, addRun]
    rfl
  have loopRun := dolen_loop_one dolenRun noAgain
  have slice : SliceEnv h
      (setI h zs { s with mode := TYPE }) slow slowNext bs := by
    refine ⟨packet.source, finalPacket.source, ?_, ?_⟩
    · rw [← finalPacket.cursor]
      rw [inputFrame]
      exact selectedPacket.cursor
    · apply UInt32.toNat_inj.mp
      rw [finalPacket.source.have_eq, packet.source.have_eq]
  have token : ZlibF.Spec.Token.Step L D dict history
      (stream slow bs) (stream slowNext bs) history true := by
    rw [sourceDrop]
    exact ZlibF.Spec.Token.Step.eob decoded
  exact ⟨result, _, slowNext, bodyPrefix.trans loopRun,
    rfl, broke, outputFrame, slice, finalPacket,
    finalBuffers, token⟩

#print axioms eob_body_no_pull_generic_with_packet
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
open Zlib.Inftrees.Spec Zlib.Inftrees.Spec.DecodeSemantics
open Zlib.Inftrees.Spec.DecodeSoundness Zlib.Inftrees.Spec.DecodeTableInvariant
open Zlib.Inftrees.Spec.Subtable
set_option autoImplicit false
theorem eob_body_no_pull_of_decode_generic_with_packet
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow bs l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    (held : ¬ l.bits < 15)
    (heldNat : 15 ≤ slow.bits.toNat)
    (statePtr : c.state = some (.tab zs))
    (mode : DataTableMode s.mode)
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff index rootWidth used : Nat} {lens : List Nat}
    (rootPtr : c.lcode = .ref codeRef baseOff)
    (indexEq : index = baseOff + (l.hold &&& c.lmask.toUInt64).toNat)
    (codesGet : Space.get h codeRef = some codes)
    (meaning : Inv LENS codes baseOff rootWidth used lens)
    (mask : c.lmask.toUInt64.toNat = 2 ^ rootWidth - 1)
    (rootFits : rootWidth ≤ slow.bits.toNat)
    (noLink : IsLink LENS
      (codes.getD (baseOff + l.hold.toNat % 2 ^ rootWidth) default) = false)
    (indexBound : index < codes.size)
    {D : List Nat} {dict history : List UInt8}
    (decoded : decodeSym lens (stream slow bs) =
      some (256, (stream slow bs).drop codes[index].bits.toNat)) :
    ∃ result after slowNext,
      C.run (Zlib.Inffast.inflate_fast_body c l) h =
        .ok (result, after) ∧
      after = setI h zs { s with mode := TYPE } ∧
      result.broke = true ∧ result.out = l.out ∧
      SliceEnv h after slow slowNext bs ∧
      FastInputPacket after slowNext bs result ∧
      DispatchBuffers after r slowNext bs ∧
      ZlibF.Spec.Token.Step lens D dict history
        (stream slow bs) (stream slowNext bs) history true := by
  have valid : ValidSymbol LENS 256 := by
    simp [ValidSymbol]
  obtain ⟨_, symbolMeaning, _, _⟩ :=
    packet.length_root_leaf_of_decode meaning rootFits heldNat noLink
      decoded valid
  have maskIndex : (l.hold &&& c.lmask.toUInt64).toNat =
      l.hold.toNat % 2 ^ rootWidth :=
    Zlib.Inffast.Proofs.u64_and_mask mask
  have entryEq :
      codes.getD (baseOff + l.hold.toNat % 2 ^ rootWidth) default =
      codes[index] := by
    rw [← maskIndex, ← indexEq]
    simp [Array.getD_eq_getD_getElem?, indexBound]
  obtain ⟨nonzero, notBase, notLink, endCode⟩ :=
    length_eob_entry_fields symbolMeaning
  have nonzero' : codes[index].op ≠ 0 := by
    simpa only [entryEq] using nonzero
  have notBase' : (codes[index].op.toUInt32 &&& 16 != 0) = false := by
    simpa only [entryEq] using notBase
  have notLink' : (codes[index].op.toUInt32 &&& 64 == 0) = false := by
    simpa only [entryEq] using notLink
  have endCode' : (codes[index].op.toUInt32 &&& 32 != 0) = true := by
    simpa only [entryEq] using endCode
  have codeFits : codes[index].bits.toNat ≤ slow.bits.toNat := by
    have rootEntry := meaning.rootTable.2.2.2
      (l.hold.toNat % 2 ^ rootWidth)
      (Nat.mod_lt _ (Nat.pow_pos (by omega)))
    obtain ⟨entry, get, _, bitsLe⟩ := rootEntry
    have eq : entry = codes[index] := by
      have cell : codes[baseOff + l.hold.toNat % 2 ^ rootWidth]? =
          some codes[index] := by
        rw [← maskIndex, ← indexEq]
        simp [indexBound]
      exact Option.some.inj (get.symm.trans cell)
    rw [eq] at bitsLe
    omega
  have codeWidth : codes[index].bits.toNat ≤ 15 := by
    have rootEntry := meaning.rootTable.2.2.2
      (l.hold.toNat % 2 ^ rootWidth)
      (Nat.mod_lt _ (Nat.pow_pos (by omega)))
    obtain ⟨entry, get, _, bitsLe⟩ := rootEntry
    have eq : entry = codes[index] := by
      have cell : codes[baseOff + l.hold.toNat % 2 ^ rootWidth]? =
          some codes[index] := by
        rw [← maskIndex, ← indexEq]
        simp [indexBound]
      exact Option.some.inj (get.symm.trans cell)
    rw [eq] at bitsLe
    have rootLe := meaning.rootTable.2.1
    omega
  exact eob_body_no_pull_generic_with_packet packet invariant buffers held
    statePtr mode rootPtr indexEq codesGet indexBound codeFits codeWidth
    nonzero' notBase' notLink' endCode' decoded

#print axioms eob_body_no_pull_of_decode_generic_with_packet
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
open Zlib.Inftrees.Spec Zlib.Inftrees.Spec.DecodeSemantics
open Zlib.Inftrees.Spec.DecodeSoundness Zlib.Inftrees.Spec.DecodeTableInvariant
open Zlib.Inftrees.Spec.Subtable
set_option autoImplicit false

/-- One no-refill end-of-block token, whether the actual length root is direct or linked. -/
theorem FastInputPacket.fast_body_no_pull_eob_of_decode_generic
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
    {baseOff rootWidth used : Nat} {lens : List Nat}
    (lcodePtr : c.lcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : LenTableSafe codes baseOff rootWidth)
    (meaning : Inv LENS codes baseOff rootWidth used lens)
    (mask : c.lmask.toUInt64.toNat = 2 ^ rootWidth - 1)
    (rootFits : rootWidth ≤ slow.bits.toNat)
    {D : List Nat} {dict history : List UInt8} {r1 : List Bool}
    (decoded : decodeSym lens (stream slow bs) = some (256, r1)) :
    ∃ (result : Zlib.Inffast.L) (after : Heap) (slowFinal : IL),
      C.run (Zlib.Inffast.inflate_fast_body c l) h = .ok (result, after) ∧
      after = setI h zs { s with mode := TYPE } ∧
      result.broke = true ∧
      FastInputPacket after slowFinal bs result ∧
      DispatchBuffers after r slowFinal bs ∧
      ZlibF.Spec.Token.Step lens D dict history
        (stream slow bs) (stream slowFinal bs) history true := by
  let rootSlice := (l.hold &&& c.lmask.toUInt64).toNat
  have maskIndex : rootSlice = l.hold.toNat % 2 ^ rootWidth :=
    Zlib.Inffast.Proofs.u64_and_mask mask
  have root : rootSlice < 2 ^ rootWidth := by
    rw [maskIndex]
    exact Nat.mod_lt _ (Nat.pow_pos (by omega))
  by_cases link : LenLink (codes.getD (baseOff + rootSlice) default)
  · exact linked_eob_body_no_pull_of_decode_generic
      packet invariant buffers held statePtr mode lcodePtr codesGet
      safe meaning mask link decoded
  · have noLink : IsLink LENS
        (codes.getD (baseOff + l.hold.toNat % 2 ^ rootWidth) default) = false := by
      cases hq : IsLink LENS (codes.getD (baseOff + rootSlice) default) with
      | false => simpa only [← maskIndex] using hq
      | true => exact False.elim (link ((len_table_link_query safe root).mpr hq))
    have heldNat : 15 ≤ slow.bits.toNat := by
      have noSmall : ¬ slow.bits.toNat < 15 := by
        intro small
        apply held
        rw [packet.bits]
        exact UInt32.lt_iff_toNat_lt.mpr small
      omega
    obtain ⟨_, _, _, restEq⟩ :=
      packet.length_root_leaf_of_decode meaning rootFits heldNat
        noLink decoded (by simp [ValidSymbol])
    let index := baseOff + rootSlice
    have indexBound : index < codes.size := by
      have rootSize := safe.2.1
      omega
    have entryEq : codes.getD (baseOff + l.hold.toNat % 2 ^ rootWidth)
        default = codes[index] := by
      rw [← maskIndex]
      simp [index, Array.getD_eq_getD_getElem?, indexBound]
    have decodedExact : decodeSym lens (stream slow bs) =
        some (256, (stream slow bs).drop codes[index].bits.toNat) := by
      rw [entryEq] at restEq
      rw [← restEq]
      exact decoded
    obtain ⟨result, after, slowFinal, run, afterEq, broke,
      _, _, finalPacket, finalBuffers, token⟩ :=
      eob_body_no_pull_of_decode_generic_with_packet
        packet invariant buffers held heldNat statePtr mode lcodePtr
        rfl codesGet meaning mask rootFits noLink indexBound
        decodedExact
    exact ⟨result, after, slowFinal, run, afterEq, broke,
      finalPacket, finalBuffers, token⟩

#print axioms FastInputPacket.fast_body_no_pull_eob_of_decode_generic
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
set_option autoImplicit false
theorem literal_body_two_pull_generic_with_packet
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
    {baseOff rootWidth index : Nat}
    (lcodePtr : c.lcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : LenTableSafe codes baseOff rootWidth)
    (mask : c.lmask.toUInt64.toNat = 2 ^ rootWidth - 1)
    (indexEq : index = baseOff +
      ((((l.hold + (first.toUInt64 <<< l.bits.toUInt64)) +
        (second.toUInt64 <<< (l.bits + 8).toUInt64)) &&&
          c.lmask.toUInt64).toNat))
    (indexBound : index < codes.size)
    (codeFits : codes[index].bits.toNat ≤ slow.bits.toNat + 16)
    (codeWidth : codes[index].bits.toNat ≤ 15)
    (literal : codes[index].op = 0)
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
    {L D : List Nat} {dict history : List UInt8} {symbol : Nat}
    (decoded : decodeSym L
      (stream slow (first :: second :: third :: fourth :: fifth :: sixth :: rest)) =
      some (symbol,
        (stream slow (first :: second :: third :: fourth :: fifth :: sixth :: rest)).drop
          codes[index].bits.toNat))
    (smallSymbol : symbol < 256)
    (value : codes[index].val.toNat = symbol) :
    ∃ slowPrefix slowFinal result after,
      C.run (Zlib.Inffast.inflate_fast_body c l) h =
        .ok (result, after) ∧
      result.out = .ref dest (j + 1) ∧
      after = Space.put h dest
        (output.set! j codes[index].val.toUInt8) ∧
      SliceEnv h after slowPrefix slowFinal
        (third :: fourth :: fifth :: sixth :: rest) ∧
      FastInputPacket after slowFinal
        (third :: fourth :: fifth :: sixth :: rest) result ∧
      DispatchBuffers after r slowFinal
        (third :: fourth :: fifth :: sixth :: rest) ∧
      ZlibF.Spec.Token.Step L D dict history
        (stream slow (first :: second :: third :: fourth :: fifth :: sixth :: rest))
        (stream slowFinal (third :: fourth :: fifth :: sixth :: rest))
        (history ++ [codes[index].val.toUInt8]) false := by
  obtain ⟨slow2, fast2, selected, rootSlice, prefixRun,
    selectedEq, selectedPacket, buffers2, _, source2,
    outFrame, holdFrame, putFrame, leftFrame,
    _, bitsFrame, _, _, rootSliceEq, rootBound⟩ :=
    packet.two_pull_root_prefix invariant buffers small
      lcodePtr codesGet safe mask
  have rootEq : index = baseOff + rootSlice := by
    rw [indexEq, ← holdFrame, ← rootSliceEq]
  have selectedHere : selected.here = .ref codeRef index := by
    rw [selectedEq, rootEq]
  have selectedOut : selected.out = .ref dest j :=
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
    rw [selectedOut]
    simpa only [outPtr] using guard
  have codeFits2 : codes[index].bits.toNat ≤ slow2.bits.toNat := by
    rw [bitsFrame]
    exact codeFits
  have decoded2 : decodeSym L
      (stream slow2 (third :: fourth :: fifth :: sixth :: rest)) =
      some (symbol,
        (stream slow2 (third :: fourth :: fifth :: sixth :: rest)).drop
          codes[index].bits.toNat) := by
    rw [source2]
    exact decoded
  have literalResult := literal_token_view_generic
    (L := L) (D := D) (dict := dict) (history := history)
    selectedPacket invariant buffers2 selectedHere codesGet
    indexBound codeFits2 codeWidth literal left2 avail2
    selectedOut put2 end2 outputGet outputWrite
    size2 current guard2 decoded2 smallSymbol value
  dsimp only at literalResult
  obtain ⟨dolenRun, slice, finalBuffers, token⟩ := literalResult
  have loopRun := dolen_loop_one dolenRun (by rfl)
  let prefixM : C.M Zlib.Inffast.L := do
    let one ← Zlib.Inffast.pull l
    let two ← Zlib.Inffast.pull one
    let here ← c.lcode.add
      (two.hold &&& c.lmask.toUInt64).toNat
    pure { two with here }
  have bodyPrefix : C.run (Zlib.Inffast.inflate_fast_body c l) h =
      C.run (prefixM >>= fun current =>
        cdoWhile (Zlib.Inffast.dolen c)
          (fun current => pure (current.againL, current)) current) h := by
    unfold Zlib.Inffast.inflate_fast_body
    have needsPull : l.bits < 15 := by
      rw [packet.bits]
      exact UInt32.lt_iff_toNat_lt.mpr small
    simp only [needsPull, ite_true]
    simp only [prefixM, C.run, payload_bind_assoc,
      payload_pure_bind]
  have bodyRun : C.run (Zlib.Inffast.inflate_fast_body c l) h =
      C.run (cdoWhile (Zlib.Inffast.dolen c)
        (fun current => pure (current.againL, current)) selected) h := by
    rw [bodyPrefix]
    change (prefixM >>= fun current =>
      cdoWhile (Zlib.Inffast.dolen c)
        (fun current => pure (current.againL, current)) current) h = _
    change prefixM h = .ok (selected, h) at prefixRun
    rw [bind_app, prefixRun]
    rfl
  have finalRun := bodyRun.trans loopRun
  have finalPacket : FastInputPacket
      (Space.put h dest (output.set! j codes[index].val.toUInt8))
      { slow2 with
        hold := slow2.hold >>> codes[index].bits.toUInt32.toUInt64,
        bits := slow2.bits - codes[index].bits.toUInt32 }
      (third :: fourth :: fifth :: sixth :: rest)
      { selected with
        againL := false, op := codes[index].op.toUInt32,
        hold := selected.hold >>> codes[index].bits.toUInt32.toUInt64,
        bits := selected.bits - codes[index].bits.toUInt32,
        out := .ref dest (j + 1) } := by
    refine ⟨slice.afterBits, ?_, ?_, ?_⟩
    · exact selectedPacket.cursor
    · exact congrArg (fun x : UInt64 =>
        x >>> codes[index].bits.toUInt32.toUInt64) selectedPacket.hold
    · exact congrArg (fun x : UInt32 =>
        x - codes[index].bits.toUInt32) selectedPacket.bits
  refine ⟨slow2, _, _, _, finalRun, ?_, ?_,
    slice, finalPacket, finalBuffers, ?_⟩
  · rfl
  · rfl
  · rw [source2] at token
    exact token

#print axioms literal_body_two_pull_generic_with_packet
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
open Zlib.Inftrees.Spec Zlib.Inftrees.Spec.DecodeSemantics
open Zlib.Inftrees.Spec.DecodeSoundness Zlib.Inftrees.Spec.DecodeTableInvariant
open Zlib.Inftrees.Spec.Subtable
set_option autoImplicit false
theorem literal_body_two_pull_of_decode_generic_with_packet
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
    {baseOff rootWidth index used : Nat} {lens : List Nat}
    (lcodePtr : c.lcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : LenTableSafe codes baseOff rootWidth)
    (meaning : Inv LENS codes baseOff rootWidth used lens)
    (mask : c.lmask.toUInt64.toNat = 2 ^ rootWidth - 1)
    (indexEq : index = baseOff +
      ((((l.hold + (first.toUInt64 <<< l.bits.toUInt64)) +
        (second.toUInt64 <<< (l.bits + 8).toUInt64)) &&&
          c.lmask.toUInt64).toNat))
    (noLink : IsLink LENS
      (codes.getD (baseOff +
        (((l.hold + (first.toUInt64 <<< l.bits.toUInt64)) +
          (second.toUInt64 <<< (l.bits + 8).toUInt64)).toNat %
            2 ^ rootWidth)) default) = false)
    (indexBound : index < codes.size)
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
    {D : List Nat} {dict history : List UInt8} {symbol : Nat}
    (decoded : decodeSym lens
      (stream slow (first :: second :: third :: fourth :: fifth :: sixth :: rest)) =
      some (symbol,
        (stream slow (first :: second :: third :: fourth :: fifth :: sixth :: rest)).drop
          codes[index].bits.toNat))
    (smallSymbol : symbol < 256)
 :
    ∃ slowPrefix slowFinal result after,
      C.run (Zlib.Inffast.inflate_fast_body c l) h =
        .ok (result, after) ∧
      result.out = .ref dest (j + 1) ∧
      after = Space.put h dest
        (output.set! j codes[index].val.toUInt8) ∧
      SliceEnv h after slowPrefix slowFinal
        (third :: fourth :: fifth :: sixth :: rest) ∧
      FastInputPacket after slowFinal
        (third :: fourth :: fifth :: sixth :: rest) result ∧
      DispatchBuffers after r slowFinal
        (third :: fourth :: fifth :: sixth :: rest) ∧
      ZlibF.Spec.Token.Step lens D dict history
        (stream slow (first :: second :: third :: fourth :: fifth :: sixth :: rest))
        (stream slowFinal (third :: fourth :: fifth :: sixth :: rest))
        (history ++ [codes[index].val.toUInt8]) false := by
  have valid : ValidSymbol LENS symbol := by
    simpa [ValidSymbol] using (show symbol ≤ 285 by omega)
  obtain ⟨_, fitsD, widthD, meaningD, _⟩ :=
    packet.two_pull_root_leaf_of_decode invariant buffers small
      lcodePtr codesGet safe meaning mask indexEq noLink decoded valid
  have entryEq : codes.getD index default = codes[index] := by
    simp [Array.getD_eq_getD_getElem?, indexBound]
  have codeFits : codes[index].bits.toNat ≤ slow.bits.toNat + 16 := by
    simpa only [entryEq] using fitsD
  have codeWidth : codes[index].bits.toNat ≤ 15 := by
    simpa only [entryEq] using widthD
  have meaningIndex : SymbolEntry LENS symbol codes[index] := by
    simpa only [entryEq] using meaningD
  obtain ⟨literal, value⟩ :=
    length_literal_entry_fields smallSymbol meaningIndex
  exact literal_body_two_pull_generic_with_packet packet invariant buffers small
    lcodePtr codesGet safe mask indexEq indexBound codeFits codeWidth
    literal left avail outPtr outputPtr endPtr outputGet
    outputWrite outputSize current guard decoded smallSymbol value

#print axioms literal_body_two_pull_of_decode_generic_with_packet
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
open Zlib.Inftrees.Spec Zlib.Inftrees.Spec.DecodeSemantics
open Zlib.Inftrees.Spec.DecodeSoundness Zlib.Inftrees.Spec.DecodeTableInvariant
open Zlib.Inftrees.Spec.Subtable
set_option autoImplicit false

/-- One actual two-pull literal token, direct or second-level table entry. -/
theorem FastInputPacket.fast_body_two_pull_literal_of_decode_generic
    {h : Heap} {slow : IL}
    {first second third fourth fifth sixth : UInt8} {tail : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow
      (first :: second :: third :: fourth :: fifth :: sixth :: tail) l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow
      (first :: second :: third :: fourth :: fifth :: sixth :: tail))
    (small : slow.bits.toNat < 15)
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff rootWidth used : Nat} {lens : List Nat}
    (lcodePtr : c.lcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : LenTableSafe codes baseOff rootWidth)
    (meaning : Inv LENS codes baseOff rootWidth used lens)
    (mask : c.lmask.toUInt64.toNat = 2 ^ rootWidth - 1)
    (left : slow.left ≠ 0) (avail : 258 ≤ slow.left.toNat)
    {dest : BRef} {output : Array UInt8} {oo j : Nat}
    (outPtr : l.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (endPtr : c.end_ = .ref dest (oo + slow.left.toNat - 257))
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (current : oo ≤ j)
    (guard : C.run (Ptr.lt l.out c.end_) h = .ok (true, h))
    {D : List Nat} {dict history : List UInt8}
    {symbol : Nat} {r1 : List Bool}
    (decoded : decodeSym lens
      (stream slow (first :: second :: third :: fourth :: fifth :: sixth :: tail)) =
      some (symbol, r1))
    (smallSymbol : symbol < 256) :
    ∃ (byte : UInt8) (result : Zlib.Inffast.L) (after : Heap)
      (slowFinal : IL),
      C.run (Zlib.Inffast.inflate_fast_body c l) h = .ok (result, after) ∧
      result.out = .ref dest (j + 1) ∧
      Space.get after dest = some (output.set! j byte) ∧
      FastInputPacket after slowFinal
        (third :: fourth :: fifth :: sixth :: tail) result ∧
      DispatchBuffers after r slowFinal
        (third :: fourth :: fifth :: sixth :: tail) ∧
      ZlibF.Spec.Token.Step lens D dict history
        (stream slow (first :: second :: third :: fourth :: fifth :: sixth :: tail))
        (stream slowFinal (third :: fourth :: fifth :: sixth :: tail))
        (history ++ [byte]) false := by
  let filledHold : UInt64 :=
    (l.hold + (first.toUInt64 <<< l.bits.toUInt64)) +
      (second.toUInt64 <<< (l.bits + 8).toUInt64)
  let rootSlice := (filledHold &&& c.lmask.toUInt64).toNat
  have maskIndex : rootSlice = filledHold.toNat % 2 ^ rootWidth :=
    Zlib.Inffast.Proofs.u64_and_mask mask
  have root : rootSlice < 2 ^ rootWidth := by
    rw [maskIndex]
    exact Nat.mod_lt _ (Nat.pow_pos (by omega))
  by_cases link : LenLink (codes.getD (baseOff + rootSlice) default)
  · have rootLink : ∀ k, k < 2 ^ rootWidth →
        (k = (((l.hold + (first.toUInt64 <<< l.bits.toUInt64)) +
          (second.toUInt64 <<< (l.bits + 8).toUInt64)) &&&
            c.lmask.toUInt64).toNat) →
        LenLink (codes.getD (baseOff + k) default) := by
      intro k _ eq
      simpa only [eq, rootSlice, filledHold] using link
    exact linked_literal_body_two_pull_of_decode_generic_with_out
      packet invariant buffers small lcodePtr codesGet safe meaning
      mask rootLink left avail outPtr outputPtr endPtr outputGet
      outputWrite outputSize current guard decoded smallSymbol
  · have noLink : IsLink LENS
        (codes.getD (baseOff + filledHold.toNat % 2 ^ rootWidth)
          default) = false := by
      cases hq : IsLink LENS (codes.getD (baseOff + rootSlice) default) with
      | false => simpa only [← maskIndex] using hq
      | true => exact False.elim (link ((len_table_link_query safe root).mpr hq))
    let index := baseOff + rootSlice
    have indexBound : index < codes.size := by
      have rootSize := safe.2.1
      omega
    have valid : ValidSymbol LENS symbol := by
      simpa [ValidSymbol] using (show symbol ≤ 285 by omega)
    obtain ⟨_, _, _, _, restEq⟩ :=
      packet.two_pull_root_leaf_of_decode invariant buffers small
        lcodePtr codesGet safe meaning mask rfl noLink decoded valid
    have entryEq : codes.getD index default = codes[index] := by
      simp [Array.getD_eq_getD_getElem?, indexBound]
    have decodedExact : decodeSym lens
        (stream slow (first :: second :: third :: fourth :: fifth :: sixth :: tail)) =
        some (symbol, (stream slow
          (first :: second :: third :: fourth :: fifth :: sixth :: tail)).drop
            codes[index].bits.toNat) := by
      rw [entryEq] at restEq
      rw [← restEq]
      exact decoded
    obtain ⟨slowPrefix, slowFinal, result, after, run, out,
      afterEq, _, finalPacket, finalBuffers, token⟩ :=
      literal_body_two_pull_of_decode_generic_with_packet
        packet invariant buffers small lcodePtr codesGet safe meaning
        mask rfl noLink indexBound left avail outPtr outputPtr endPtr
        outputGet outputWrite outputSize current guard decodedExact smallSymbol
    have get : Space.get after dest = some
        (output.set! j codes[index].val.toUInt8) := by
      rw [afterEq]
      exact byte_view_get_put outputGet outputWrite _
    exact ⟨codes[index].val.toUInt8, result, after, slowFinal,
      run, out, get, finalPacket, finalBuffers, token⟩

#print axioms FastInputPacket.fast_body_two_pull_literal_of_decode_generic
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
set_option autoImplicit false
theorem eob_body_two_pull_generic_with_packet
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
    {baseOff rootWidth index : Nat}
    (lcodePtr : c.lcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : LenTableSafe codes baseOff rootWidth)
    (mask : c.lmask.toUInt64.toNat = 2 ^ rootWidth - 1)
    (indexEq : index = baseOff +
      ((((l.hold + (first.toUInt64 <<< l.bits.toUInt64)) +
        (second.toUInt64 <<< (l.bits + 8).toUInt64)) &&&
          c.lmask.toUInt64).toNat))
    (indexBound : index < codes.size)
    (codeFits : codes[index].bits.toNat ≤ slow.bits.toNat + 16)
    (codeWidth : codes[index].bits.toNat ≤ 15)
    (nonzero : codes[index].op ≠ 0)
    (notBase : (codes[index].op.toUInt32 &&& 16 != 0) = false)
    (notLink : (codes[index].op.toUInt32 &&& 64 == 0) = false)
    (endCode : (codes[index].op.toUInt32 &&& 32 != 0) = true)
    {L D : List Nat} {dict history : List UInt8}
    (decoded : decodeSym L
      (stream slow (first :: second :: third :: fourth :: fifth :: sixth :: rest)) =
      some (256,
        (stream slow (first :: second :: third :: fourth :: fifth :: sixth :: rest)).drop
          codes[index].bits.toNat)) :
    ∃ slowPrefix slowFinal result after,
      C.run (Zlib.Inffast.inflate_fast_body c l) h =
        .ok (result, after) ∧
      after = setI h zs { s with mode := TYPE } ∧
      result.broke = true ∧ result.out = l.out ∧
      SliceEnv h after slowPrefix slowFinal
        (third :: fourth :: fifth :: sixth :: rest) ∧
      FastInputPacket after slowFinal
        (third :: fourth :: fifth :: sixth :: rest) result ∧
      DispatchBuffers after r slowFinal
        (third :: fourth :: fifth :: sixth :: rest) ∧
      ZlibF.Spec.Token.Step L D dict history
        (stream slow (first :: second :: third :: fourth :: fifth :: sixth :: rest))
        (stream slowFinal (third :: fourth :: fifth :: sixth :: rest))
        history true := by
  obtain ⟨slow2, fast2, selected, rootSlice, prefixRun,
    selectedEq, selectedPacket, buffers2, _, source2,
    outFrame, holdFrame, _, _, nextFrame, bitsFrame,
    _, _, rootSliceEq, _⟩ :=
    packet.two_pull_root_prefix invariant buffers small
      lcodePtr codesGet safe mask
  have rootEq : index = baseOff + rootSlice := by
    rw [indexEq, ← holdFrame, ← rootSliceEq]
  have selectedHere : selected.here = .ref codeRef index := by
    rw [selectedEq, rootEq]
  have codeFits2 : codes[index].bits.toNat ≤ slow2.bits.toNat := by
    rw [bitsFrame]
    exact codeFits
  obtain ⟨result, slowFinal, dolenRun, broke, noAgain,
    inputFrame, outputFrame, finalPacket, _, finalBuffers,
    _, sourceDrop⟩ :=
    selectedPacket.dolen_end_leaf_default_state
      invariant buffers2 statePtr mode selectedHere codesGet
      indexBound codeFits2 codeWidth nonzero notBase
      notLink endCode
  have cursorEq : slowFinal.next = slow2.next := by
    rw [← finalPacket.cursor, inputFrame]
    exact selectedPacket.cursor
  have countEq : slowFinal.have_ = slow2.have_ := by
    apply UInt32.toNat_inj.mp
    rw [finalPacket.source.have_eq, selectedPacket.source.have_eq]
  have slice : SliceEnv h (setI h zs { s with mode := TYPE })
      slow2 slowFinal (third :: fourth :: fifth :: sixth :: rest) :=
    ⟨selectedPacket.source, finalPacket.source,
      cursorEq, countEq⟩
  have loopRun := dolen_loop_one dolenRun noAgain
  have needsPull : l.bits < 15 := by
    rw [packet.bits]
    exact UInt32.lt_iff_toNat_lt.mpr small
  have bodyRun := body_from_two_pull_root needsPull prefixRun loopRun
  have decoded2 : decodeSym L
      (stream slow2 (third :: fourth :: fifth :: sixth :: rest)) =
      some (256,
        (stream slow2 (third :: fourth :: fifth :: sixth :: rest)).drop
          codes[index].bits.toNat) := by
    rw [source2]
    exact decoded
  have token : ZlibF.Spec.Token.Step L D dict history
      (stream slow (first :: second :: third :: fourth :: fifth :: sixth :: rest))
      (stream slowFinal (third :: fourth :: fifth :: sixth :: rest))
      history true := by
    rw [sourceDrop, source2]
    exact ZlibF.Spec.Token.Step.eob decoded
  exact ⟨slow2, slowFinal, result,
    setI h zs { s with mode := TYPE }, bodyRun, rfl,
    broke, outputFrame.trans outFrame, slice, finalPacket,
    finalBuffers, token⟩

#print axioms eob_body_two_pull_generic_with_packet
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
open Zlib.Inftrees.Spec Zlib.Inftrees.Spec.DecodeSemantics
open Zlib.Inftrees.Spec.DecodeSoundness Zlib.Inftrees.Spec.DecodeTableInvariant
open Zlib.Inftrees.Spec.Subtable
set_option autoImplicit false
theorem eob_body_two_pull_of_decode_generic_with_packet
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
    {baseOff rootWidth index used : Nat} {lens : List Nat}
    (lcodePtr : c.lcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : LenTableSafe codes baseOff rootWidth)
    (meaning : Inv LENS codes baseOff rootWidth used lens)
    (mask : c.lmask.toUInt64.toNat = 2 ^ rootWidth - 1)
    (indexEq : index = baseOff +
      ((((l.hold + (first.toUInt64 <<< l.bits.toUInt64)) +
        (second.toUInt64 <<< (l.bits + 8).toUInt64)) &&&
          c.lmask.toUInt64).toNat))
    (noLinkQuery : IsLink LENS
      (codes.getD (baseOff +
        (((l.hold + (first.toUInt64 <<< l.bits.toUInt64)) +
          (second.toUInt64 <<< (l.bits + 8).toUInt64)).toNat %
            2 ^ rootWidth)) default) = false)
    (indexBound : index < codes.size)
    {D : List Nat} {dict history : List UInt8}
    (decoded : decodeSym lens
      (stream slow (first :: second :: third :: fourth :: fifth :: sixth :: rest)) =
      some (256,
        (stream slow (first :: second :: third :: fourth :: fifth :: sixth :: rest)).drop
          codes[index].bits.toNat)) :
    ∃ slowPrefix slowFinal result after,
      C.run (Zlib.Inffast.inflate_fast_body c l) h =
        .ok (result, after) ∧
      after = setI h zs { s with mode := TYPE } ∧
      result.broke = true ∧ result.out = l.out ∧
      SliceEnv h after slowPrefix slowFinal
        (third :: fourth :: fifth :: sixth :: rest) ∧
      FastInputPacket after slowFinal
        (third :: fourth :: fifth :: sixth :: rest) result ∧
      DispatchBuffers after r slowFinal
        (third :: fourth :: fifth :: sixth :: rest) ∧
      ZlibF.Spec.Token.Step lens D dict history
        (stream slow (first :: second :: third :: fourth :: fifth :: sixth :: rest))
        (stream slowFinal (third :: fourth :: fifth :: sixth :: rest))
        history true := by
  have valid : ValidSymbol LENS 256 := by
    simp [ValidSymbol]
  obtain ⟨_, fitsD, widthD, meaningD, _⟩ :=
    packet.two_pull_root_leaf_of_decode invariant buffers small
      lcodePtr codesGet safe meaning mask indexEq noLinkQuery decoded valid
  have entryEq : codes.getD index default = codes[index] := by
    simp [Array.getD_eq_getD_getElem?, indexBound]
  have codeFits : codes[index].bits.toNat ≤ slow.bits.toNat + 16 := by
    simpa only [entryEq] using fitsD
  have codeWidth : codes[index].bits.toNat ≤ 15 := by
    simpa only [entryEq] using widthD
  have meaningIndex : SymbolEntry LENS 256 codes[index] := by
    simpa only [entryEq] using meaningD
  obtain ⟨nonzero, notBase, notLink, endCode⟩ :=
    length_eob_entry_fields meaningIndex
  exact eob_body_two_pull_generic_with_packet packet invariant buffers small
    statePtr mode lcodePtr codesGet safe mask indexEq indexBound
    codeFits codeWidth nonzero notBase notLink endCode decoded

#print axioms eob_body_two_pull_of_decode_generic_with_packet
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
open Zlib.Inftrees.Spec Zlib.Inftrees.Spec.DecodeSemantics
open Zlib.Inftrees.Spec.DecodeSoundness Zlib.Inftrees.Spec.DecodeTableInvariant
open Zlib.Inftrees.Spec.Subtable
set_option autoImplicit false

/-- One actual two-pull end-of-block token, direct or second-level table entry. -/
theorem FastInputPacket.fast_body_two_pull_eob_of_decode_generic
    {h : Heap} {slow : IL}
    {first second third fourth fifth sixth : UInt8} {tail : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow
      (first :: second :: third :: fourth :: fifth :: sixth :: tail) l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow
      (first :: second :: third :: fourth :: fifth :: sixth :: tail))
    (small : slow.bits.toNat < 15)
    (statePtr : c.state = some (.tab zs))
    (mode : DataTableMode s.mode)
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff rootWidth used : Nat} {lens : List Nat}
    (lcodePtr : c.lcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : LenTableSafe codes baseOff rootWidth)
    (meaning : Inv LENS codes baseOff rootWidth used lens)
    (mask : c.lmask.toUInt64.toNat = 2 ^ rootWidth - 1)
    {D : List Nat} {dict history : List UInt8} {r1 : List Bool}
    (decoded : decodeSym lens
      (stream slow (first :: second :: third :: fourth :: fifth :: sixth :: tail)) =
      some (256, r1)) :
    ∃ (result : Zlib.Inffast.L) (after : Heap) (slowFinal : IL),
      C.run (Zlib.Inffast.inflate_fast_body c l) h = .ok (result, after) ∧
      after = setI h zs { s with mode := TYPE } ∧
      result.broke = true ∧
      FastInputPacket after slowFinal
        (third :: fourth :: fifth :: sixth :: tail) result ∧
      DispatchBuffers after r slowFinal
        (third :: fourth :: fifth :: sixth :: tail) ∧
      ZlibF.Spec.Token.Step lens D dict history
        (stream slow (first :: second :: third :: fourth :: fifth :: sixth :: tail))
        (stream slowFinal (third :: fourth :: fifth :: sixth :: tail))
        history true := by
  let filledHold : UInt64 :=
    (l.hold + (first.toUInt64 <<< l.bits.toUInt64)) +
      (second.toUInt64 <<< (l.bits + 8).toUInt64)
  let rootSlice := (filledHold &&& c.lmask.toUInt64).toNat
  have maskIndex : rootSlice = filledHold.toNat % 2 ^ rootWidth :=
    Zlib.Inffast.Proofs.u64_and_mask mask
  have root : rootSlice < 2 ^ rootWidth := by
    rw [maskIndex]
    exact Nat.mod_lt _ (Nat.pow_pos (by omega))
  by_cases link : LenLink (codes.getD (baseOff + rootSlice) default)
  · have rootLink : ∀ k, k < 2 ^ rootWidth →
        (k = (((l.hold + (first.toUInt64 <<< l.bits.toUInt64)) +
          (second.toUInt64 <<< (l.bits + 8).toUInt64)) &&&
            c.lmask.toUInt64).toNat) →
        LenLink (codes.getD (baseOff + k) default) := by
      intro k _ eq
      simpa only [eq, rootSlice, filledHold] using link
    exact linked_eob_body_two_pull_of_decode_generic
      packet invariant buffers small statePtr mode lcodePtr codesGet
      safe meaning mask rootLink decoded
  · have noLink : IsLink LENS
        (codes.getD (baseOff + filledHold.toNat % 2 ^ rootWidth)
          default) = false := by
      cases hq : IsLink LENS (codes.getD (baseOff + rootSlice) default) with
      | false => simpa only [← maskIndex] using hq
      | true => exact False.elim (link ((len_table_link_query safe root).mpr hq))
    let index := baseOff + rootSlice
    have indexBound : index < codes.size := by
      have rootSize := safe.2.1
      omega
    obtain ⟨_, _, _, _, restEq⟩ :=
      packet.two_pull_root_leaf_of_decode invariant buffers small
        lcodePtr codesGet safe meaning mask rfl noLink decoded
        (by simp [ValidSymbol])
    have entryEq : codes.getD index default = codes[index] := by
      simp [Array.getD_eq_getD_getElem?, indexBound]
    have decodedExact : decodeSym lens
        (stream slow (first :: second :: third :: fourth :: fifth :: sixth :: tail)) =
        some (256, (stream slow
          (first :: second :: third :: fourth :: fifth :: sixth :: tail)).drop
            codes[index].bits.toNat) := by
      rw [entryEq] at restEq
      rw [← restEq]
      exact decoded
    obtain ⟨slowPrefix, slowFinal, result, after, run, afterEq,
      broke, _, _, finalPacket, finalBuffers, token⟩ :=
      eob_body_two_pull_of_decode_generic_with_packet
        packet invariant buffers small statePtr mode lcodePtr codesGet
        safe meaning mask rfl noLink indexBound decodedExact
    exact ⟨result, after, slowFinal, run, afterEq, broke,
      finalPacket, finalBuffers, token⟩

#print axioms FastInputPacket.fast_body_two_pull_eob_of_decode_generic
end Zlib.Inflate.Proofs
