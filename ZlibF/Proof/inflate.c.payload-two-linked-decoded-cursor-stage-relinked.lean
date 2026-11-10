import ZlibF.Proof.«inflate.c.payload-linked-decoded-cursor-stage-relinked»
namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
open Zlib.Inftrees.Spec Zlib.Inftrees.Spec.DecodeSemantics
open Zlib.Inftrees.Spec.DecodeSoundness Zlib.Inftrees.Spec.DecodeTableInvariant
open Zlib.Inftrees.Spec.Subtable
set_option autoImplicit false
set_option maxRecDepth 4096
theorem FastInputPacket.fast_body_two_pull_linked_match_of_decode_cursor
    {h : Heap} {slow : IL}
    {first second third fourth fifth sixth : UInt8} {tail : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow
      (first :: second :: third :: fourth :: fifth :: sixth :: tail) l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow
      (first :: second :: third :: fourth :: fifth :: sixth :: tail))
    {L : List Nat}
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff rootWidth rootSlice : Nat}
    {filledHold : UInt64}
    (holdEq : filledHold = (l.hold + (first.toUInt64 <<< l.bits.toUInt64)) +
      (second.toUInt64 <<< (l.bits + 8).toUInt64))
    (rootSliceEq : rootSlice = (filledHold &&& c.lmask.toUInt64).toNat)
    (lcodePtr : c.lcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : LenTableSafe codes baseOff rootWidth)
    {tableUsed : Nat}
    (meaning : Inv LENS codes baseOff rootWidth tableUsed L)
    (mask : c.lmask.toUInt64.toNat = 2 ^ rootWidth - 1)
    (link : LenLink (codes.getD (baseOff + rootSlice) default))
    (small : slow.bits.toNat < 15)
    {distRef : CodeRef} {distCodes : Array Code}
    {distOff distWidth distUsed : Nat} {D : List Nat}
    (dcodePtr : c.dcode = .ref distRef distOff)
    (distGet : Space.get h distRef = some distCodes)
    (distSafe : DistTableSafe distCodes distOff distWidth)
    (distMeaning : DecodeTableInvariant.Inv DISTS distCodes distOff distWidth distUsed D)
    (distFlags : FastTableFlags.QueryCompatible DISTS distCodes distOff distWidth)
    (distMask : c.dmask.toUInt64.toNat = 2 ^ distWidth - 1)
    (left : slow.left ≠ 0) (avail : 258 ≤ slow.left.toNat)
    {dest : BRef} {output : Array UInt8} {oo bg j : Nat}
    (outPtr : l.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (begPtr : c.beg = .ref dest bg)
    (endPtr : c.end_ = .ref dest (oo + slow.left.toNat - 257))
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (current : oo ≤ j) (beginLe : bg ≤ j) (span : j - bg < 2 ^ 32)
    (guard : C.run (Ptr.lt l.out c.end_) h = .ok (true, h))
    (whaveBound : c.whave.toNat ≤ c.wsize.toNat)
    (wnextBound : c.wnext.toNat ≤ c.wsize.toNat)
    (wsizeBound : c.wsize.toNat ≤ 32768)
    {saved : Array UInt8} {woff : Nat}
    (windowView : 0 < c.whave.toNat → ∃ window,
      window ≠ dest ∧ c.window = .ref window woff ∧
      Space.get h window = some saved ∧ woff + c.wsize.toNat ≤ saved.size)
    {dict history : List UInt8} {input r1 r2 r3 rest : List Bool}
    {symbol distanceSymbol lengthExtra distanceExtra : Nat}
    (lengthCode : decodeSym L input = some (symbol, r1))
    (lengthMin : 257 ≤ symbol) (lengthMax : symbol ≤ 285)
    (lengthSource : input = stream slow
      (first :: second :: third :: fourth :: fifth :: sixth :: tail))
    (lengthBits : readBits (lengthExtras.getD (symbol - 257) 0) r1 =
      some (lengthExtra, r2))
    (distanceCode : decodeSym D r2 = some (distanceSymbol, r3))
    (distanceSymbolBound : distanceSymbol ≤ 29)
    (distanceBits : readBits (distExtras.getD distanceSymbol 0) r3 =
      some (distanceExtra, rest))
    (dictionary : MatchHistory.saved saved c.wsize.toNat c.wnext.toNat
      c.whave.toNat woff = dict)
    (dictCount : dict.length = c.whave.toNat)
    (written : ZlibF.Math.LZ77Copy.writtenBytes output j (j - bg) = history)
    (historyCount : history.length = j - bg)
    (backBound : distBases.getD distanceSymbol 0 + distanceExtra ≤
      (dict ++ history).length) :
    ∃ used result after array slowFinal,
      used ≤ 7 ∧ used ≤ (first :: second :: third :: fourth :: fifth :: sixth :: tail).length ∧
      C.run (Zlib.Inffast.inflate_fast_body c l) h = .ok (result, after) ∧
      result.againL = false ∧ result.againD = false ∧
      result.out = .ref dest
        (j + (lengthBases.getD (symbol - 257) 0 + lengthExtra)) ∧
      FastInputPacket after slowFinal
        ((first :: second :: third :: fourth :: fifth :: sixth :: tail).drop used) result ∧
      stream slowFinal
        ((first :: second :: third :: fourth :: fifth :: sixth :: tail).drop used) = rest ∧
      Space.get after dest = some array ∧ array.size = output.size ∧
      Space.ro after dest = false ∧
      ZlibF.Math.LZ77Copy.writtenBytes array
        (j + (lengthBases.getD (symbol - 257) 0 + lengthExtra))
        ((j - bg) + (lengthBases.getD (symbol - 257) 0 + lengthExtra)) =
        copyBack dict (distBases.getD distanceSymbol 0 + distanceExtra)
          (lengthBases.getD (symbol - 257) 0 + lengthExtra) history ∧
      Token.Step L D dict history input rest
        (ZlibF.Math.LZ77Copy.writtenBytes array
          (j + (lengthBases.getD (symbol - 257) 0 + lengthExtra))
          ((j - bg) + (lengthBases.getD (symbol - 257) 0 + lengthExtra))) false ∧
      result.in_ = inputAdvance l.in_ used := by
  obtain ⟨slow2, fast2, selected, actualSlice, _, selectedEq,
    selectedPacket, buffers2, _, sourceEq, _, holdFrame, _, _, _, _,
    held2, _, actualSliceEq, actualRootBound⟩ :=
    packet.two_pull_root_prefix invariant buffers small
      lcodePtr codesGet safe mask
  let raw4 := third :: fourth :: fifth :: sixth :: tail
  have fastHold : fast2.hold = filledHold := holdFrame.trans holdEq.symm
  have selectedHold : selected.hold = filledHold := by
    rw [selectedEq]
    exact fastHold
  have sliceEq : actualSlice = rootSlice := by
    rw [actualSliceEq, fastHold, ← rootSliceEq]
  have selectedHere : selected.here = .ref codeRef (baseOff + rootSlice) := by
    rw [selectedEq, sliceEq]
  have root : rootSlice < 2 ^ rootWidth := by
    rw [← sliceEq]
    exact actualRootBound
  have queryLink := (payload_len_table_link_query safe root).mp link
  have rootIndex : rootSlice = selected.hold.toNat % 2 ^ rootWidth := by
    rw [rootSliceEq, selectedHold,
      Zlib.Inffast.Proofs.u64_and_mask mask]
  have decoded2 : decodeSym L (stream slow2 raw4) = some (symbol, r1) := by
    rw [sourceEq, ← lengthSource]
    exact lengthCode
  obtain ⟨_, leafSlice, _, _, _, _, _, _, leafSliceEq,
    selectedMeaning, selectedRest⟩ :=
    selectedPacket.payload_length_selected_link_match_of_decode
      invariant buffers2 selectedHere lcodePtr codesGet safe meaning
      root rootIndex link queryLink (by omega) decoded2 lengthMax
  have targetMeaning :
      let rootEntry := codes.getD (baseOff + rootSlice) default
      let slice := (filledHold >>> rootEntry.bits.toUInt32.toUInt64).toNat %
        2 ^ rootEntry.op.toNat
      SymbolEntry LENS symbol
        (codes.getD (baseOff + rootEntry.val.toNat + slice) default) := by
    rw [leafSliceEq] at selectedMeaning
    simpa only [selectedHold] using selectedMeaning
  have codeRest :
      let rootEntry := codes.getD (baseOff + rootSlice) default
      let slice := (filledHold >>> rootEntry.bits.toUInt32.toUInt64).toNat %
        2 ^ rootEntry.op.toNat
      r1 = (stream slow
        (first :: second :: third :: fourth :: fifth :: sixth :: tail)).drop
        (rootEntry.bits.toNat +
          (codes.getD (baseOff + rootEntry.val.toNat + slice) default).bits.toNat) := by
    rw [leafSliceEq] at selectedRest
    rw [← sourceEq]
    simpa only [selectedHold] using selectedRest
  exact packet.fast_body_two_pull_linked_match_token_cursor
    invariant buffers holdEq rootSliceEq lcodePtr codesGet safe mask
    link small dcodePtr distGet distSafe distMeaning distFlags distMask
    left avail outPtr outputPtr begPtr endPtr outputGet outputWrite
    outputSize current beginLe span guard whaveBound wnextBound wsizeBound
    windowView lengthCode lengthMin lengthMax lengthSource
    targetMeaning codeRest lengthBits distanceCode distanceSymbolBound
    distanceBits dictionary dictCount written historyCount backBound

#print axioms FastInputPacket.fast_body_two_pull_linked_match_of_decode_cursor
end Zlib.Inflate.Proofs
