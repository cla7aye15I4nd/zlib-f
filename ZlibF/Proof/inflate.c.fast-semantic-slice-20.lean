import ZlibF.Proof.«inflate.c.fast-semantic-slice-19»
set_option autoImplicit false

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
open Zlib.Inftrees.Spec Zlib.Inftrees.Spec.DecodeSemantics
open Zlib.Inftrees.Spec.DecodeSoundness Zlib.Inftrees.Spec.DecodeTableInvariant
open Zlib.Inftrees.Spec.Subtable
set_option autoImplicit false
set_option maxRecDepth 4096

/-- The actual held root query accepts the independently decoded length
symbol whenever it is a direct table leaf. This obtains the branch meaning
from the installed table invariant, not from a caller supplied leaf fact. -/
theorem FastInputPacket.length_root_match_of_decode
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L}
    (packet : FastInputPacket h slow bs l)
    {codes : Array Code} {baseOff rootWidth used : Nat}
    {lens : List Nat}
    (meaning : Inv LENS codes baseOff rootWidth used lens)
    (rootFits : rootWidth ≤ slow.bits.toNat)
    (held : 15 ≤ slow.bits.toNat)
    (noLink : IsLink LENS
      (codes.getD (baseOff + l.hold.toNat % 2 ^ rootWidth) default) = false)
    {symbol : Nat} {rest : List Bool}
    (decoded : decodeSym lens (stream slow bs) = some (symbol, rest))
    (lengthMin : 257 ≤ symbol) (lengthMax : symbol ≤ 285) :
    let entry := codes.getD (baseOff + l.hold.toNat % 2 ^ rootWidth) default
    LeafAccepted LENS entry ∧ SymbolEntry LENS symbol entry ∧
      entry.op &&& 16 ≠ 0 ∧
      entry.bits.toNat = lens.getD symbol 0 ∧
      rest = (stream slow bs).drop entry.bits.toNat := by
  let slice := l.hold.toNat % 2 ^ rootWidth
  let entry := codes.getD (baseOff + slice) default
  let inp := stream slow bs
  have valid : ValidSymbol LENS symbol := by
    simpa [ValidSymbol] using lengthMax
  have long : 15 ≤ inp.length := by
    simp only [inp, stream, List.length_append, natBits_length]
    omega
  have rootBound : baseOff + slice < codes.size := by
    have rootSize := meaning.rootTable.2.2.1
    have modBound : slice < 2 ^ rootWidth :=
      Nat.mod_lt _ (Nat.pow_pos (by omega))
    omega
  have rootRead : readBits rootWidth inp =
      some (slice, inp.drop rootWidth) := by
    have read := readBits_held_stream slow bs rootWidth rootFits
    simpa only [inp, slice, ← packet.hold] using read
  have cell : codes[baseOff + slice]? = some entry := by
    simp [entry, Array.getD_eq_getD_getElem?, rootBound]
  have noLinkCode :
      (entry.op != 0 && (entry.op &&& 0xf0) == 0) = false := by
    simpa [IsLink, entry, slice] using noLink
  have queryRoot : tableRead LENS codes baseOff rootWidth inp =
      some (entry, entry.bits.toNat) := by
    simp only [tableRead, rootRead, bind, Option.bind, cell]
    simp only [noLinkCode]
    simp
  obtain ⟨other, count, query, classification⟩ :=
    meaning.classify inp long
  have acceptedOther : LeafAccepted LENS other :=
    classification.mpr ⟨symbol, rest, decoded, valid⟩
  have same : (other, count) = (entry, entry.bits.toNat) :=
    Option.some.inj (query.symm.trans queryRoot)
  have accepted : LeafAccepted LENS entry := by
    simpa only [(Prod.mk.inj same).1] using acceptedOther
  obtain ⟨found, _, foundMeaning, width, foundDecode⟩ :=
    packet.length_root_leaf_meaning meaning rootFits held rootBound
      noLink accepted
  have decodedEq := Option.some.inj (foundDecode.symm.trans decoded)
  have symbolEq : found = symbol := congrArg Prod.fst decodedEq
  have restEq : rest = inp.drop entry.bits.toNat :=
    (congrArg Prod.snd decodedEq).symm
  subst found
  have base := (length_base_symbol_fields_view lengthMin lengthMax
    foundMeaning).1
  exact ⟨accepted, foundMeaning, base, width, restEq⟩

#print axioms FastInputPacket.length_root_match_of_decode
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
open Zlib.Inftrees.Spec Zlib.Inftrees.Spec.DecodeSemantics
open Zlib.Inftrees.Spec.DecodeSoundness Zlib.Inftrees.Spec.DecodeTableInvariant
open Zlib.Inftrees.Spec.Subtable
set_option autoImplicit false
set_option maxRecDepth 4096
theorem FastInputPacket.length_root_body_no_pull_match_of_decode
    {h : Heap} {slow : IL}
    {first second third fourth fifth : UInt8} {tail : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow
      (first :: second :: third :: fourth :: fifth :: tail) l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow
      (first :: second :: third :: fourth :: fifth :: tail))
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff rootWidth tableUsed : Nat} {lens : List Nat}
    (lcodePtr : c.lcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : LenTableSafe codes baseOff rootWidth)
    (meaning : Inv LENS codes baseOff rootWidth tableUsed lens)
    (mask : c.lmask.toUInt64.toNat = 2 ^ rootWidth - 1)
    (rootFits : rootWidth ≤ slow.bits.toNat)
    (held : 15 ≤ slow.bits.toNat)
    (noLink : IsLink LENS
      (codes.getD (baseOff + l.hold.toNat % 2 ^ rootWidth) default) = false)
    {distRef : CodeRef} {distCodes : Array Code}
    {distOff distWidth distUsed : Nat} {D : List Nat}
    (dcodePtr : c.dcode = .ref distRef distOff)
    (distGet : Space.get h distRef = some distCodes)
    (distSafe : DistTableSafe distCodes distOff distWidth)
    (distMeaning : Inv DISTS distCodes distOff distWidth distUsed D)
    (distFlags : FastTableFlags.QueryCompatible DISTS distCodes distOff distWidth)
    (distMask : c.dmask.toUInt64.toNat = 2 ^ distWidth - 1)
    (bitsBound : slow.bits.toNat ≤ 30)
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
    (lengthCode : decodeSym lens input = some (symbol, r1))
    (lengthMin : 257 ≤ symbol) (lengthMax : symbol ≤ 285)
    (lengthSource : input = stream slow
      (first :: second :: third :: fourth :: fifth :: tail))
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
    let rootSlice := (l.hold &&& c.lmask.toUInt64).toNat
    C.run (c.lcode.add rootSlice) h =
      .ok (.ref codeRef (baseOff + rootSlice), h) ∧
    ∃ used result after array slowFinal,
      used ≤ 5 ∧ used ≤ (first :: second :: third :: fourth :: fifth :: tail).length ∧
      C.run (Zlib.Inffast.inflate_fast_body c l) h = .ok (result, after) ∧
      result.againL = false ∧ result.againD = false ∧ result.broke = l.broke ∧
      FastInputPacket after slowFinal
        ((first :: second :: third :: fourth :: fifth :: tail).drop used) result ∧
      stream slowFinal
        ((first :: second :: third :: fourth :: fifth :: tail).drop used) = rest ∧
      Space.get after dest = some array ∧ array.size = output.size ∧
      Space.ro after dest = false ∧
      Token.Step lens D dict history input rest
        (ZlibF.Math.LZ77Copy.writtenBytes array
          (j + (lengthBases.getD (symbol - 257) 0 + lengthExtra))
          ((j - bg) + (lengthBases.getD (symbol - 257) 0 + lengthExtra))) false := by
  have actualDecoded : decodeSym lens
      (stream slow (first :: second :: third :: fourth :: fifth :: tail)) =
      some (symbol, r1) := by
    rw [← lengthSource]
    exact lengthCode
  obtain ⟨accepted, _, base, _, _⟩ :=
    packet.length_root_match_of_decode meaning rootFits held noLink
      actualDecoded lengthMin lengthMax
  exact packet.length_root_base_body_no_pull_token_view
    invariant buffers lcodePtr codesGet safe meaning mask rootFits held
    noLink accepted base dcodePtr distGet distSafe distMeaning distFlags
    distMask bitsBound left avail outPtr outputPtr begPtr endPtr outputGet
    outputWrite outputSize current beginLe span guard whaveBound wnextBound
    wsizeBound windowView lengthCode lengthSource lengthBits distanceCode
    distanceSymbolBound distanceBits dictionary dictCount written historyCount
    backBound

#print axioms FastInputPacket.length_root_body_no_pull_match_of_decode
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
open Zlib.Inftrees.Spec Zlib.Inftrees.Spec.DecodeSemantics
open Zlib.Inftrees.Spec.DecodeSoundness Zlib.Inftrees.Spec.DecodeTableInvariant
open Zlib.Inftrees.Spec.Subtable
set_option autoImplicit false
set_option maxRecDepth 4096
theorem FastInputPacket.fast_body_two_pull_root_match_of_decode
    {h : Heap} {slow : IL}
    {first second third fourth fifth sixth : UInt8} {tail : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow
      (first :: second :: third :: fourth :: fifth :: sixth :: tail) l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow
      (first :: second :: third :: fourth :: fifth :: sixth :: tail))
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff rootWidth tableUsed : Nat} {lens : List Nat}
    (lcodePtr : c.lcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : LenTableSafe codes baseOff rootWidth)
    (meaning : Inv LENS codes baseOff rootWidth tableUsed lens)
    (mask : c.lmask.toUInt64.toNat = 2 ^ rootWidth - 1)
    (small : slow.bits.toNat < 15)
    {filledHold : UInt64}
    (holdEq : filledHold = (l.hold + (first.toUInt64 <<< l.bits.toUInt64)) +
      (second.toUInt64 <<< (l.bits + 8).toUInt64))
    (noLink : IsLink LENS
      (codes.getD (baseOff + filledHold.toNat % 2 ^ rootWidth) default) = false)
    {distRef : CodeRef} {distCodes : Array Code}
    {distOff distWidth distUsed : Nat} {D : List Nat}
    (dcodePtr : c.dcode = .ref distRef distOff)
    (distGet : Space.get h distRef = some distCodes)
    (distSafe : DistTableSafe distCodes distOff distWidth)
    (distMeaning : Inv DISTS distCodes distOff distWidth distUsed D)
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
    (lengthCode : decodeSym lens input = some (symbol, r1))
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
      FastInputPacket after slowFinal
        ((first :: second :: third :: fourth :: fifth :: sixth :: tail).drop used) result ∧
      stream slowFinal
        ((first :: second :: third :: fourth :: fifth :: sixth :: tail).drop used) = rest ∧
      Space.get after dest = some array ∧ array.size = output.size ∧
      Space.ro after dest = false ∧
      Token.Step lens D dict history input rest
        (ZlibF.Math.LZ77Copy.writtenBytes array
          (j + (lengthBases.getD (symbol - 257) 0 + lengthExtra))
          ((j - bg) + (lengthBases.getD (symbol - 257) 0 + lengthExtra))) false := by
  obtain ⟨slow2, fast2, selected, rootSlice, _, selectedEq,
    selectedPacket, _, _, sourceEq, _, holdFrame, _, _, _, _,
    held2, _, _, _⟩ :=
    packet.two_pull_root_prefix invariant buffers small
      lcodePtr codesGet safe mask
  let raw4 := third :: fourth :: fifth :: sixth :: tail
  have fastPacket : FastInputPacket h slow2 raw4 fast2 := by
    exact ⟨selectedPacket.source,
      by simpa only [selectedEq] using selectedPacket.cursor,
      by simpa only [selectedEq] using selectedPacket.hold,
      by simpa only [selectedEq] using selectedPacket.bits⟩
  have fastHold : fast2.hold = filledHold := holdFrame.trans holdEq.symm
  have rootFits2 : rootWidth ≤ slow2.bits.toNat := by
    have width := safe.1
    omega
  have noLink2 : IsLink LENS
      (codes.getD (baseOff + fast2.hold.toNat % 2 ^ rootWidth) default) = false := by
    rwa [fastHold]
  have decoded2 : decodeSym lens (stream slow2 raw4) =
      some (symbol, r1) := by
    rw [sourceEq, ← lengthSource]
    exact lengthCode
  obtain ⟨accepted2, _, base2, _, _⟩ :=
    fastPacket.length_root_match_of_decode meaning rootFits2
      (by omega) noLink2 decoded2 lengthMin lengthMax
  have accepted : LeafAccepted LENS
      (codes.getD (baseOff + filledHold.toNat % 2 ^ rootWidth) default) := by
    rwa [fastHold] at accepted2
  have base : (codes.getD
      (baseOff + filledHold.toNat % 2 ^ rootWidth) default).op &&& 16 ≠ 0 := by
    rwa [fastHold] at base2
  exact packet.fast_body_two_pull_root_match_token
    invariant buffers lcodePtr codesGet safe meaning mask small
    holdEq noLink accepted base dcodePtr distGet distSafe distMeaning
    distFlags distMask left avail outPtr outputPtr begPtr endPtr
    outputGet outputWrite outputSize current beginLe span guard
    whaveBound wnextBound wsizeBound windowView lengthCode lengthSource
    lengthBits distanceCode distanceSymbolBound distanceBits
    dictionary dictCount written historyCount backBound

#print axioms FastInputPacket.fast_body_two_pull_root_match_of_decode
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
open Zlib.Inftrees.Spec.DecodeSemantics
open Zlib.Inftrees.Spec.DecodeSoundness
open Zlib.Inftrees.Spec.DecodeShort
open Zlib.Inftrees.Spec.DecodeTableInvariant
open Zlib.Inftrees.Spec.Subtable

/-- The actual two-level length lookup's physical link index and the
constructor-backed independent Huffman decode select the same leaf. -/
theorem FastInputPacket.length_selected_link_match_of_decode
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow bs l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff rootWidth rootSlice used : Nat} {lens : List Nat}
    (herePtr : l.here = .ref codeRef (baseOff + rootSlice))
    (lcodePtr : c.lcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : LenTableSafe codes baseOff rootWidth)
    (meaning : Inv LENS codes baseOff rootWidth used lens)
    (root : rootSlice < 2 ^ rootWidth)
    (rootIndex : rootSlice = l.hold.toNat % 2 ^ rootWidth)
    (link : LenLink (codes.getD (baseOff + rootSlice) default))
    (queryLink : IsLink LENS
      (codes.getD (baseOff + rootSlice) default) = true)
    (held : 15 ≤ slow.bits.toNat)
    {symbol : Nat} {rest : List Bool}
    (decoded : decodeSym lens (stream slow bs) = some (symbol, rest))
    (lengthMax : symbol ≤ 285) :
    let rootEntry := codes.getD (baseOff + rootSlice) default
    ∃ linked slice slowNext,
      C.run (Zlib.Inffast.dolen c l) h = .ok (linked, h) ∧
      linked.againL = true ∧
      linked.here = .ref codeRef
        (baseOff + rootEntry.val.toNat + slice) ∧
      FastInputPacket h slowNext bs linked ∧
      stream slowNext bs = (stream slow bs).drop rootEntry.bits.toNat ∧
      slice = (l.hold >>> rootEntry.bits.toUInt32.toUInt64).toNat %
        2 ^ rootEntry.op.toNat ∧
      SymbolEntry LENS symbol
        (codes.getD (baseOff + rootEntry.val.toNat + slice) default) ∧
      rest = (stream slow bs).drop
        (rootEntry.bits.toNat +
          (codes.getD (baseOff + rootEntry.val.toNat + slice) default).bits.toNat) := by
  let rootEntry := codes.getD (baseOff + rootSlice) default
  obtain ⟨linked, slice, slowNext, firstRun, againL,
    sliceBound, sliceEq, linkedHere, targetLeaf, _,
    linkedPacket, _, _, sourceDrop⟩ :=
    packet.dolen_root_link_default_state_with_slice
      invariant buffers herePtr lcodePtr codesGet safe
      root link held
  let target := codes.getD
    (baseOff + rootEntry.val.toNat + slice) default
  have rootRead : readBits rootWidth (stream slow bs) =
      some (rootSlice, (stream slow bs).drop rootWidth) := by
    have rootFits : rootWidth ≤ slow.bits.toNat := by
      have width := meaning.rootTable.2.1
      omega
    have read := readBits_held_stream slow bs rootWidth rootFits
    simpa only [← packet.hold, ← rootIndex] using read
  have rootBound : baseOff + rootSlice < codes.size := by
    have rootSize := safe.2.1
    omega
  have rootCell : codes[baseOff + rootSlice]? = some rootEntry := by
    simp [rootEntry, Array.getD_eq_getD_getElem?, rootBound]
  have selected := safe.2.2 rootSlice root
  have rootEq : rootEntry = codes[baseOff + rootSlice] := by
    simp [rootEntry, Array.getD_eq_getD_getElem?, rootBound]
  have rootGet : codes.getD (baseOff + rootSlice) default =
      codes[baseOff + rootSlice] := by
    simp [Array.getD_eq_getD_getElem?, rootBound]
  have rootLink : LenLink codes[baseOff + rootSlice] := by
    simpa only [rootGet] using link
  rw [rootGet, ite_eq_left rootLink] at selected
  obtain ⟨rootWidthBound, _, opWidth, _, _⟩ := selected
  obtain ⟨rootBits, subSafe⟩ :=
    meaning.subtables rootSlice rootEntry root rootCell queryLink
  have subBits : rootEntry.bits.toNat + rootEntry.op.toNat ≤ 15 :=
    subSafe.2.2.1
  have linkFits : rootEntry.bits.toNat + rootEntry.op.toNat ≤
      slow.bits.toNat := by
    omega
  have linkWidth : rootEntry.bits.toNat ≤ 15 := by
    omega
  have secondRead := packet.length_link_second_read
    rootEntry linkWidth linkFits sliceEq
  have targetBound : baseOff + rootEntry.val.toNat + slice <
      codes.size := (len_table_link_target safe root link sliceBound).1
  have targetCell : codes[baseOff + rootEntry.val.toNat + slice]? =
      some target := by
    simp [target, Array.getD_eq_getD_getElem?, targetBound]
  have queryLinkCode :
      (rootEntry.op != 0 && (rootEntry.op &&& 0xf0) == 0) = true := by
    simpa [IsLink, rootEntry] using queryLink
  have query : tableRead LENS codes baseOff rootWidth
      (stream slow bs) =
      some (target, rootEntry.bits.toNat + target.bits.toNat) := by
    simp only [tableRead, rootRead, bind, Option.bind, rootCell]
    simp only [queryLinkCode, ite_true, secondRead,
      targetCell]
    rfl
  have consumed : rootEntry.bits.toNat + target.bits.toNat ≤
      (stream slow bs).length := by
    have codeLe : rootEntry.bits.toNat + target.bits.toNat ≤ 15 := by
      have raw : target.bits.toNat + rootEntry.bits.toNat ≤ 15 := targetLeaf.1
      omega
    simp only [stream, List.length_append, natBits_length]
    omega
  have padding : padded (stream slow bs) = stream slow bs := by
    have long : 15 ≤ (stream slow bs).length := by
      simp only [stream, List.length_append, natBits_length]
      omega
    simp [padded, Nat.sub_eq_zero_of_le long]
  have long : 15 ≤ (stream slow bs).length := by
    simp only [stream, List.length_append, natBits_length]
    omega
  obtain ⟨other, otherCount, otherQuery, classification⟩ :=
    meaning.classify (stream slow bs) long
  have valid : ValidSymbol LENS symbol := by
    simpa [ValidSymbol] using lengthMax
  have acceptedOther : LeafAccepted LENS other :=
    classification.mpr ⟨symbol, rest, decoded, valid⟩
  have same : (other, otherCount) =
      (target, rootEntry.bits.toNat + target.bits.toNat) :=
    Option.some.inj (otherQuery.symm.trans query)
  have accepted : LeafAccepted LENS target := by
    simpa only [(Prod.mk.inj same).1] using acceptedOther
  obtain ⟨found, _, foundMeaning, _, foundDecode, _⟩ :=
    meaning.short (stream slow bs) target
      (rootEntry.bits.toNat + target.bits.toNat)
      (by rw [padding]; exact query) consumed accepted
  have decodedEq := Option.some.inj (foundDecode.symm.trans decoded)
  have symbolEq : found = symbol := congrArg Prod.fst decodedEq
  have restEq : rest = (stream slow bs).drop
      (rootEntry.bits.toNat + target.bits.toNat) :=
    (congrArg Prod.snd decodedEq).symm
  subst found
  exact ⟨linked, slice, slowNext, firstRun, againL,
    linkedHere, linkedPacket, sourceDrop, sliceEq, foundMeaning, restEq⟩

#print axioms FastInputPacket.length_selected_link_match_of_decode
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
open Zlib.Inftrees.Spec.Subtable
set_option autoImplicit false

/-- The shape-checked length-table link is exactly the code branch read by
the independent table query. This is a finite fact about the code op field. -/
theorem len_table_link_query
    {codes : Array Code} {baseOff rootWidth idx : Nat}
    (safe : LenTableSafe codes baseOff rootWidth)
    (idxBound : idx < 2 ^ rootWidth) :
    let entry := codes.getD (baseOff + idx) default
    LenLink entry ↔ IsLink LENS entry = true := by
  let entry := codes.getD (baseOff + idx) default
  constructor
  · intro link
    have linkOK := safe.2.2 idx idxBound
    rw [ite_eq_left link] at linkOK
    have smallMask : ∀ op : UInt8,
        op.toNat ≤ 15 → op &&& 0xf0 = 0 := by
      apply Zlib.Inffast.Proofs.u8_forall
      decide +kernel
    have opMask : entry.op &&& 0xf0 = 0 :=
      smallMask entry.op linkOK.2.2.1
    simp [IsLink]
    exact ⟨by simpa only [entry, Array.getD_eq_getD_getElem?] using link.1,
      by simpa only [entry, Array.getD_eq_getD_getElem?] using opMask⟩
  · intro query
    have pure : ∀ op : UInt8,
        (op != 0 && (op &&& 0xf0) == 0) = true →
        op ≠ 0 ∧ op &&& 16 = 0 ∧ op &&& 64 = 0 := by
      apply Zlib.Inffast.Proofs.u8_forall
      decide +kernel
    exact pure entry.op (by simpa [IsLink, entry] using query)

#print axioms len_table_link_query
end Zlib.Inflate.Proofs

