import ZlibF.Proof.«inflate.c.payload-dolen-base-cursor-stage-relinked»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
open Zlib.Inftrees.Spec Zlib.Inftrees.Spec.DecodeSemantics
open Zlib.Inftrees.Spec.DecodeSoundness Zlib.Inftrees.Spec.DecodeTableInvariant
open Zlib.Inftrees.Spec.DecodeShort
open Zlib.Inftrees.Spec.Subtable
set_option autoImplicit false
set_option maxRecDepth 4096

theorem FastInputPacket.payload_length_root_leaf_meaning
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L}
    (packet : FastInputPacket h slow bs l)
    {codes : Array Code} {baseOff rootWidth used : Nat}
    {lens : List Nat}
    (meaning : Inv LENS codes baseOff rootWidth used lens)
    (rootFits : rootWidth ≤ slow.bits.toNat)
    (held : 15 ≤ slow.bits.toNat)
    (indexBound : baseOff +
      (l.hold.toNat % 2 ^ rootWidth) < codes.size)
    (noLink : IsLink LENS
      (codes.getD (baseOff + (l.hold.toNat % 2 ^ rootWidth)) default) = false)
    (accepted : LeafAccepted LENS
      (codes.getD (baseOff + (l.hold.toNat % 2 ^ rootWidth)) default)) :
    let entry := codes.getD
      (baseOff + (l.hold.toNat % 2 ^ rootWidth)) default
    ∃ symbol,
      ValidSymbol LENS symbol ∧
      SymbolEntry LENS symbol entry ∧
      entry.bits.toNat = lens.getD symbol 0 ∧
      decodeSym lens (stream slow bs) =
        some (symbol, (stream slow bs).drop entry.bits.toNat) := by
  let slice := l.hold.toNat % 2 ^ rootWidth
  let entry := codes.getD (baseOff + slice) default
  have rootRead := readBits_held_stream slow bs rootWidth rootFits
  have rootReadL : readBits rootWidth (stream slow bs) =
      some (slice, (stream slow bs).drop rootWidth) := by
    simpa only [slice, ← packet.hold] using rootRead
  have cell : codes[baseOff + slice]? = some entry := by
    have bound : baseOff + slice < codes.size := indexBound
    simp [entry, Array.getD_eq_getD_getElem?, bound]
  have noLinkCode :
      (entry.op != 0 && (entry.op &&& 0xf0) == 0) = false := by
    simpa [IsLink, entry, slice] using noLink
  have query : tableRead LENS codes baseOff rootWidth
      (stream slow bs) = some (entry, entry.bits.toNat) := by
    simp only [tableRead, rootReadL, bind, Option.bind, cell]
    simp only [noLinkCode]
    simp
  have long : 15 ≤ (stream slow bs).length := by
    simp only [stream, List.length_append, natBits_length]
    omega
  have padding : padded (stream slow bs) = stream slow bs := by
    simp [padded, Nat.sub_eq_zero_of_le long]
  have fit : entry.bits.toNat ≤ (stream slow bs).length := by
    obtain ⟨tableEntry, tableCell, _, tableBits⟩ :=
      meaning.rootTable.2.2.2 slice
        (Nat.mod_lt _ (Nat.pow_pos (by omega)))
    have same : tableEntry = entry :=
      Option.some.inj (tableCell.symm.trans cell)
    rw [same] at tableBits
    simp only [stream, List.length_append, natBits_length]
    omega
  obtain ⟨symbol, valid, entryMeaning, codeLen,
    decoded, _⟩ := meaning.short (stream slow bs) entry
    entry.bits.toNat (by rw [padding]; exact query) fit accepted
  exact ⟨symbol, valid, entryMeaning, codeLen, decoded⟩


theorem FastInputPacket.payload_length_selected_root_leaf_meaning
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    (packet : FastInputPacket h slow bs l)
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff rootWidth used : Nat} {lens : List Nat}
    (lcodePtr : c.lcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : LenTableSafe codes baseOff rootWidth)
    (meaning : Inv LENS codes baseOff rootWidth used lens)
    (mask : c.lmask.toUInt64.toNat = 2 ^ rootWidth - 1)
    (rootFits : rootWidth ≤ slow.bits.toNat)
    (held : 15 ≤ slow.bits.toNat)
    (noLink : IsLink LENS
      (codes.getD (baseOff + (l.hold.toNat % 2 ^ rootWidth)) default) = false)
    (accepted : LeafAccepted LENS
      (codes.getD (baseOff + (l.hold.toNat % 2 ^ rootWidth)) default)) :
    let rootSlice := (l.hold &&& c.lmask.toUInt64).toNat
    let selected : Zlib.Inffast.L :=
      { l with here := .ref codeRef (baseOff + rootSlice) }
    let entry := codes.getD (baseOff + rootSlice) default
    C.run (c.lcode.add rootSlice) h =
      .ok (.ref codeRef (baseOff + rootSlice), h) ∧
    FastInputPacket h slow bs selected ∧
    ∃ symbol,
      ValidSymbol LENS symbol ∧
      SymbolEntry LENS symbol entry ∧
      entry.bits.toNat = lens.getD symbol 0 ∧
      decodeSym lens (stream slow bs) =
        some (symbol, (stream slow bs).drop entry.bits.toNat) := by
  obtain ⟨_, addRun, selectedPacket⟩ :=
    packet.fast_body_root_lookup lcodePtr codesGet safe mask
  have maskIndex : (l.hold &&& c.lmask.toUInt64).toNat =
      l.hold.toNat % 2 ^ rootWidth :=
    Zlib.Inffast.Proofs.u64_and_mask mask
  have rootBound : baseOff +
      (l.hold.toNat % 2 ^ rootWidth) < codes.size := by
    have rootSize := safe.2.1
    have modBound : l.hold.toNat % 2 ^ rootWidth <
        2 ^ rootWidth :=
      Nat.mod_lt _ (Nat.pow_pos (by omega))
    omega
  obtain ⟨symbol, valid, entryMeaning, width, decoded⟩ :=
    packet.payload_length_root_leaf_meaning meaning rootFits held
      rootBound noLink accepted
  refine ⟨addRun, selectedPacket, symbol, valid, ?_, ?_, ?_⟩
  · simpa only [maskIndex] using entryMeaning
  · simpa only [maskIndex] using width
  · simpa only [maskIndex] using decoded


theorem payload_length_base_symbol_lower_view {symbol : Nat} {entry : Code}
    (valid : ValidSymbol LENS symbol)
    (meaning : SymbolEntry LENS symbol entry)
    (base : entry.op &&& 16 ≠ 0) : 257 ≤ symbol := by
  have hi : symbol ≤ 285 := by simpa [ValidSymbol] using valid
  by_cases small : symbol < 256
  · have fields : entry.op = 0 ∧ entry.val.toNat = symbol := by
      simpa only [SymbolEntry, ite_true, ite_eq_left small] using meaning
    simp [fields.1] at base
  · by_cases ending : symbol = 256
    · subst symbol
      have fields : entry.op = 96 ∧ entry.val = 0 := by
        simpa [SymbolEntry] using meaning
      rw [fields.1] at base
      exact False.elim (base (by decide))
    · omega


theorem FastInputPacket.payload_length_selected_root_base_meaning
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    (packet : FastInputPacket h slow bs l)
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff rootWidth used : Nat} {lens : List Nat}
    (lcodePtr : c.lcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : LenTableSafe codes baseOff rootWidth)
    (meaning : Inv LENS codes baseOff rootWidth used lens)
    (mask : c.lmask.toUInt64.toNat = 2 ^ rootWidth - 1)
    (rootFits : rootWidth ≤ slow.bits.toNat)
    (held : 15 ≤ slow.bits.toNat)
    (noLink : IsLink LENS
      (codes.getD (baseOff + l.hold.toNat % 2 ^ rootWidth) default) = false)
    (accepted : LeafAccepted LENS
      (codes.getD (baseOff + l.hold.toNat % 2 ^ rootWidth) default))
    (base : (codes.getD (baseOff + l.hold.toNat % 2 ^ rootWidth) default).op &&& 16 ≠ 0) :
    let rootSlice := (l.hold &&& c.lmask.toUInt64).toNat
    let selected : Zlib.Inffast.L :=
      { l with here := .ref codeRef (baseOff + rootSlice) }
    let entry := codes.getD (baseOff + rootSlice) default
    C.run (c.lcode.add rootSlice) h =
      .ok (.ref codeRef (baseOff + rootSlice), h) ∧
    FastInputPacket h slow bs selected ∧
    ∃ symbol,
      257 ≤ symbol ∧ symbol ≤ 285 ∧
      SymbolEntry LENS symbol entry ∧
      entry.bits.toNat = lens.getD symbol 0 ∧
      decodeSym lens (stream slow bs) =
        some (symbol, (stream slow bs).drop entry.bits.toNat) ∧
      entry.op &&& 16 ≠ 0 ∧
      (entry.op &&& 15).toNat = lengthExtras.getD (symbol - 257) 0 ∧
      entry.val.toNat = lengthBases.getD (symbol - 257) 0 ∧
      (entry.op &&& 15).toNat ≤ 5 ∧
      3 ≤ entry.val.toNat ∧
      entry.val.toNat + 2 ^ (entry.op &&& 15).toNat ≤ 259 := by
  obtain ⟨lookup, selectedPacket, symbol, valid, symbolMeaning, width, decoded⟩ :=
    packet.payload_length_selected_root_leaf_meaning lcodePtr codesGet safe meaning
      mask rootFits held noLink accepted
  have maskIndex : (l.hold &&& c.lmask.toUInt64).toNat =
      l.hold.toNat % 2 ^ rootWidth :=
    Zlib.Inffast.Proofs.u64_and_mask mask
  have baseSelected :
      (codes.getD (baseOff + (l.hold &&& c.lmask.toUInt64).toNat) default).op &&& 16 ≠ 0 := by
    simpa only [maskIndex] using base
  have lower := payload_length_base_symbol_lower_view valid symbolMeaning
    (by simpa only [maskIndex] using baseSelected)
  have upper : symbol ≤ 285 := by simpa [ValidSymbol] using valid
  have fields := payload_length_base_symbol_fields_view lower upper symbolMeaning
  exact ⟨lookup, selectedPacket, symbol, lower, upper,
    symbolMeaning, width, decoded, fields⟩


theorem FastInputPacket.length_root_base_valid_token_view_cursor
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
    (accepted : LeafAccepted LENS
      (codes.getD (baseOff + l.hold.toNat % 2 ^ rootWidth) default))
    (base : (codes.getD (baseOff + l.hold.toNat % 2 ^ rootWidth) default).op &&& 16 ≠ 0)
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
    let selected : Zlib.Inffast.L :=
      {l with here := .ref codeRef (baseOff + rootSlice)}
    C.run (c.lcode.add rootSlice) h =
      .ok (.ref codeRef (baseOff + rootSlice), h) ∧
    ∃ used result after array slowFinal,
      used ≤ 5 ∧ used ≤ (first :: second :: third :: fourth :: fifth :: tail).length ∧
      C.run (Zlib.Inffast.dolen c selected) h = .ok (result, after) ∧
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
          ((j - bg) + (lengthBases.getD (symbol - 257) 0 + lengthExtra))) false ∧
      result.in_ = inputAdvance l.in_ used := by
  let rootSlice := (l.hold &&& c.lmask.toUInt64).toNat
  let selected : Zlib.Inffast.L := {l with here := .ref codeRef (baseOff + rootSlice)}
  let index := baseOff + rootSlice
  let entry := codes.getD index default
  obtain ⟨lookup, selectedPacket, foundSymbol, lower, upper, symbolMeaning,
    _, decoded, baseEntry, _, value, _, _, _⟩ :=
    packet.payload_length_selected_root_base_meaning lcodePtr codesGet safe meaning
      mask rootFits held noLink accepted base
  have actualLength : decodeSym lens
      (stream slow (first :: second :: third :: fourth :: fifth :: tail)) =
      some (symbol, r1) := by
    rw [← lengthSource]
    exact lengthCode
  have same := Option.some.inj (decoded.symm.trans actualLength)
  have symbolEq : foundSymbol = symbol := congrArg Prod.fst same
  have restEq : r1 = (stream slow
      (first :: second :: third :: fourth :: fifth :: tail)).drop entry.bits.toNat :=
    (congrArg Prod.snd same).symm
  subst foundSymbol
  have rootBound : rootSlice < 2 ^ rootWidth := by
    have maskIndex : rootSlice = l.hold.toNat % 2 ^ rootWidth :=
      Zlib.Inffast.Proofs.u64_and_mask mask
    rw [maskIndex]
    exact Nat.mod_lt _ (Nat.pow_pos (by omega))
  have indexBound : index < codes.size := by
    have rootSize := safe.2.1
    omega
  have entryEq : entry = codes[index] := by
    simp [entry, Array.getD_eq_getD_getElem?, indexBound]
  have codeWidth : codes[index].bits.toNat ≤ 15 := by
    have cases := len_table_root_cases safe rootBound
    have found : entry.bits.toNat ≤ 15 := by
      simpa only [entry, index] using cases.2.1
    rwa [entryEq] at found
  have codeFits : codes[index].bits.toNat ≤ slow.bits.toNat := by omega
  have baseCode : codes[index].op &&& 16 ≠ 0 := by
    simpa only [← entryEq] using baseEntry
  have selectedHere : selected.here = .ref codeRef index := rfl
  have selectedOut : selected.out = .ref dest j := outPtr
  have selectedGuard : C.run (Ptr.lt selected.out c.end_) h = .ok (true, h) := guard
  have codeRest : r1 = (stream slow
      (first :: second :: third :: fourth :: fifth :: tail)).drop
        codes[index].bits.toNat := by
    simpa only [← entryEq] using restEq
  obtain ⟨used, result, after, array, slowFinal, usedBound, usedRaw,
    run, againL, againD, out, broke, finalPacket, finalSource,
    get, size, ro, bytes, token, cursorBase⟩ :=
    selectedPacket.dolen_base_valid_token_view_cursor invariant buffers
      selectedHere codesGet indexBound codeFits codeWidth baseCode
      dcodePtr distGet distSafe distMeaning distFlags distMask bitsBound
      left avail selectedOut outputPtr begPtr endPtr outputGet outputWrite
      outputSize current beginLe span selectedGuard whaveBound wnextBound
      wsizeBound windowView lengthCode lower upper
      (by simpa only [← entryEq] using symbolMeaning) lengthSource
      codeRest lengthBits distanceCode distanceSymbolBound distanceBits
      dictionary dictCount written historyCount backBound
  refine ⟨lookup, used, result, after, array, slowFinal,
    usedBound, usedRaw, run, againL, againD, ?_,
    finalPacket, finalSource, get, size, ro, ?_, ?_⟩
  · simpa only [selected] using broke
  · have valueCode : codes[index].val.toNat =
        lengthBases.getD (symbol - 257) 0 := by
      simpa only [← entryEq] using value
    rw [valueCode] at token
    exact token
  · simpa only [selected] using cursorBase

#print axioms FastInputPacket.length_root_base_valid_token_view_cursor
end Zlib.Inflate.Proofs
