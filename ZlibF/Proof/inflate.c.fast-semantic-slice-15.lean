import ZlibF.Proof.«inflate.c.fast-semantic-slice-14»
set_option autoImplicit false

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
open Zlib.Inftrees.Spec Zlib.Inftrees.Spec.DecodeSemantics
set_option autoImplicit false
set_option maxRecDepth 4096

/-- A selected actual length-base `dolen` call refines the independent
match token, including its real distance loop and copy output. -/
theorem FastInputPacket.dolen_base_valid_token_view
    {h : Heap} {slow : IL}
    {first second third fourth fifth : UInt8} {tail : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow
      (first :: second :: third :: fourth :: fifth :: tail) l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow
      (first :: second :: third :: fourth :: fifth :: tail))
    {codeRef : CodeRef} {codes : Array Code} {index : Nat}
    (herePtr : l.here = .ref codeRef index)
    (codesGet : Space.get h codeRef = some codes)
    (indexBound : index < codes.size)
    (codeFits : codes[index].bits.toNat ≤ slow.bits.toNat)
    (codeWidth : codes[index].bits.toNat ≤ 15)
    (base : codes[index].op &&& 16 ≠ 0)
    {distRef : CodeRef} {distCodes : Array Code}
    {distOff distWidth tableUsed : Nat} {D : List Nat}
    (dcodePtr : c.dcode = .ref distRef distOff)
    (distGet : Space.get h distRef = some distCodes)
    (distSafe : DistTableSafe distCodes distOff distWidth)
    (distMeaning : DecodeTableInvariant.Inv DISTS distCodes distOff distWidth tableUsed D)
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
    {L : List Nat} {dict history : List UInt8} {input r1 r2 r3 rest : List Bool}
    {symbol distanceSymbol lengthExtra distanceExtra : Nat}
    (lengthCode : decodeSym L input = some (symbol, r1))
    (lengthMin : 257 ≤ symbol) (lengthMax : symbol ≤ 285)
    (lengthMeaning : SymbolEntry LENS symbol codes[index])
    (lengthSource : input = stream slow
      (first :: second :: third :: fourth :: fifth :: tail))
    (codeRest : r1 = (stream slow
      (first :: second :: third :: fourth :: fifth :: tail)).drop codes[index].bits.toNat)
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
      used ≤ 5 ∧ used ≤ (first :: second :: third :: fourth :: fifth :: tail).length ∧
      C.run (Zlib.Inffast.dolen c l) h = .ok (result, after) ∧
      result.againL = false ∧ result.againD = false ∧
      result.out = .ref dest (j + (codes[index].val.toNat + lengthExtra)) ∧
      result.broke = l.broke ∧
      FastInputPacket after slowFinal
        ((first :: second :: third :: fourth :: fifth :: tail).drop used) result ∧
      stream slowFinal
        ((first :: second :: third :: fourth :: fifth :: tail).drop used) = rest ∧
      Space.get after dest = some array ∧ array.size = output.size ∧
      Space.ro after dest = false ∧
      ZlibF.Math.LZ77Copy.writtenBytes array
        (j + (codes[index].val.toNat + lengthExtra))
        ((j - bg) + (codes[index].val.toNat + lengthExtra)) =
        copyBack dict (distBases.getD distanceSymbol 0 + distanceExtra)
          (codes[index].val.toNat + lengthExtra) history ∧
      Token.Step L D dict history input rest
        (ZlibF.Math.LZ77Copy.writtenBytes array
          (j + (codes[index].val.toNat + lengthExtra))
          ((j - bg) + (codes[index].val.toNat + lengthExtra))) false := by
  let raw := first :: second :: third :: fourth :: fifth :: tail
  let entry := codes[index]
  let slowCode : IL := { slow with hold := slow.hold >>> entry.bits.toUInt32.toUInt64, bits := slow.bits - entry.bits.toUInt32 }
  let baseLocal : Zlib.Inffast.L := { l with againL := false, hold := l.hold >>> entry.bits.toUInt32.toUInt64, bits := l.bits - entry.bits.toUInt32, op := entry.op.toUInt32 &&& 15, len := entry.val.toUInt32 }
  obtain ⟨basePacket, codeBuffers, codeStream, runEq⟩ :=
    packet.dolen_base_source_prefix buffers herePtr codesGet indexBound
      codeFits codeWidth base
  have fields := length_base_symbol_fields_view lengthMin lengthMax lengthMeaning
  have baseWidth : baseLocal.op.toNat ≤ 5 := by
    simpa only [baseLocal, Zlib.Inffast.Proofs.mask15] using fields.2.2.2.1
  have baseLength : 3 ≤ baseLocal.len.toNat ∧
      baseLocal.len.toNat + 2 ^ baseLocal.op.toNat ≤ 259 := by
    simpa only [baseLocal, UInt16.toNat_toUInt32, Zlib.Inffast.Proofs.mask15] using
      (And.intro fields.2.2.2.2.1 fields.2.2.2.2.2)
  have baseBits : slowCode.bits.toNat ≤ 30 := by
    change (slow.bits - entry.bits.toUInt32).toNat ≤ 30
    rw [Zlib.Inffast.Proofs.u32_toNat_sub (by
      simpa only [entry, UInt8.toNat_toUInt32] using codeFits)]
    omega
  have baseOut : baseLocal.out = .ref dest j := outPtr
  have basePut : slowCode.put = .ref dest oo := outputPtr
  have baseEnd : c.end_ = .ref dest (oo + slowCode.left.toNat - 257) := endPtr
  have baseSize : oo + slowCode.left.toNat ≤ output.size := outputSize
  have baseGuard : C.run (Ptr.lt baseLocal.out c.end_) h = .ok (true, h) := guard
  have baseWidthEq : baseLocal.op.toNat = lengthExtras.getD (symbol - 257) 0 := by
    simpa only [baseLocal, Zlib.Inffast.Proofs.mask15] using fields.2.1
  have baseValue : baseLocal.len.toNat = lengthBases.getD (symbol - 257) 0 := by
    simpa only [baseLocal, UInt16.toNat_toUInt32] using fields.2.2.1
  have codeSource : r1 = stream slowCode raw := by
    rw [codeRest, codeStream]
  have actualCode : decodeSym L (stream slow raw) = some (symbol, r1) := by
    rw [← lengthSource]
    exact lengthCode
  have inputCode : decodeSym L input = some (symbol, r1) := by
    simpa only [lengthSource] using actualCode
  obtain ⟨used, result, after, array, slowFinal,
    usedBound, usedRaw, lenRun, againD, out, broke, againL,
    finalPacket, finalSource, get, size, ro, bytes, token⟩ :=
    basePacket.dolenLen_valid_token_view invariant codeBuffers
      dcodePtr distGet distSafe distMeaning distFlags distMask
      baseWidth baseBits left avail baseLength baseOut basePut begPtr baseEnd
      outputGet outputWrite baseSize current beginLe span baseGuard
      whaveBound wnextBound wsizeBound windowView
      inputCode lengthMin lengthMax lengthBits baseWidthEq codeSource
      distanceCode distanceSymbolBound distanceBits baseValue
      dictionary dictCount written historyCount backBound
  have run : C.run (Zlib.Inffast.dolen c l) h = .ok (result, after) := by
    rw [runEq]
    exact lenRun
  refine ⟨used, result, after, array, slowFinal, usedBound, usedRaw,
    run, ?_, againD, ?_, ?_, finalPacket, finalSource,
    get, size, ro, ?_, ?_⟩
  · simpa only [baseLocal] using againL
  · simpa only [baseLocal, UInt16.toNat_toUInt32] using out
  · simpa only [baseLocal] using broke
  · simpa only [baseLocal, UInt16.toNat_toUInt32] using bytes
  · simpa only [baseLocal, UInt16.toNat_toUInt32] using token

#print axioms FastInputPacket.dolen_base_valid_token_view
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
open Zlib.Inftrees.Spec Zlib.Inftrees.Spec.DecodeSemantics
open Zlib.Inftrees.Spec.DecodeSoundness Zlib.Inftrees.Spec.DecodeTableInvariant
open Zlib.Inftrees.Spec.Subtable
set_option autoImplicit false
set_option maxRecDepth 4096

/-- One actual root-selected length base, from code-table pointer addition
through the complete match copy, refines the independent match token. -/
theorem FastInputPacket.length_root_base_valid_token_view
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
          ((j - bg) + (lengthBases.getD (symbol - 257) 0 + lengthExtra))) false := by
  let rootSlice := (l.hold &&& c.lmask.toUInt64).toNat
  let selected : Zlib.Inffast.L := {l with here := .ref codeRef (baseOff + rootSlice)}
  let index := baseOff + rootSlice
  let entry := codes.getD index default
  obtain ⟨lookup, selectedPacket, foundSymbol, lower, upper, symbolMeaning,
    _, decoded, baseEntry, _, value, _, _, _⟩ :=
    packet.length_selected_root_base_meaning lcodePtr codesGet safe meaning
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
    get, size, ro, bytes, token⟩ :=
    selectedPacket.dolen_base_valid_token_view invariant buffers
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
    finalPacket, finalSource, get, size, ro, ?_⟩
  · simpa only [selected] using broke
  · have valueCode : codes[index].val.toNat =
        lengthBases.getD (symbol - 257) 0 := by
      simpa only [← entryEq] using value
    rw [valueCode] at token
    exact token

#print axioms FastInputPacket.length_root_base_valid_token_view
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
open Zlib.Inftrees.Spec Zlib.Inftrees.Spec.DecodeSemantics
set_option autoImplicit false
set_option maxRecDepth 4096

/-- The selected base leaf also works after an actual length-link pass:
the independent decoder's original input need only share its remainder. -/
theorem FastInputPacket.dolen_base_valid_token_view_linkable
    {h : Heap} {slow : IL}
    {first second third fourth fifth : UInt8} {tail : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow
      (first :: second :: third :: fourth :: fifth :: tail) l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow
      (first :: second :: third :: fourth :: fifth :: tail))
    {codeRef : CodeRef} {codes : Array Code} {index : Nat}
    (herePtr : l.here = .ref codeRef index)
    (codesGet : Space.get h codeRef = some codes)
    (indexBound : index < codes.size)
    (codeFits : codes[index].bits.toNat ≤ slow.bits.toNat)
    (codeWidth : codes[index].bits.toNat ≤ 15)
    (base : codes[index].op &&& 16 ≠ 0)
    {distRef : CodeRef} {distCodes : Array Code}
    {distOff distWidth tableUsed : Nat} {D : List Nat}
    (dcodePtr : c.dcode = .ref distRef distOff)
    (distGet : Space.get h distRef = some distCodes)
    (distSafe : DistTableSafe distCodes distOff distWidth)
    (distMeaning : DecodeTableInvariant.Inv DISTS distCodes distOff distWidth tableUsed D)
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
    {L : List Nat} {dict history : List UInt8} {input r1 r2 r3 rest : List Bool}
    {symbol distanceSymbol lengthExtra distanceExtra : Nat}
    (lengthCode : decodeSym L input = some (symbol, r1))
    (lengthMin : 257 ≤ symbol) (lengthMax : symbol ≤ 285)
    (lengthMeaning : SymbolEntry LENS symbol codes[index])
    (codeRest : r1 = (stream slow
      (first :: second :: third :: fourth :: fifth :: tail)).drop codes[index].bits.toNat)
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
      used ≤ 5 ∧ used ≤ (first :: second :: third :: fourth :: fifth :: tail).length ∧
      C.run (Zlib.Inffast.dolen c l) h = .ok (result, after) ∧
      result.againL = false ∧ result.againD = false ∧
      result.out = .ref dest (j + (codes[index].val.toNat + lengthExtra)) ∧
      result.broke = l.broke ∧
      FastInputPacket after slowFinal
        ((first :: second :: third :: fourth :: fifth :: tail).drop used) result ∧
      stream slowFinal
        ((first :: second :: third :: fourth :: fifth :: tail).drop used) = rest ∧
      Space.get after dest = some array ∧ array.size = output.size ∧
      Space.ro after dest = false ∧
      ZlibF.Math.LZ77Copy.writtenBytes array
        (j + (codes[index].val.toNat + lengthExtra))
        ((j - bg) + (codes[index].val.toNat + lengthExtra)) =
        copyBack dict (distBases.getD distanceSymbol 0 + distanceExtra)
          (codes[index].val.toNat + lengthExtra) history ∧
      Token.Step L D dict history input rest
        (ZlibF.Math.LZ77Copy.writtenBytes array
          (j + (codes[index].val.toNat + lengthExtra))
          ((j - bg) + (codes[index].val.toNat + lengthExtra))) false := by
  let raw := first :: second :: third :: fourth :: fifth :: tail
  let entry := codes[index]
  let slowCode : IL := { slow with hold := slow.hold >>> entry.bits.toUInt32.toUInt64, bits := slow.bits - entry.bits.toUInt32 }
  let baseLocal : Zlib.Inffast.L := { l with againL := false, hold := l.hold >>> entry.bits.toUInt32.toUInt64, bits := l.bits - entry.bits.toUInt32, op := entry.op.toUInt32 &&& 15, len := entry.val.toUInt32 }
  obtain ⟨basePacket, codeBuffers, codeStream, runEq⟩ :=
    packet.dolen_base_source_prefix buffers herePtr codesGet indexBound
      codeFits codeWidth base
  have fields := length_base_symbol_fields_view lengthMin lengthMax lengthMeaning
  have baseWidth : baseLocal.op.toNat ≤ 5 := by
    simpa only [baseLocal, Zlib.Inffast.Proofs.mask15] using fields.2.2.2.1
  have baseLength : 3 ≤ baseLocal.len.toNat ∧
      baseLocal.len.toNat + 2 ^ baseLocal.op.toNat ≤ 259 := by
    simpa only [baseLocal, UInt16.toNat_toUInt32, Zlib.Inffast.Proofs.mask15] using
      (And.intro fields.2.2.2.2.1 fields.2.2.2.2.2)
  have baseBits : slowCode.bits.toNat ≤ 30 := by
    change (slow.bits - entry.bits.toUInt32).toNat ≤ 30
    rw [Zlib.Inffast.Proofs.u32_toNat_sub (by
      simpa only [entry, UInt8.toNat_toUInt32] using codeFits)]
    omega
  have baseOut : baseLocal.out = .ref dest j := outPtr
  have basePut : slowCode.put = .ref dest oo := outputPtr
  have baseEnd : c.end_ = .ref dest (oo + slowCode.left.toNat - 257) := endPtr
  have baseSize : oo + slowCode.left.toNat ≤ output.size := outputSize
  have baseGuard : C.run (Ptr.lt baseLocal.out c.end_) h = .ok (true, h) := guard
  have baseWidthEq : baseLocal.op.toNat = lengthExtras.getD (symbol - 257) 0 := by
    simpa only [baseLocal, Zlib.Inffast.Proofs.mask15] using fields.2.1
  have baseValue : baseLocal.len.toNat = lengthBases.getD (symbol - 257) 0 := by
    simpa only [baseLocal, UInt16.toNat_toUInt32] using fields.2.2.1
  have codeSource : r1 = stream slowCode raw := by
    rw [codeRest, codeStream]
  obtain ⟨used, result, after, array, slowFinal,
    usedBound, usedRaw, lenRun, againD, out, broke, againL,
    finalPacket, finalSource, get, size, ro, bytes, token⟩ :=
    basePacket.dolenLen_valid_token_view invariant codeBuffers
      dcodePtr distGet distSafe distMeaning distFlags distMask
      baseWidth baseBits left avail baseLength baseOut basePut begPtr baseEnd
      outputGet outputWrite baseSize current beginLe span baseGuard
      whaveBound wnextBound wsizeBound windowView
      lengthCode lengthMin lengthMax lengthBits baseWidthEq codeSource
      distanceCode distanceSymbolBound distanceBits baseValue
      dictionary dictCount written historyCount backBound
  have run : C.run (Zlib.Inffast.dolen c l) h = .ok (result, after) := by
    rw [runEq]
    exact lenRun
  refine ⟨used, result, after, array, slowFinal, usedBound, usedRaw,
    run, ?_, againD, ?_, ?_, finalPacket, finalSource,
    get, size, ro, ?_, ?_⟩
  · simpa only [baseLocal] using againL
  · simpa only [baseLocal, UInt16.toNat_toUInt32] using out
  · simpa only [baseLocal] using broke
  · simpa only [baseLocal, UInt16.toNat_toUInt32] using bytes
  · simpa only [baseLocal, UInt16.toNat_toUInt32] using token

#print axioms FastInputPacket.dolen_base_valid_token_view_linkable
end Zlib.Inflate.Proofs

