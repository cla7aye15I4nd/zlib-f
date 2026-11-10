import ZlibF.Proof.«inflate.c.payload-unified-stage»
set_option maxRecDepth 8192

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
open Zlib.Inftrees.Spec Zlib.Inftrees.Spec.DecodeSemantics
open Zlib.Inftrees.Spec.DecodeSoundness Zlib.Inftrees.Spec.DecodeTableInvariant
open Zlib.Inftrees.Spec.Subtable
set_option autoImplicit false
set_option maxRecDepth 4096
theorem FastInputPacket.length_root_base_valid_token_view_with_output
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
      result.out = .ref dest
        (j + (lengthBases.getD (symbol - 257) 0 + lengthExtra)) ∧
      FastInputPacket after slowFinal
        ((first :: second :: third :: fourth :: fifth :: tail).drop used) result ∧
      stream slowFinal
        ((first :: second :: third :: fourth :: fifth :: tail).drop used) = rest ∧
      Space.get after dest = some array ∧ array.size = output.size ∧
      Space.ro after dest = false ∧
      ZlibF.Math.LZ77Copy.writtenBytes array
        (j + (lengthBases.getD (symbol - 257) 0 + lengthExtra))
        ((j - bg) + (lengthBases.getD (symbol - 257) 0 + lengthExtra)) =
        copyBack dict (distBases.getD distanceSymbol 0 + distanceExtra)
          (lengthBases.getD (symbol - 257) 0 + lengthExtra) history ∧
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
  have valueCode : codes[index].val.toNat =
      lengthBases.getD (symbol - 257) 0 := by
    simpa only [← entryEq] using value
  rw [valueCode] at out bytes token
  exact ⟨lookup, used, result, after, array, slowFinal,
    usedBound, usedRaw, run, againL, againD,
    by simpa only [selected] using broke,
    out, finalPacket, finalSource, get, size, ro, bytes, token⟩

#print axioms FastInputPacket.length_root_base_valid_token_view_with_output
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
open Zlib.Inftrees.Spec Zlib.Inftrees.Spec.DecodeSemantics
open Zlib.Inftrees.Spec.DecodeSoundness Zlib.Inftrees.Spec.DecodeTableInvariant
open Zlib.Inftrees.Spec.Subtable
set_option autoImplicit false
theorem FastInputPacket.length_root_base_body_no_pull_token_view_with_output
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
    C.run (c.lcode.add rootSlice) h =
      .ok (.ref codeRef (baseOff + rootSlice), h) ∧
    ∃ used result after array slowFinal,
      used ≤ 5 ∧ used ≤ (first :: second :: third :: fourth :: fifth :: tail).length ∧
      C.run (Zlib.Inffast.inflate_fast_body c l) h = .ok (result, after) ∧
      result.againL = false ∧ result.againD = false ∧ result.broke = l.broke ∧
      result.out = .ref dest
        (j + (lengthBases.getD (symbol - 257) 0 + lengthExtra)) ∧
      FastInputPacket after slowFinal
        ((first :: second :: third :: fourth :: fifth :: tail).drop used) result ∧
      stream slowFinal
        ((first :: second :: third :: fourth :: fifth :: tail).drop used) = rest ∧
      Space.get after dest = some array ∧ array.size = output.size ∧
      Space.ro after dest = false ∧
      ZlibF.Math.LZ77Copy.writtenBytes array
        (j + (lengthBases.getD (symbol - 257) 0 + lengthExtra))
        ((j - bg) + (lengthBases.getD (symbol - 257) 0 + lengthExtra)) =
        copyBack dict (distBases.getD distanceSymbol 0 + distanceExtra)
          (lengthBases.getD (symbol - 257) 0 + lengthExtra) history ∧
      Token.Step lens D dict history input rest
        (ZlibF.Math.LZ77Copy.writtenBytes array
          (j + (lengthBases.getD (symbol - 257) 0 + lengthExtra))
          ((j - bg) + (lengthBases.getD (symbol - 257) 0 + lengthExtra))) false := by
  have prior := packet.length_root_base_valid_token_view_with_output
    invariant buffers lcodePtr codesGet safe meaning mask rootFits held
    noLink accepted base dcodePtr distGet distSafe distMeaning distFlags
    distMask bitsBound left avail outPtr outputPtr begPtr endPtr outputGet
    outputWrite outputSize current beginLe span guard whaveBound wnextBound
    wsizeBound windowView lengthCode lengthSource lengthBits distanceCode
    distanceSymbolBound distanceBits dictionary dictCount written historyCount
    backBound
  dsimp only at prior ⊢
  obtain ⟨addRun, used, result, after, array, slowFinal,
    usedBound, usedRaw, run, againL, againD, broke, out, finalPacket,
    finalSource, get, size, ro, bytes, token⟩ := prior
  have notSmall : ¬ l.bits < 15 := by
    intro less
    have lessNat : l.bits.toNat < 15 := UInt32.lt_iff_toNat_lt.mp less
    rw [packet.bits] at lessNat
    omega
  have loopRun := dolen_loop_one run againL
  have bodyRun : C.run (Zlib.Inffast.inflate_fast_body c l) h =
      .ok (result, after) := by
    unfold Zlib.Inffast.inflate_fast_body
    simp only [notSmall, ite_false]
    unfold C.run at addRun ⊢
    simp only [bind_app, addRun]
    exact loopRun
  exact ⟨addRun, used, result, after, array, slowFinal,
    usedBound, usedRaw, bodyRun, againL, againD, broke, out,
    finalPacket, finalSource, get, size, ro, bytes, token⟩

#print axioms FastInputPacket.length_root_base_body_no_pull_token_view_with_output
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
open Zlib.Inftrees.Spec Zlib.Inftrees.Spec.DecodeSemantics
open Zlib.Inftrees.Spec.DecodeSoundness Zlib.Inftrees.Spec.DecodeTableInvariant
open Zlib.Inftrees.Spec.Subtable
set_option autoImplicit false
theorem FastInputPacket.length_root_body_no_pull_match_of_decode_with_output
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
      result.out = .ref dest
        (j + (lengthBases.getD (symbol - 257) 0 + lengthExtra)) ∧
      FastInputPacket after slowFinal
        ((first :: second :: third :: fourth :: fifth :: tail).drop used) result ∧
      stream slowFinal
        ((first :: second :: third :: fourth :: fifth :: tail).drop used) = rest ∧
      Space.get after dest = some array ∧ array.size = output.size ∧
      Space.ro after dest = false ∧
      ZlibF.Math.LZ77Copy.writtenBytes array
        (j + (lengthBases.getD (symbol - 257) 0 + lengthExtra))
        ((j - bg) + (lengthBases.getD (symbol - 257) 0 + lengthExtra)) =
        copyBack dict (distBases.getD distanceSymbol 0 + distanceExtra)
          (lengthBases.getD (symbol - 257) 0 + lengthExtra) history ∧
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
  exact packet.length_root_base_body_no_pull_token_view_with_output
    invariant buffers lcodePtr codesGet safe meaning mask rootFits held
    noLink accepted base dcodePtr distGet distSafe distMeaning distFlags
    distMask bitsBound left avail outPtr outputPtr begPtr endPtr outputGet
    outputWrite outputSize current beginLe span guard whaveBound wnextBound
    wsizeBound windowView lengthCode lengthSource lengthBits distanceCode
    distanceSymbolBound distanceBits dictionary dictCount written historyCount
    backBound

#print axioms FastInputPacket.length_root_body_no_pull_match_of_decode_with_output
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
open Zlib.Inftrees.Spec Zlib.Inftrees.Spec.DecodeSemantics
open Zlib.Inftrees.Spec.DecodeSoundness Zlib.Inftrees.Spec.DecodeTableInvariant
open Zlib.Inftrees.Spec.Subtable
set_option autoImplicit false
theorem FastInputPacket.length_root_base_four_byte_valid_token_view_with_output
    {h : Heap} {slow : IL}
    {first second third fourth : UInt8} {tail : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow
      (first :: second :: third :: fourth :: tail) l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow
      (first :: second :: third :: fourth :: tail))
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
      (first :: second :: third :: fourth :: tail))
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
      used ≤ 5 ∧ used ≤ (first :: second :: third :: fourth :: tail).length ∧
      C.run (Zlib.Inffast.dolen c selected) h = .ok (result, after) ∧
      result.againL = false ∧ result.againD = false ∧ result.broke = l.broke ∧
      result.out = .ref dest
        (j + (lengthBases.getD (symbol - 257) 0 + lengthExtra)) ∧
      FastInputPacket after slowFinal
        ((first :: second :: third :: fourth :: tail).drop used) result ∧
      stream slowFinal
        ((first :: second :: third :: fourth :: tail).drop used) = rest ∧
      Space.get after dest = some array ∧ array.size = output.size ∧
      Space.ro after dest = false ∧
      ZlibF.Math.LZ77Copy.writtenBytes array
        (j + (lengthBases.getD (symbol - 257) 0 + lengthExtra))
        ((j - bg) + (lengthBases.getD (symbol - 257) 0 + lengthExtra)) =
        copyBack dict (distBases.getD distanceSymbol 0 + distanceExtra)
          (lengthBases.getD (symbol - 257) 0 + lengthExtra) history ∧
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
      (stream slow (first :: second :: third :: fourth :: tail)) =
      some (symbol, r1) := by
    rw [← lengthSource]
    exact lengthCode
  have same := Option.some.inj (decoded.symm.trans actualLength)
  have symbolEq : foundSymbol = symbol := congrArg Prod.fst same
  have restEq : r1 = (stream slow
      (first :: second :: third :: fourth :: tail)).drop entry.bits.toNat :=
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
      (first :: second :: third :: fourth :: tail)).drop
        codes[index].bits.toNat := by
    simpa only [← entryEq] using restEq
  obtain ⟨used, result, after, array, slowFinal, usedBound, usedRaw,
    run, againL, againD, out, broke, finalPacket, finalSource,
    get, size, ro, bytes, token⟩ :=
    selectedPacket.dolen_base_four_byte_valid_token_view invariant buffers
      selectedHere codesGet indexBound codeFits codeWidth baseCode
      dcodePtr distGet distSafe distMeaning distFlags distMask bitsBound
      left avail selectedOut outputPtr begPtr endPtr outputGet outputWrite
      outputSize current beginLe span selectedGuard whaveBound wnextBound
      wsizeBound windowView lengthCode lower upper
      (by simpa only [← entryEq] using symbolMeaning) lengthSource
      codeRest lengthBits distanceCode distanceSymbolBound distanceBits
      dictionary dictCount written historyCount backBound
  have valueCode : codes[index].val.toNat =
      lengthBases.getD (symbol - 257) 0 := by
    simpa only [← entryEq] using value
  rw [valueCode] at out bytes token
  exact ⟨lookup, used, result, after, array, slowFinal,
    usedBound, usedRaw, run, againL, againD,
    by simpa only [selected] using broke,
    out, finalPacket, finalSource, get, size, ro, bytes, token⟩

#print axioms FastInputPacket.length_root_base_four_byte_valid_token_view_with_output
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
open Zlib.Inftrees.Spec Zlib.Inftrees.Spec.DecodeSemantics
open Zlib.Inftrees.Spec.DecodeSoundness Zlib.Inftrees.Spec.DecodeTableInvariant
open Zlib.Inftrees.Spec.Subtable
set_option autoImplicit false
theorem FastInputPacket.fast_body_two_pull_root_match_token_with_output
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
    (accepted : LeafAccepted LENS
      (codes.getD (baseOff + filledHold.toNat % 2 ^ rootWidth) default))
    (base : (codes.getD (baseOff + filledHold.toNat % 2 ^ rootWidth) default).op &&& 16 ≠ 0)
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
      Token.Step lens D dict history input rest
        (ZlibF.Math.LZ77Copy.writtenBytes array
          (j + (lengthBases.getD (symbol - 257) 0 + lengthExtra))
          ((j - bg) + (lengthBases.getD (symbol - 257) 0 + lengthExtra))) false := by
  obtain ⟨slow2, fast2, selected, rootSlice, prefixRun,
    selectedEq, selectedPacket, buffers2, _, sourceEq,
    selectedOutEq, holdFrame, putEq, leftEq, _, _, held2,
    bound2, rootSliceEq, _⟩ :=
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
  have accepted2 : LeafAccepted LENS
      (codes.getD (baseOff + fast2.hold.toNat % 2 ^ rootWidth) default) := by
    rwa [fastHold]
  have base2 : (codes.getD
      (baseOff + fast2.hold.toNat % 2 ^ rootWidth) default).op &&& 16 ≠ 0 := by
    rwa [fastHold]
  have out2 : fast2.out = .ref dest j := by
    have eq : selected.out = fast2.out := by rw [selectedEq]
    rw [← eq, selectedOutEq]
    exact outPtr
  have put2 : slow2.put = .ref dest oo := putEq.trans outputPtr
  have end2 : c.end_ = .ref dest (oo + slow2.left.toNat - 257) := by
    rw [leftEq]
    exact endPtr
  have size2 : oo + slow2.left.toNat ≤ output.size := by
    rw [leftEq]
    exact outputSize
  have left2 : slow2.left ≠ 0 := by rw [leftEq]; exact left
  have avail2 : 258 ≤ slow2.left.toNat := by rw [leftEq]; exact avail
  have guard2 : C.run (Ptr.lt fast2.out c.end_) h = .ok (true, h) := by
    rw [out2]
    simpa only [outPtr] using guard
  have source2 : input = stream slow2 raw4 := by
    exact lengthSource.trans sourceEq.symm
  obtain ⟨_, used4, result, after, array, slowFinal,
    usedBound, usedRaw, dolenRun, noAgain, againD, _, out,
    finalPacket, finalSource, get, size, ro, bytes, token⟩ :=
    fastPacket.length_root_base_four_byte_valid_token_view_with_output
      invariant buffers2 lcodePtr codesGet safe meaning mask
      rootFits2 (by omega) noLink2 accepted2 base2
      dcodePtr distGet distSafe distMeaning distFlags distMask bound2
      left2 avail2 out2 put2 begPtr end2 outputGet outputWrite size2
      current beginLe span guard2 whaveBound wnextBound wsizeBound
      windowView lengthCode source2 lengthBits distanceCode
      distanceSymbolBound distanceBits dictionary dictCount written
      historyCount backBound
  have selectedLoop : C.run (cdoWhile (Zlib.Inffast.dolen c)
      (fun q => pure (q.againL, q)) selected) h = .ok (result, after) := by
    have loopRun := dolen_loop_one dolenRun noAgain
    simpa only [selectedEq, rootSliceEq] using loopRun
  have needsPull : l.bits < 15 := by
    rw [packet.bits]
    exact UInt32.lt_iff_toNat_lt.mpr small
  have bodyRun := body_from_two_pull_root needsPull prefixRun selectedLoop
  have suffix : raw4.drop used4 =
      (first :: second :: third :: fourth :: fifth :: sixth :: tail).drop
        (2 + used4) := by
    simp only [raw4]
    rw [← List.drop_drop]
    rfl
  refine ⟨2 + used4, result, after, array, slowFinal,
    by omega, (by simp only [List.length_cons] at usedRaw ⊢; omega),
    bodyRun, noAgain, againD, out, ?_, ?_, get, size, ro, bytes, token⟩
  · rw [← suffix]
    exact finalPacket
  · rw [← suffix]
    exact finalSource

#print axioms FastInputPacket.fast_body_two_pull_root_match_token_with_output
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
open Zlib.Inftrees.Spec Zlib.Inftrees.Spec.DecodeSemantics
open Zlib.Inftrees.Spec.DecodeSoundness Zlib.Inftrees.Spec.DecodeTableInvariant
open Zlib.Inftrees.Spec.Subtable
set_option autoImplicit false
theorem FastInputPacket.fast_body_two_pull_root_match_of_decode_with_output
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
  exact packet.fast_body_two_pull_root_match_token_with_output
    invariant buffers lcodePtr codesGet safe meaning mask small
    holdEq noLink accepted base dcodePtr distGet distSafe distMeaning
    distFlags distMask left avail outPtr outputPtr begPtr endPtr
    outputGet outputWrite outputSize current beginLe span guard
    whaveBound wnextBound wsizeBound windowView lengthCode lengthSource
    lengthBits distanceCode distanceSymbolBound distanceBits
    dictionary dictCount written historyCount backBound

#print axioms FastInputPacket.fast_body_two_pull_root_match_of_decode_with_output
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
open Zlib.Inftrees.Spec Zlib.Inftrees.Spec.DecodeSemantics
open Zlib.Inftrees.Spec.DecodeSoundness Zlib.Inftrees.Spec.DecodeTableInvariant
open Zlib.Inftrees.Spec.Subtable
set_option autoImplicit false
theorem FastInputPacket.fast_body_no_pull_match_of_decode_with_output
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
    ∃ used result after array slowFinal,
      used ≤ 5 ∧ used ≤ (first :: second :: third :: fourth :: fifth :: tail).length ∧
      C.run (Zlib.Inffast.inflate_fast_body c l) h = .ok (result, after) ∧
      result.againL = false ∧ result.againD = false ∧ result.broke = l.broke ∧
      result.out = .ref dest
        (j + (lengthBases.getD (symbol - 257) 0 + lengthExtra)) ∧
      FastInputPacket after slowFinal
        ((first :: second :: third :: fourth :: fifth :: tail).drop used) result ∧
      stream slowFinal
        ((first :: second :: third :: fourth :: fifth :: tail).drop used) = rest ∧
      Space.get after dest = some array ∧ array.size = output.size ∧
      Space.ro after dest = false ∧
      ZlibF.Math.LZ77Copy.writtenBytes array
        (j + (lengthBases.getD (symbol - 257) 0 + lengthExtra))
        ((j - bg) + (lengthBases.getD (symbol - 257) 0 + lengthExtra)) =
        copyBack dict (distBases.getD distanceSymbol 0 + distanceExtra)
          (lengthBases.getD (symbol - 257) 0 + lengthExtra) history ∧
      Token.Step lens D dict history input rest
        (ZlibF.Math.LZ77Copy.writtenBytes array
          (j + (lengthBases.getD (symbol - 257) 0 + lengthExtra))
          ((j - bg) + (lengthBases.getD (symbol - 257) 0 + lengthExtra))) false := by
  let rootSlice := (l.hold &&& c.lmask.toUInt64).toNat
  have maskIndex : rootSlice = l.hold.toNat % 2 ^ rootWidth :=
    Zlib.Inffast.Proofs.u64_and_mask mask
  have root : rootSlice < 2 ^ rootWidth := by
    rw [maskIndex]
    exact Nat.mod_lt _ (Nat.pow_pos (by omega))
  by_cases link : LenLink (codes.getD (baseOff + rootSlice) default)
  · obtain ⟨_, used, result, after, array, slowFinal,
      usedBound, usedRaw, _, _, _, bodyRun, againL, againD,
      broke, out, finalPacket, finalSource, get, size, ro, bytes, token⟩ :=
      packet.dolen_linked_body_no_pull_match_of_decode
        invariant buffers (by rfl) lcodePtr codesGet safe meaning mask
        root link held dcodePtr distGet distSafe distMeaning distFlags
        distMask bitsBound left avail outPtr outputPtr begPtr endPtr
        outputGet outputWrite outputSize current beginLe span guard
        whaveBound wnextBound wsizeBound windowView lengthCode
        lengthMin lengthMax lengthSource lengthBits distanceCode
        distanceSymbolBound distanceBits dictionary dictCount written
        historyCount backBound
    exact ⟨used, result, after, array, slowFinal,
      usedBound, usedRaw, bodyRun, againL, againD, broke, out,
      finalPacket, finalSource, get, size, ro, bytes, token⟩
  · have queryFalse : IsLink LENS
        (codes.getD (baseOff + rootSlice) default) = false := by
      cases hq : IsLink LENS
          (codes.getD (baseOff + rootSlice) default) with
      | false => rfl
      | true =>
        exact False.elim (link ((len_table_link_query safe root).mpr hq))
    have noLink : IsLink LENS
        (codes.getD (baseOff + l.hold.toNat % 2 ^ rootWidth) default) = false := by
      simpa only [maskIndex] using queryFalse
    obtain ⟨_, used, result, after, array, slowFinal,
      usedBound, usedRaw, bodyRun, againL, againD, broke, out,
      finalPacket, finalSource, get, size, ro, bytes, token⟩ :=
      packet.length_root_body_no_pull_match_of_decode_with_output
        invariant buffers lcodePtr codesGet safe meaning mask
        rootFits held noLink dcodePtr distGet distSafe distMeaning
        distFlags distMask bitsBound left avail outPtr outputPtr begPtr
        endPtr outputGet outputWrite outputSize current beginLe span
        guard whaveBound wnextBound wsizeBound windowView lengthCode
        lengthMin lengthMax lengthSource lengthBits distanceCode
        distanceSymbolBound distanceBits dictionary dictCount written
        historyCount backBound
    exact ⟨used, result, after, array, slowFinal,
      usedBound, usedRaw, bodyRun, againL, againD, broke, out,
      finalPacket, finalSource, get, size, ro, bytes, token⟩

#print axioms FastInputPacket.fast_body_no_pull_match_of_decode_with_output
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
open Zlib.Inftrees.Spec Zlib.Inftrees.Spec.DecodeSemantics
open Zlib.Inftrees.Spec.DecodeSoundness Zlib.Inftrees.Spec.DecodeTableInvariant
open Zlib.Inftrees.Spec.Subtable
set_option autoImplicit false
theorem FastInputPacket.fast_body_two_pull_match_of_decode_with_output
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
      Token.Step lens D dict history input rest
        (ZlibF.Math.LZ77Copy.writtenBytes array
          (j + (lengthBases.getD (symbol - 257) 0 + lengthExtra))
          ((j - bg) + (lengthBases.getD (symbol - 257) 0 + lengthExtra))) false := by
  let rootSlice := (filledHold &&& c.lmask.toUInt64).toNat
  have maskIndex : rootSlice = filledHold.toNat % 2 ^ rootWidth :=
    Zlib.Inffast.Proofs.u64_and_mask mask
  have root : rootSlice < 2 ^ rootWidth := by
    rw [maskIndex]
    exact Nat.mod_lt _ (Nat.pow_pos (by omega))
  by_cases link : LenLink (codes.getD (baseOff + rootSlice) default)
  · obtain ⟨used, result, after, array, slowFinal,
      usedBound, usedRaw, bodyRun, againL, againD, out,
      finalPacket, finalSource, get, size, ro, bytes, token⟩ :=
      packet.fast_body_two_pull_linked_match_of_decode
        invariant buffers holdEq (by rfl) lcodePtr codesGet safe
        meaning mask link small dcodePtr distGet distSafe distMeaning
        distFlags distMask left avail outPtr outputPtr begPtr endPtr
        outputGet outputWrite outputSize current beginLe span guard
        whaveBound wnextBound wsizeBound windowView lengthCode lengthMin
        lengthMax lengthSource lengthBits distanceCode distanceSymbolBound
        distanceBits dictionary dictCount written historyCount backBound
    exact ⟨used, result, after, array, slowFinal,
      usedBound, usedRaw, bodyRun, againL, againD, out,
      finalPacket, finalSource, get, size, ro, bytes, token⟩
  · have queryFalse : IsLink LENS
        (codes.getD (baseOff + rootSlice) default) = false := by
      cases hq : IsLink LENS
          (codes.getD (baseOff + rootSlice) default) with
      | false => rfl
      | true =>
        exact False.elim (link ((len_table_link_query safe root).mpr hq))
    have noLink : IsLink LENS
        (codes.getD (baseOff + filledHold.toNat % 2 ^ rootWidth) default) = false := by
      simpa only [maskIndex] using queryFalse
    obtain ⟨used, result, after, array, slowFinal,
      usedBound, usedRaw, bodyRun, againL, againD, out,
      finalPacket, finalSource, get, size, ro, bytes, token⟩ :=
      packet.fast_body_two_pull_root_match_of_decode_with_output
        invariant buffers lcodePtr codesGet safe meaning mask small
        holdEq noLink dcodePtr distGet distSafe distMeaning distFlags
        distMask left avail outPtr outputPtr begPtr endPtr outputGet
        outputWrite outputSize current beginLe span guard whaveBound
        wnextBound wsizeBound windowView lengthCode lengthMin lengthMax
        lengthSource lengthBits distanceCode distanceSymbolBound
        distanceBits dictionary dictCount written historyCount backBound
    exact ⟨used, result, after, array, slowFinal,
      usedBound, usedRaw, bodyRun, againL, againD, out,
      finalPacket, finalSource, get, size, ro, bytes, token⟩

#print axioms FastInputPacket.fast_body_two_pull_match_of_decode_with_output
end Zlib.Inflate.Proofs
