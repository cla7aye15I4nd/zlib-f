import ZlibF.Proof.«inflate.c.payload-four-root-cursor-stage-relinked»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
open Zlib.Inftrees.Spec Zlib.Inftrees.Spec.DecodeSemantics
set_option autoImplicit false
set_option maxRecDepth 4096

theorem FastInputPacket.dolen_linked_base_four_byte_valid_token_view_cursor
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
    {baseOff rootWidth rootSlice : Nat}
    (herePtr : l.here = .ref codeRef (baseOff + rootSlice))
    (lcodePtr : c.lcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : LenTableSafe codes baseOff rootWidth)
    (root : rootSlice < 2 ^ rootWidth)
    (link : LenLink (codes.getD (baseOff + rootSlice) default))
    (held : 15 ≤ slow.bits.toNat)
    {distRef : CodeRef} {distCodes : Array Code}
    {distOff distWidth distUsed : Nat} {D : List Nat}
    (dcodePtr : c.dcode = .ref distRef distOff)
    (distGet : Space.get h distRef = some distCodes)
    (distSafe : DistTableSafe distCodes distOff distWidth)
    (distMeaning : DecodeTableInvariant.Inv DISTS distCodes distOff distWidth distUsed D)
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
    (lengthSource : input = stream slow
      (first :: second :: third :: fourth :: tail))
    (targetMeaning :
      let rootEntry := codes.getD (baseOff + rootSlice) default
      let slice := (l.hold >>> rootEntry.bits.toUInt32.toUInt64).toNat %
        2 ^ rootEntry.op.toNat
      SymbolEntry LENS symbol
        (codes.getD (baseOff + rootEntry.val.toNat + slice) default))
    (codeRest :
      let rootEntry := codes.getD (baseOff + rootSlice) default
      let slice := (l.hold >>> rootEntry.bits.toUInt32.toUInt64).toNat %
        2 ^ rootEntry.op.toNat
      r1 = (stream slow
        (first :: second :: third :: fourth :: tail)).drop
        (rootEntry.bits.toNat +
          (codes.getD (baseOff + rootEntry.val.toNat + slice) default).bits.toNat))
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
    ∃ linked used result after array slowFinal,
      used ≤ 5 ∧ used ≤ (first :: second :: third :: fourth :: tail).length ∧
      C.run (Zlib.Inffast.dolen c l) h = .ok (linked, h) ∧
      C.run (Zlib.Inffast.dolen c linked) h = .ok (result, after) ∧
      C.run (cdoWhile (Zlib.Inffast.dolen c)
        (fun q => pure (q.againL, q)) l) h = .ok (result, after) ∧
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
      Token.Step L D dict history input rest
        (ZlibF.Math.LZ77Copy.writtenBytes array
          (j + (lengthBases.getD (symbol - 257) 0 + lengthExtra))
          ((j - bg) + (lengthBases.getD (symbol - 257) 0 + lengthExtra))) false ∧
      result.in_ = inputAdvance l.in_ used := by
  let raw := first :: second :: third :: fourth :: tail
  let rootEntry := codes.getD (baseOff + rootSlice) default
  let slice := (l.hold >>> rootEntry.bits.toUInt32.toUInt64).toNat %
    2 ^ rootEntry.op.toNat
  let targetIndex := baseOff + rootEntry.val.toNat + slice
  let target := codes.getD targetIndex default
  let slowLink : IL := { slow with hold := slow.hold >>> rootEntry.bits.toUInt32.toUInt64, bits := slow.bits - rootEntry.bits.toUInt32 }
  obtain ⟨linked, actualSlice, firstRun, sliceEq, linkedHere,
    againL, linkedBrokeEq, linkedOutEq, linkedLenEq, linkedPacket, linkedBuffers,
    sourceDrop⟩ :=
    packet.payload_dolen_root_link_actual_slow_frame invariant buffers
      herePtr lcodePtr codesGet safe root link held
  have sliceActual : actualSlice = slice := by simpa only [slice] using sliceEq
  have sliceBound : slice < 2 ^ rootEntry.op.toNat :=
    Nat.mod_lt _ (Nat.pow_pos (by omega))
  have targetSafe := len_table_link_target
    (codes := codes) (baseOff := baseOff) (rootBits := rootWidth)
    (rootIndex := rootSlice) (slice := slice) safe root link sliceBound
  have targetBound : targetIndex < codes.size := targetSafe.1
  have targetEq : target = codes[targetIndex] := by
    simp [target, Array.getD_eq_getD_getElem?, targetBound]
  have targetBits : target.bits.toNat + rootEntry.bits.toNat ≤ 15 := by
    simpa only [target, targetIndex] using targetSafe.2.2
  have slowLinkBits :
      slowLink.bits.toNat =
      slow.bits.toNat - rootEntry.bits.toNat := by
    change (slow.bits - rootEntry.bits.toUInt32).toNat = _
    rw [Zlib.Inffast.Proofs.u32_toNat_sub (by
      have rootWidthBound := (len_table_root_cases safe root).2.1
      have rootWidthBound' : rootEntry.bits.toNat ≤ 15 := by
        simpa only [rootEntry] using rootWidthBound
      simpa only [UInt8.toNat_toUInt32] using
        (show rootEntry.bits.toNat ≤ slow.bits.toNat by omega))]
    rfl
  have targetFits : target.bits.toNat ≤
      slowLink.bits.toNat := by
    rw [slowLinkBits]
    omega
  have targetWidth : codes[targetIndex].bits.toNat ≤ 15 := by
    rw [← targetEq]
    omega
  have targetFitsCode : codes[targetIndex].bits.toNat ≤ slowLink.bits.toNat := by
    simpa only [← targetEq] using targetFits
  have targetBase : codes[targetIndex].op &&& 16 ≠ 0 := by
    have fields := payload_length_base_symbol_fields_view lengthMin lengthMax targetMeaning
    simpa only [← targetEq] using fields.1
  have targetCode : linked.here = .ref codeRef targetIndex := by
    simpa only [targetIndex, sliceActual] using linkedHere
  have linkedOut : linked.out = .ref dest j := linkedOutEq.trans outPtr
  have linkedBitsBound :
      slowLink.bits.toNat ≤ 30 := by
    rw [slowLinkBits]
    omega
  have linkedPut :
      slowLink.put = .ref dest oo := outputPtr
  have linkedEnd : c.end_ = .ref dest
      (oo + slowLink.left.toNat - 257) := endPtr
  have linkedSize : oo +
      slowLink.left.toNat ≤ output.size := outputSize
  have linkedGuard : C.run (Ptr.lt linked.out c.end_) h = .ok (true, h) := by
    rw [linkedOut]
    simpa only [outPtr] using guard
  have targetRest : r1 = (stream
      slowLink raw).drop target.bits.toNat := by
    rw [codeRest, sourceDrop, List.drop_drop]
  have targetRestCode : r1 = (stream slowLink raw).drop codes[targetIndex].bits.toNat := by
    simpa only [← targetEq] using targetRest
  have actualCode : decodeSym L (stream slow raw) = some (symbol, r1) := by
    rw [← lengthSource]
    exact lengthCode
  have inputCode : decodeSym L input = some (symbol, r1) := by
    simpa only [lengthSource] using actualCode
  obtain ⟨used, result, after, array, slowFinal, usedBound, usedRaw,
    secondRun, noAgain, againD, resultOut, resultBroke, finalPacket,
    finalSource, get, size, ro, bytes, token, cursorBase⟩ :=
    linkedPacket.dolen_base_four_byte_valid_token_view_linkable_cursor invariant linkedBuffers
      targetCode codesGet targetBound targetFitsCode targetWidth targetBase
      dcodePtr distGet distSafe distMeaning distFlags distMask
      linkedBitsBound left avail linkedOut linkedPut begPtr linkedEnd
      outputGet outputWrite linkedSize current beginLe span linkedGuard
      whaveBound wnextBound wsizeBound windowView inputCode lengthMin lengthMax
      (by simpa only [← targetEq] using targetMeaning) targetRestCode lengthBits
      distanceCode distanceSymbolBound distanceBits dictionary dictCount
      written historyCount backBound
  have loopRun : C.run (cdoWhile (Zlib.Inffast.dolen c)
      (fun q => pure (q.againL, q)) l) h = .ok (result, after) := by
    apply Zlib.Inffast.Proofs.cdoWhile_two firstRun
      (by simp only [againL, C.run, pure] :
        C.run (pure (linked.againL, linked)) h = .ok ((true, linked), h))
      secondRun
      (by simp only [noAgain, C.run, pure] :
        C.run (pure (result.againL, result)) after = .ok ((false, result), after))
  have brokeEq : result.broke = l.broke := resultBroke.trans linkedBrokeEq
  have valueEq : codes[targetIndex].val.toNat =
      lengthBases.getD (symbol - 257) 0 := by
    have fields := payload_length_base_symbol_fields_view lengthMin lengthMax targetMeaning
    simpa only [← targetEq] using fields.2.2.1
  rw [valueEq] at token
  rw [valueEq] at resultOut bytes
  refine ⟨linked, used, result, after, array, slowFinal,
    usedBound, usedRaw, firstRun, secondRun, loopRun, noAgain, againD,
    brokeEq, resultOut, finalPacket, finalSource, get, size, ro, bytes, token, ?_⟩
  have linkedCursor := Zlib.Inffast.Proofs.dolen_continue_cursor c l h linked h firstRun againL
  simpa only [linkedCursor] using cursorBase

#print axioms FastInputPacket.dolen_linked_base_four_byte_valid_token_view_cursor
end Zlib.Inflate.Proofs
