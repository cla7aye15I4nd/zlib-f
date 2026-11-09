import ZlibF.Proof.«inflate.c.fast-semantic-slice-18»
set_option autoImplicit false

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
private theorem payload_bind_assoc {α β γ : Type}
    (m : C.M α) (f : α → C.M β) (g : β → C.M γ) :
    (m >>= f) >>= g = m >>= fun x => f x >>= g := by
  funext heap
  simp only [bind_app]
  cases m heap <;> rfl

end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
private theorem payload_pure_bind {α β : Type}
    (x : α) (f : α → C.M β) :
    (pure x : C.M α) >>= f = f x := by
  funext heap
  rfl

end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
private theorem body_from_two_pull_root
    {h after : Heap} {l selected result : Zlib.Inffast.L}
    {c : Zlib.Inffast.Ctx}
    (needsPull : l.bits < 15)
    (prefixRun : C.run (do
      let one ← Zlib.Inffast.pull l
      let two ← Zlib.Inffast.pull one
      let here ← c.lcode.add
        (two.hold &&& c.lmask.toUInt64).toNat
      pure { two with here }) h = .ok (selected, h))
    (loopRun : C.run (cdoWhile (Zlib.Inffast.dolen c)
      (fun current => pure (current.againL, current)) selected) h =
      .ok (result, after)) :
    C.run (Zlib.Inffast.inflate_fast_body c l) h =
      .ok (result, after) := by
  let prefixM : C.M Zlib.Inffast.L := do
    let one ← Zlib.Inffast.pull l
    let two ← Zlib.Inffast.pull one
    let here ← c.lcode.add
      (two.hold &&& c.lmask.toUInt64).toNat
    pure { two with here }
  have same : C.run (Zlib.Inffast.inflate_fast_body c l) h =
      C.run (prefixM >>= fun current =>
        cdoWhile (Zlib.Inffast.dolen c)
          (fun current => pure (current.againL, current)) current) h := by
    unfold Zlib.Inffast.inflate_fast_body
    simp only [needsPull, ite_true]
    simp only [prefixM, C.run, payload_bind_assoc,
      payload_pure_bind]
  rw [same]
  change (prefixM >>= fun current =>
    cdoWhile (Zlib.Inffast.dolen c)
      (fun current => pure (current.againL, current)) current) h = _
  change prefixM h = .ok (selected, h) at prefixRun
  rw [bind_app, prefixRun]
  exact loopRun

end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
open Zlib.Inftrees.Spec Zlib.Inftrees.Spec.DecodeSemantics
set_option autoImplicit false
set_option maxRecDepth 4096

/-- Two actual `dolen` passes through a length link and selected base leaf
refine one independent match token and execute the real copy. -/
theorem FastInputPacket.dolen_linked_base_four_byte_valid_token_view
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
          ((j - bg) + (lengthBases.getD (symbol - 257) 0 + lengthExtra))) false := by
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
    packet.dolen_root_link_actual_slow_frame invariant buffers
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
    have fields := length_base_symbol_fields_view lengthMin lengthMax targetMeaning
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
    finalSource, get, size, ro, bytes, token⟩ :=
    linkedPacket.dolen_base_four_byte_valid_token_view_linkable invariant linkedBuffers
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
    have fields := length_base_symbol_fields_view lengthMin lengthMax targetMeaning
    simpa only [← targetEq] using fields.2.2.1
  rw [valueEq] at token
  rw [valueEq] at resultOut bytes
  exact ⟨linked, used, result, after, array, slowFinal,
    usedBound, usedRaw, firstRun, secondRun, loopRun, noAgain, againD,
    brokeEq, resultOut, finalPacket, finalSource, get, size, ro, bytes, token⟩

#print axioms FastInputPacket.dolen_linked_base_four_byte_valid_token_view
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
open Zlib.Inftrees.Spec Zlib.Inftrees.Spec.DecodeSemantics
open Zlib.Inftrees.Spec.DecodeSoundness Zlib.Inftrees.Spec.DecodeTableInvariant
open Zlib.Inftrees.Spec.Subtable
set_option autoImplicit false
set_option maxRecDepth 4096
theorem FastInputPacket.fast_body_two_pull_root_match_token
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
    usedBound, usedRaw, dolenRun, noAgain, againD, _,
    finalPacket, finalSource, get, size, ro, token⟩ :=
    fastPacket.length_root_base_four_byte_valid_token_view
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
    bodyRun, noAgain, againD, ?_, ?_, get, size, ro, token⟩
  · rw [← suffix]
    exact finalPacket
  · rw [← suffix]
    exact finalSource

#print axioms FastInputPacket.fast_body_two_pull_root_match_token
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
open Zlib.Inftrees.Spec Zlib.Inftrees.Spec.DecodeSemantics
open Zlib.Inftrees.Spec.DecodeSoundness Zlib.Inftrees.Spec.DecodeTableInvariant
open Zlib.Inftrees.Spec.Subtable
set_option autoImplicit false
set_option maxRecDepth 4096
theorem FastInputPacket.fast_body_two_pull_linked_match_token
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
    {baseOff rootWidth rootSlice : Nat}
    {filledHold : UInt64}
    (holdEq : filledHold = (l.hold + (first.toUInt64 <<< l.bits.toUInt64)) +
      (second.toUInt64 <<< (l.bits + 8).toUInt64))
    (rootSliceEq : rootSlice = (filledHold &&& c.lmask.toUInt64).toNat)
    (lcodePtr : c.lcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : LenTableSafe codes baseOff rootWidth)
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
    {L : List Nat} {dict history : List UInt8} {input r1 r2 r3 rest : List Bool}
    {symbol distanceSymbol lengthExtra distanceExtra : Nat}
    (lengthCode : decodeSym L input = some (symbol, r1))
    (lengthMin : 257 ≤ symbol) (lengthMax : symbol ≤ 285)
    (lengthSource : input = stream slow
      (first :: second :: third :: fourth :: fifth :: sixth :: tail))
    (targetMeaning :
      let rootEntry := codes.getD (baseOff + rootSlice) default
      let slice := (filledHold >>> rootEntry.bits.toUInt32.toUInt64).toNat %
        2 ^ rootEntry.op.toNat
      SymbolEntry LENS symbol
        (codes.getD (baseOff + rootEntry.val.toNat + slice) default))
    (codeRest :
      let rootEntry := codes.getD (baseOff + rootSlice) default
      let slice := (filledHold >>> rootEntry.bits.toUInt32.toUInt64).toNat %
        2 ^ rootEntry.op.toNat
      r1 = (stream slow
        (first :: second :: third :: fourth :: fifth :: sixth :: tail)).drop
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
          ((j - bg) + (lengthBases.getD (symbol - 257) 0 + lengthExtra))) false := by
  obtain ⟨slow2, fast2, selected, actualSlice, prefixRun,
    selectedEq, selectedPacket, buffers2, _, sourceEq,
    selectedOutEq, holdFrame, putEq, leftEq, _, _, held2,
    bound2, actualSliceEq, actualRootBound⟩ :=
    packet.two_pull_root_prefix invariant buffers small
      lcodePtr codesGet safe mask
  let raw4 := third :: fourth :: fifth :: sixth :: tail
  have fastHold : fast2.hold = filledHold := holdFrame.trans holdEq.symm
  have sliceEq : actualSlice = rootSlice := by
    rw [actualSliceEq, fastHold, ← rootSliceEq]
  have selectedHere : selected.here = .ref codeRef (baseOff + rootSlice) := by
    rw [selectedEq, sliceEq]
  have out2 : selected.out = .ref dest j := selectedOutEq.trans outPtr
  have put2 : slow2.put = .ref dest oo := putEq.trans outputPtr
  have end2 : c.end_ = .ref dest (oo + slow2.left.toNat - 257) := by
    rw [leftEq]
    exact endPtr
  have size2 : oo + slow2.left.toNat ≤ output.size := by
    rw [leftEq]
    exact outputSize
  have left2 : slow2.left ≠ 0 := by rw [leftEq]; exact left
  have avail2 : 258 ≤ slow2.left.toNat := by rw [leftEq]; exact avail
  have guard2 : C.run (Ptr.lt selected.out c.end_) h = .ok (true, h) := by
    rw [out2]
    simpa only [outPtr] using guard
  have source2 : input = stream slow2 raw4 :=
    lengthSource.trans sourceEq.symm
  have target2 :
      let rootEntry := codes.getD (baseOff + rootSlice) default
      let slice := (selected.hold >>> rootEntry.bits.toUInt32.toUInt64).toNat %
        2 ^ rootEntry.op.toNat
      SymbolEntry LENS symbol
        (codes.getD (baseOff + rootEntry.val.toNat + slice) default) := by
    simpa only [selectedEq, fastHold] using targetMeaning
  have codeRest2 :
      let rootEntry := codes.getD (baseOff + rootSlice) default
      let slice := (selected.hold >>> rootEntry.bits.toUInt32.toUInt64).toNat %
        2 ^ rootEntry.op.toNat
      r1 = (stream slow2 raw4).drop
        (rootEntry.bits.toNat +
          (codes.getD (baseOff + rootEntry.val.toNat + slice) default).bits.toNat) := by
    rw [sourceEq]
    simpa only [selectedEq, fastHold] using codeRest
  obtain ⟨_, used4, result, after, array, slowFinal,
    usedBound, usedRaw, _, _, loopRun, noAgain, againD, _,
    out, finalPacket, finalSource, get, size, ro, bytes, token⟩ :=
    selectedPacket.dolen_linked_base_four_byte_valid_token_view
      invariant buffers2 selectedHere lcodePtr codesGet safe
      (by rw [← sliceEq]; exact actualRootBound)
      link (by omega) dcodePtr distGet distSafe distMeaning distFlags
      distMask bound2 left2 avail2 out2 put2 begPtr end2 outputGet
      outputWrite size2 current beginLe span guard2 whaveBound
      wnextBound wsizeBound windowView lengthCode lengthMin lengthMax
      source2 target2 codeRest2 lengthBits distanceCode
      distanceSymbolBound distanceBits dictionary dictCount written
      historyCount backBound
  have needsPull : l.bits < 15 := by
    rw [packet.bits]
    exact UInt32.lt_iff_toNat_lt.mpr small
  have bodyRun := body_from_two_pull_root needsPull prefixRun loopRun
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

#print axioms FastInputPacket.fast_body_two_pull_linked_match_token
end Zlib.Inflate.Proofs

