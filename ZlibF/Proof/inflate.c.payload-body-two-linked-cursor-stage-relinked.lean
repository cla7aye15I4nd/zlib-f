import ZlibF.Proof.«inflate.c.payload-body-two-root-cursor-stage-relinked»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
open Zlib.Inftrees.Spec Zlib.Inftrees.Spec.DecodeSemantics
open Zlib.Inftrees.Spec.DecodeSoundness Zlib.Inftrees.Spec.DecodeTableInvariant
open Zlib.Inftrees.Spec.Subtable
set_option autoImplicit false
set_option maxRecDepth 4096

private theorem payload_link_cursor_bind_assoc {α β γ : Type}
    (m : C.M α) (f : α → C.M β) (g : β → C.M γ) :
    (m >>= f) >>= g = m >>= fun x => f x >>= g := by
  funext heap
  simp only [bind_app]
  cases m heap <;> rfl

private theorem payload_link_cursor_pure_bind {α β : Type}
    (x : α) (f : α → C.M β) :
    (pure x : C.M α) >>= f = f x := by
  funext heap
  rfl

private theorem payload_link_body_from_two_pull_root
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
    simp only [prefixM, C.run, payload_link_cursor_bind_assoc,
      payload_link_cursor_pure_bind]
  rw [same]
  change (prefixM >>= fun current =>
    cdoWhile (Zlib.Inffast.dolen c)
      (fun current => pure (current.againL, current)) current) h = _
  change prefixM h = .ok (selected, h) at prefixRun
  rw [bind_app, prefixRun]
  exact loopRun


theorem FastInputPacket.fast_body_two_pull_linked_match_token_cursor
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
          ((j - bg) + (lengthBases.getD (symbol - 257) 0 + lengthExtra))) false ∧
      result.in_ = inputAdvance l.in_ used := by
  obtain ⟨slow2, fast2, selected, actualSlice, prefixRun,
    selectedEq, selectedPacket, buffers2, _, sourceEq,
    selectedOutEq, holdFrame, putEq, leftEq, nextFrame, _, held2,
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
    out, finalPacket, finalSource, get, size, ro, bytes, token, cursor4⟩ :=
    selectedPacket.dolen_linked_base_four_byte_valid_token_view_cursor
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
  have bodyRun := payload_link_body_from_two_pull_root needsPull prefixRun loopRun
  have suffix : raw4.drop used4 =
      (first :: second :: third :: fourth :: fifth :: sixth :: tail).drop
        (2 + used4) := by
    simp only [raw4]
    rw [← List.drop_drop]
    rfl
  refine ⟨2 + used4, result, after, array, slowFinal,
    by omega, (by simp only [List.length_cons] at usedRaw ⊢; omega),
    bodyRun, noAgain, againD, out, ?_, ?_, get, size, ro, bytes, token, ?_⟩
  · rw [← suffix]
    exact finalPacket
  · rw [← suffix]
    exact finalSource
  · have selectedCursor : selected.in_ = inputAdvance l.in_ 2 := by
      rw [selectedPacket.cursor, nextFrame, ← packet.cursor]
    rw [cursor4, selectedCursor, inputAdvance_add]

#print axioms FastInputPacket.fast_body_two_pull_linked_match_token_cursor
end Zlib.Inflate.Proofs
