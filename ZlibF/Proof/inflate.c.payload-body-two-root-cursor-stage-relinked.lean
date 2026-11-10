import ZlibF.Proof.«inflate.c.payload-body-linked-cursor-stage-relinked»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
open Zlib.Inftrees.Spec Zlib.Inftrees.Spec.DecodeSemantics
open Zlib.Inftrees.Spec.DecodeSoundness Zlib.Inftrees.Spec.DecodeTableInvariant
open Zlib.Inftrees.Spec.Subtable
set_option autoImplicit false
set_option maxRecDepth 4096

private theorem payload_cursor_bind_assoc {α β γ : Type}
    (m : C.M α) (f : α → C.M β) (g : β → C.M γ) :
    (m >>= f) >>= g = m >>= fun x => f x >>= g := by
  funext heap
  simp only [bind_app]
  cases m heap <;> rfl

private theorem payload_cursor_pure_bind {α β : Type}
    (x : α) (f : α → C.M β) :
    (pure x : C.M α) >>= f = f x := by
  funext heap
  rfl

private theorem payload_body_from_two_pull_root
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
    simp only [prefixM, C.run, payload_cursor_bind_assoc,
      payload_cursor_pure_bind]
  rw [same]
  change (prefixM >>= fun current =>
    cdoWhile (Zlib.Inffast.dolen c)
      (fun current => pure (current.againL, current)) current) h = _
  change prefixM h = .ok (selected, h) at prefixRun
  rw [bind_app, prefixRun]
  exact loopRun


theorem FastInputPacket.fast_body_two_pull_root_match_token_cursor
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
          ((j - bg) + (lengthBases.getD (symbol - 257) 0 + lengthExtra))) false ∧
      result.in_ = inputAdvance l.in_ used := by
  obtain ⟨slow2, fast2, selected, rootSlice, prefixRun,
    selectedEq, selectedPacket, buffers2, _, sourceEq,
    selectedOutEq, holdFrame, putEq, leftEq, nextFrame, _, held2,
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
    finalPacket, finalSource, get, size, ro, token, cursor4⟩ :=
    fastPacket.length_root_base_four_byte_valid_token_view_cursor
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
  have bodyRun := payload_body_from_two_pull_root needsPull prefixRun selectedLoop
  have suffix : raw4.drop used4 =
      (first :: second :: third :: fourth :: fifth :: sixth :: tail).drop
        (2 + used4) := by
    simp only [raw4]
    rw [← List.drop_drop]
    rfl
  refine ⟨2 + used4, result, after, array, slowFinal,
    by omega, (by simp only [List.length_cons] at usedRaw ⊢; omega),
    bodyRun, noAgain, againD, ?_, ?_, get, size, ro, token, ?_⟩
  · rw [← suffix]
    exact finalPacket
  · rw [← suffix]
    exact finalSource
  · have fast2Cursor : fast2.in_ = inputAdvance l.in_ 2 := by
      have eq : fast2.in_ = slow2.next := by
        simpa only [selectedEq] using selectedPacket.cursor
      rw [eq, nextFrame, ← packet.cursor]
    rw [cursor4, fast2Cursor, inputAdvance_add]

#print axioms FastInputPacket.fast_body_two_pull_root_match_token_cursor
end Zlib.Inflate.Proofs
