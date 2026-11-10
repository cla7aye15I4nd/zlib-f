import ZlibF.Proof.«inflate.c.payload-valid-body-cursor-stage»
import ZlibF.Proof.«inflate.c.payload-symbols-stage»
namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
open Zlib.Inftrees.Spec Zlib.Inftrees.Spec.DecodeSemantics
open Zlib.Inftrees.Spec.DecodeSoundness Zlib.Inftrees.Spec.DecodeTableInvariant
open Zlib.Inftrees.Spec.Subtable
set_option autoImplicit false
set_option maxRecDepth 8192

theorem FastInputPacket.fast_body_of_symbols_cursor
    {h : Heap} {slow : IL}
    {first second third fourth fifth sixth : UInt8} {rawTail : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow
      (first :: second :: third :: fourth :: fifth :: sixth :: rawTail) l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow
      (first :: second :: third :: fourth :: fifth :: sixth :: rawTail))
    (statePtr : c.state = some (.tab zs))
    (mode : DataTableMode s.mode)
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff rootWidth tableUsed : Nat} {lens : List Nat}
    (lcodePtr : c.lcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : LenTableSafe codes baseOff rootWidth)
    (meaning : Inv LENS codes baseOff rootWidth tableUsed lens)
    (mask : c.lmask.toUInt64.toNat = 2 ^ rootWidth - 1)
    (bitsBound : slow.bits.toNat ≤ 30)
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
    {dict history target : List UInt8} {input tail : List Bool}
    (lengthSource : input = stream slow
      (first :: second :: third :: fourth :: fifth :: sixth :: rawTail))
    (dictionary : MatchHistory.saved saved c.wsize.toNat c.wnext.toNat
      c.whave.toNat woff = dict)
    (dictCount : dict.length = c.whave.toNat)
    (written : ZlibF.Math.LZ77Copy.writtenBytes output j (j - bg) = history)
    (historyCount : history.length = j - bg)
    (parsed : Symbols lens D dict history input tail target) :
    ∃ used result after array slowFinal made next done,
      used ≤ 7 ∧
      used ≤ (first :: second :: third :: fourth :: fifth :: sixth :: rawTail).length ∧
      C.run (Zlib.Inffast.inflate_fast_body c l) h = .ok (result, after) ∧
      FastInputPacket after slowFinal
        ((first :: second :: third :: fourth :: fifth :: sixth :: rawTail).drop used) result ∧
      Space.get after dest = some array ∧
      Token.Step lens D dict history input
        (stream slowFinal
          ((first :: second :: third :: fourth :: fifth :: sixth :: rawTail).drop used))
        next done ∧
      ZlibF.Math.LZ77Copy.writtenBytes array (j + made) ((j - bg) + made) = next ∧
      (done = false → result.out = .ref dest (j + made)) ∧
      (done = true → after = setI h zs { s with mode := TYPE } ∧
        result.broke = true ∧ made = 0) ∧
      (done = true →
        stream slowFinal
          ((first :: second :: third :: fourth :: fifth :: sixth :: rawTail).drop used) = tail ∧
        next = target) ∧
      (done = false → Symbols lens D dict next
        (stream slowFinal
          ((first :: second :: third :: fourth :: fifth :: sixth :: rawTail).drop used))
        tail target) ∧
      result.in_ = inputAdvance l.in_ used := by
  obtain ⟨canonicalRest, canonicalNext, canonicalDone,
    canonical, _⟩ :=
    ZlibF.Spec.Token.symbols_exposes_step
      lens D dict history input tail target parsed
  obtain ⟨symbol, distanceSymbol, lengthExtra, distanceExtra,
    r1, r2, r3, decoded, valid, lengthBits, distanceCode,
    distanceSymbolBound, distanceBits, backBound⟩ := canonical.parse
  obtain ⟨used, result, after, array, slowFinal,
    usedBound, usedRaw, run, packetFinal, get, effect, cursor⟩ :=
    packet.fast_body_valid_token_cursor invariant buffers statePtr mode
      lcodePtr codesGet safe meaning mask bitsBound dcodePtr distGet
      distSafe distMeaning distFlags distMask left avail outPtr outputPtr
      begPtr endPtr outputGet outputWrite outputSize current beginLe
      span guard whaveBound wnextBound wsizeBound windowView decoded
      valid lengthSource lengthBits distanceCode distanceSymbolBound
      distanceBits dictionary dictCount written historyCount backBound
  have jBound : j < output.size := by
    have endWithin : oo + slow.left.toNat - 257 ≤ output.size := by omega
    have jWithin : j ≤ output.size := by
      by_cases inside : j ≤ output.size
      · exact inside
      · have impossible := guard
        simp [C.run, Ptr.lt, outPtr, endPtr, outputGet, inside] at impossible
    have g : j < oo + slow.left.toNat - 257 := by
      have equal := guard
      simp [C.run, Ptr.lt, outPtr, endPtr, outputGet,
        jWithin, endWithin] at equal
      exact equal
    omega
  rcases effect with ⟨byte, small, _, out, arrayEq, token⟩ |
    ⟨endSymbol, _, afterEq, broke, arrayEq, token⟩ |
    ⟨large, out, restEq, bytes, token⟩
  · have bytesNext : ZlibF.Math.LZ77Copy.writtenBytes array
        (j + 1) ((j - bg) + 1) = history ++ [byte] := by
      rw [arrayEq]
      rw [ZlibF.Math.LZ77Copy.written_set_append_payload
        output j (j - bg) byte (Nat.sub_le _ _) jBound]
      rw [written]
    obtain ⟨endAlign, continueAlign⟩ := token.align_symbols parsed
    exact ⟨used, result, after, array, slowFinal, 1,
      history ++ [byte], false, usedBound, usedRaw, run,
      packetFinal, get, token, bytesNext, (fun _ => out),
      (by simp), (by simp), (fun _ => continueAlign rfl), cursor⟩
  · have bytesNext : ZlibF.Math.LZ77Copy.writtenBytes array
        (j + 0) ((j - bg) + 0) = history := by
      simpa [arrayEq] using written
    obtain ⟨endAlign, continueAlign⟩ := token.align_symbols parsed
    exact ⟨used, result, after, array, slowFinal, 0,
      history, true, usedBound, usedRaw, run, packetFinal,
      get, token, bytesNext, (by simp),
      (by intro _; exact ⟨afterEq, broke, rfl⟩),
      (fun _ => endAlign rfl), (by simp), cursor⟩
  · have tokenActual : Token.Step lens D dict history input
        (stream slowFinal
          ((first :: second :: third :: fourth :: fifth :: sixth :: rawTail).drop used))
        (ZlibF.Math.LZ77Copy.writtenBytes array
          (j + (lengthBases.getD (symbol - 257) 0 + lengthExtra))
          ((j - bg) + (lengthBases.getD (symbol - 257) 0 + lengthExtra)))
        false := by
      rw [restEq]
      exact token
    obtain ⟨endAlign, continueAlign⟩ := tokenActual.align_symbols parsed
    exact ⟨used, result, after, array, slowFinal,
      lengthBases.getD (symbol - 257) 0 + lengthExtra,
      ZlibF.Math.LZ77Copy.writtenBytes array
        (j + (lengthBases.getD (symbol - 257) 0 + lengthExtra))
        ((j - bg) + (lengthBases.getD (symbol - 257) 0 + lengthExtra)),
      false, usedBound, usedRaw, run, packetFinal, get,
      tokenActual, rfl, (fun _ => out), (by simp), (by simp),
      (fun _ => continueAlign rfl), cursor⟩

#print axioms FastInputPacket.fast_body_of_symbols_cursor
end Zlib.Inflate.Proofs
