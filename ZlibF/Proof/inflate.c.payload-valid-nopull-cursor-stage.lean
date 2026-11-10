import ZlibF.Proof.«inflate.c.payload-eob-nopull-cursor-stage»
namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
open Zlib.Inftrees.Spec Zlib.Inftrees.Spec.DecodeSemantics
open Zlib.Inftrees.Spec.DecodeSoundness Zlib.Inftrees.Spec.DecodeTableInvariant
open Zlib.Inftrees.Spec.Subtable
set_option autoImplicit false
set_option maxRecDepth 8192

/-- One actual fast-body step selects the independent literal, end, or
match token. The three alternatives expose exact output effects. -/
theorem FastInputPacket.fast_body_no_pull_valid_token_cursor
    {h : Heap} {slow : IL}
    {first second third fourth fifth : UInt8} {tail : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow
      (first :: second :: third :: fourth :: fifth :: tail) l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow
      (first :: second :: third :: fourth :: fifth :: tail))
    (statePtr : c.state = some (.tab zs))
    (mode : DataTableMode s.mode)
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
    (decoded : decodeSym lens input = some (symbol, r1))
    (valid : symbol ≤ 285)
    (lengthSource : input = stream slow
      (first :: second :: third :: fourth :: fifth :: tail))
    (lengthBits : 257 ≤ symbol →
      readBits (lengthExtras.getD (symbol - 257) 0) r1 =
        some (lengthExtra, r2))
    (distanceCode : 257 ≤ symbol → decodeSym D r2 =
      some (distanceSymbol, r3))
    (distanceSymbolBound : 257 ≤ symbol → distanceSymbol ≤ 29)
    (distanceBits : 257 ≤ symbol →
      readBits (distExtras.getD distanceSymbol 0) r3 =
        some (distanceExtra, rest))
    (dictionary : MatchHistory.saved saved c.wsize.toNat c.wnext.toNat
      c.whave.toNat woff = dict)
    (dictCount : dict.length = c.whave.toNat)
    (written : ZlibF.Math.LZ77Copy.writtenBytes output j (j - bg) = history)
    (historyCount : history.length = j - bg)
    (backBound : 257 ≤ symbol →
      distBases.getD distanceSymbol 0 + distanceExtra ≤
        (dict ++ history).length) :
    ∃ used result after array slowFinal,
      used ≤ 5 ∧
      used ≤ (first :: second :: third :: fourth :: fifth :: tail).length ∧
      C.run (Zlib.Inffast.inflate_fast_body c l) h = .ok (result, after) ∧
      FastInputPacket after slowFinal
        ((first :: second :: third :: fourth :: fifth :: tail).drop used) result ∧
      Space.get after dest = some array ∧
      ((∃ byte, symbol < 256 ∧ used = 0 ∧
          result.out = .ref dest (j + 1) ∧
          array = output.set! j byte ∧
          Token.Step lens D dict history input
            (stream slowFinal (first :: second :: third :: fourth :: fifth :: tail))
            (history ++ [byte]) false)
       ∨ (symbol = 256 ∧ used = 0 ∧
          after = setI h zs { s with mode := TYPE } ∧
          result.broke = true ∧ array = output ∧
          Token.Step lens D dict history input
            (stream slowFinal (first :: second :: third :: fourth :: fifth :: tail))
            history true)
       ∨ (257 ≤ symbol ∧
          result.out = .ref dest
            (j + (lengthBases.getD (symbol - 257) 0 + lengthExtra)) ∧
          stream slowFinal
            ((first :: second :: third :: fourth :: fifth :: tail).drop used) = rest ∧
          ZlibF.Math.LZ77Copy.writtenBytes array
            (j + (lengthBases.getD (symbol - 257) 0 + lengthExtra))
            ((j - bg) + (lengthBases.getD (symbol - 257) 0 + lengthExtra)) =
            copyBack dict (distBases.getD distanceSymbol 0 + distanceExtra)
              (lengthBases.getD (symbol - 257) 0 + lengthExtra) history ∧
          Token.Step lens D dict history input rest
            (ZlibF.Math.LZ77Copy.writtenBytes array
              (j + (lengthBases.getD (symbol - 257) 0 + lengthExtra))
              ((j - bg) + (lengthBases.getD (symbol - 257) 0 + lengthExtra))) false)) ∧
      result.in_ = inputAdvance l.in_ used := by
  have heldLocal : ¬ l.bits < 15 := by
    intro small
    have smallNat : slow.bits.toNat < 15 := by
      simpa only [packet.bits, UInt32.toNat_ofNat] using
        UInt32.lt_iff_toNat_lt.mp small
    omega
  have decodedStream : decodeSym lens
      (stream slow (first :: second :: third :: fourth :: fifth :: tail)) =
      some (symbol, r1) := by
    rw [← lengthSource]
    exact decoded
  by_cases literal : symbol < 256
  · obtain ⟨byte, result, after, slowFinal, run, out, get,
      packetFinal, buffersFinal, token, cursor⟩ :=
      packet.fast_body_no_pull_literal_of_decode_generic_cursor
        invariant buffers heldLocal lcodePtr codesGet safe meaning
        mask rootFits left avail outPtr outputPtr endPtr
        outputGet outputWrite outputSize current guard
        decodedStream literal
    refine ⟨0, result, after, output.set! j byte, slowFinal,
      by omega, by simp, run, ?_, get, Or.inl ⟨byte, literal,
        rfl, out, rfl, ?_⟩, ?_⟩
    · simpa only [List.drop_zero] using packetFinal
    · rw [lengthSource]
      exact token
    · simpa only [inputAdvance_zero] using cursor
  · by_cases endCode : symbol = 256
    · subst symbol
      obtain ⟨result, after, slowFinal, run, afterEq, broke,
        packetFinal, buffersFinal, token, cursor⟩ :=
        packet.fast_body_no_pull_eob_of_decode_generic_cursor
          invariant buffers heldLocal statePtr mode lcodePtr
          codesGet safe meaning mask rootFits decodedStream
      have get : Space.get after dest = some output := by
        rw [afterEq, byte_view_get_setI]
        exact outputGet
      refine ⟨0, result, after, output, slowFinal,
        by omega, by simp, run, ?_, get,
        Or.inr (Or.inl ⟨rfl, rfl, afterEq, broke, rfl, ?_⟩), ?_⟩
      · simpa only [List.drop_zero] using packetFinal
      · rw [lengthSource]
        exact token
      · simpa only [inputAdvance_zero] using cursor
    · have lengthMin : 257 ≤ symbol := by omega
      obtain ⟨used, result, after, array, slowFinal,
        usedBound, usedRaw, run, _, _, _, out, packetFinal,
        finalSource, get, _, _, bytes, token, cursor⟩ :=
        packet.fast_body_no_pull_match_of_decode_with_output_cursor
          invariant buffers lcodePtr codesGet safe meaning mask
          rootFits held dcodePtr distGet distSafe distMeaning
          distFlags distMask bitsBound left avail outPtr outputPtr
          begPtr endPtr outputGet outputWrite outputSize current
          beginLe span guard whaveBound wnextBound wsizeBound
          windowView decoded lengthMin valid lengthSource
          (lengthBits lengthMin) (distanceCode lengthMin)
          (distanceSymbolBound lengthMin) (distanceBits lengthMin)
          dictionary dictCount written historyCount (backBound lengthMin)
      exact ⟨used, result, after, array, slowFinal, usedBound,
        usedRaw, run, packetFinal, get,
        Or.inr (Or.inr ⟨lengthMin, out, finalSource, bytes, token⟩), cursor⟩

#print axioms FastInputPacket.fast_body_no_pull_valid_token_cursor
end Zlib.Inflate.Proofs
