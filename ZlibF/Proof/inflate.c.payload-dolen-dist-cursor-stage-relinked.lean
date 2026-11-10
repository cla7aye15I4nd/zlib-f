import ZlibF.Proof.«inflate.c.payload-distance-cursor-split»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
open Zlib.Inftrees.Spec Zlib.Inftrees.Spec.DecodeSemantics
set_option autoImplicit false
set_option maxRecDepth 4096

theorem FastInputPacket.dolenDist_valid_token_view_cursor
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow bs l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff rootWidth tableUsed : Nat} {D : List Nat}
    (dcodePtr : c.dcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : DistTableSafe codes baseOff rootWidth)
    (meaning : DecodeTableInvariant.Inv DISTS codes baseOff rootWidth tableUsed D)
    (flags : FastTableFlags.QueryCompatible DISTS codes baseOff rootWidth)
    (mask : c.dmask.toUInt64.toNat = 2 ^ rootWidth - 1)
    (held : 15 ≤ slow.bits.toNat)
    (left : slow.left ≠ 0) (avail : 258 ≤ slow.left.toNat)
    (length : 3 ≤ l.len.toNat ∧ l.len.toNat ≤ 258)
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
    (lengthSymbolMin : 257 ≤ symbol) (lengthSymbolMax : symbol ≤ 285)
    (lengthBits : readBits (lengthExtras.getD (symbol - 257) 0) r1 =
      some (lengthExtra, r2))
    (distanceSource : r2 = stream slow bs)
    (distanceCode : decodeSym D r2 = some (distanceSymbol, r3))
    (distanceSymbolBound : distanceSymbol ≤ 29)
    (distanceBits : readBits (distExtras.getD distanceSymbol 0) r3 =
      some (distanceExtra, rest))
    (lengthValue : l.len.toNat = lengthBases.getD (symbol - 257) 0 + lengthExtra)
    (dictionary : MatchHistory.saved saved c.wsize.toNat c.wnext.toNat
      c.whave.toNat woff = dict)
    (dictCount : dict.length = c.whave.toNat)
    (written : ZlibF.Math.LZ77Copy.writtenBytes output j (j - bg) = history)
    (historyCount : history.length = j - bg)
    (backBound : distBases.getD distanceSymbol 0 + distanceExtra ≤
      (dict ++ history).length) :
    ∃ used result after array slowFinal,
      used ≤ 2 ∧ used ≤ bs.length ∧
      C.run (Zlib.Inffast.Proofs.dolenDist c l) h = .ok (result, after) ∧
      result.againD = false ∧ result.out = .ref dest (j + l.len.toNat) ∧
      result.broke = l.broke ∧ result.againL = l.againL ∧
      FastInputPacket after slowFinal (bs.drop used) result ∧
      stream slowFinal (bs.drop used) = rest ∧
      Space.get after dest = some array ∧ array.size = output.size ∧
      Space.ro after dest = false ∧
      ZlibF.Math.LZ77Copy.writtenBytes array (j + l.len.toNat)
        ((j - bg) + l.len.toNat) =
        copyBack dict (distBases.getD distanceSymbol 0 + distanceExtra)
          l.len.toNat history ∧
      Token.Step L D dict history input rest
        (ZlibF.Math.LZ77Copy.writtenBytes array (j + l.len.toNat)
          ((j - bg) + l.len.toNat)) false ∧
      result.in_ = inputAdvance l.in_ used := by
  let idx : Nat := (l.hold &&& c.dmask.toUInt64).toNat
  have idxEq : idx = l.hold.toNat % 2 ^ rootWidth :=
    Zlib.Inffast.Proofs.u64_and_mask mask
  have idxBound : idx < 2 ^ rootWidth := by
    rw [idxEq]
    exact Nat.mod_lt _ (Nat.pow_pos (by omega))
  have addRun : C.run (Ptr.add c.dcode idx) h =
      .ok (.ref codeRef (baseOff + idx), h) := by
    rw [dcodePtr]
    exact Ptr.add_nat_ok codesGet (by
      have rootSize := safe.2.1
      omega)
  let selected : Zlib.Inffast.L :=
    {l with here := .ref codeRef (baseOff + idx)}
  have selectedPacket : FastInputPacket h slow bs selected :=
    ⟨packet.source, packet.cursor, packet.hold, packet.bits⟩
  have selectedHere : selected.here =
      .ref codeRef (baseOff + selected.hold.toNat % 2 ^ rootWidth) := by
    simpa only [selected] using
      (show (Ptr.ref codeRef (baseOff + idx) : CodePtr) =
        .ref codeRef (baseOff + l.hold.toNat % 2 ^ rootWidth) by
        rw [← idxEq])
  obtain ⟨used, result, after, array, slowFinal,
    usedTwo, usedLength, loopRun, againD, out, broke, againL,
    finalPacket, source, get, size, ro, bytes, token, cursor, slowCursor, haveCount⟩ :=
    selectedPacket.dodist_loop_valid_token_view_with_frame_cursor
      (rootWidth := rootWidth) invariant buffers selectedHere
      dcodePtr codesGet meaning flags held left avail length
      outPtr outputPtr begPtr endPtr outputGet outputWrite outputSize
      current beginLe span guard whaveBound wnextBound wsizeBound windowView
      lengthCode lengthSymbolMin lengthSymbolMax lengthBits distanceSource
      distanceCode distanceSymbolBound distanceBits lengthValue
      dictionary dictCount written historyCount backBound
  have run : C.run (Zlib.Inffast.Proofs.dolenDist c l) h = .ok (result, after) := by
    change (Zlib.Inffast.Proofs.dolenDist c l) h = .ok (result, after)
    unfold Zlib.Inffast.Proofs.dolenDist
    change Ptr.add c.dcode idx h = .ok (.ref codeRef (baseOff + idx), h) at addRun
    rw [bind_ok addRun]
    simpa [C.run, selected] using loopRun
  exact ⟨used, result, after, array, slowFinal, usedTwo, usedLength,
    run, againD, out, broke, againL, finalPacket, source, get, size,
    ro, bytes, token, cursor⟩

#print axioms FastInputPacket.dolenDist_valid_token_view_cursor
end Zlib.Inflate.Proofs
