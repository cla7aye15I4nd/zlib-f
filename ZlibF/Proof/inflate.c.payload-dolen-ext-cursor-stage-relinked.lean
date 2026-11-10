import ZlibF.Proof.«inflate.c.payload-dolen-refill-cursor-stage-relinked»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
open Zlib.Inftrees.Spec Zlib.Inftrees.Spec.DecodeSemantics
set_option autoImplicit false
set_option maxRecDepth 4096

theorem FastInputPacket.dolenExt_valid_token_view_cursor
    {h : Heap} {slow : IL}
    {first second third fourth : UInt8} {tail : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow (first :: second :: third :: fourth :: tail) l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow (first :: second :: third :: fourth :: tail))
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff rootWidth tableUsed : Nat} {D : List Nat}
    (dcodePtr : c.dcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : DistTableSafe codes baseOff rootWidth)
    (meaning : DecodeTableInvariant.Inv DISTS codes baseOff rootWidth tableUsed D)
    (flags : FastTableFlags.QueryCompatible DISTS codes baseOff rootWidth)
    (mask : c.dmask.toUInt64.toNat = 2 ^ rootWidth - 1)
    (extraWidth : l.op.toNat ≤ 5)
    (extraFits : l.op.toNat ≤ slow.bits.toNat)
    (bitsBound : slow.bits.toNat ≤ 30)
    (left : slow.left ≠ 0) (avail : 258 ≤ slow.left.toNat)
    (length : 3 ≤ l.len.toNat ∧ l.len.toNat + 2 ^ l.op.toNat ≤ 259)
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
    (width : l.op.toNat = lengthExtras.getD (symbol - 257) 0)
    (lengthInput : r1 = stream slow (first :: second :: third :: fourth :: tail))
    (distanceCode : decodeSym D r2 = some (distanceSymbol, r3))
    (distanceSymbolBound : distanceSymbol ≤ 29)
    (distanceBits : readBits (distExtras.getD distanceSymbol 0) r3 =
      some (distanceExtra, rest))
    (lengthValue : l.len.toNat = lengthBases.getD (symbol - 257) 0)
    (dictionary : MatchHistory.saved saved c.wsize.toNat c.wnext.toNat
      c.whave.toNat woff = dict)
    (dictCount : dict.length = c.whave.toNat)
    (written : ZlibF.Math.LZ77Copy.writtenBytes output j (j - bg) = history)
    (historyCount : history.length = j - bg)
    (backBound : distBases.getD distanceSymbol 0 + distanceExtra ≤
      (dict ++ history).length) :
    ∃ used result after array slowFinal,
      used ≤ 4 ∧ used ≤ (first :: second :: third :: fourth :: tail).length ∧
      C.run (Zlib.Inffast.Proofs.dolenExt c l) h = .ok (result, after) ∧
      result.againD = false ∧ result.out = .ref dest (j + (l.len.toNat + lengthExtra)) ∧
      result.broke = l.broke ∧ result.againL = l.againL ∧
      FastInputPacket after slowFinal ((first :: second :: third :: fourth :: tail).drop used) result ∧
      stream slowFinal ((first :: second :: third :: fourth :: tail).drop used) = rest ∧
      Space.get after dest = some array ∧ array.size = output.size ∧
      Space.ro after dest = false ∧
      ZlibF.Math.LZ77Copy.writtenBytes array (j + (l.len.toNat + lengthExtra))
        ((j - bg) + (l.len.toNat + lengthExtra)) =
        copyBack dict (distBases.getD distanceSymbol 0 + distanceExtra)
          (l.len.toNat + lengthExtra) history ∧
      Token.Step L D dict history input rest
        (ZlibF.Math.LZ77Copy.writtenBytes array (j + (l.len.toNat + lengthExtra))
          ((j - bg) + (l.len.toNat + lengthExtra))) false ∧
      result.in_ = inputAdvance l.in_ used := by
  let raw := first :: second :: third :: fourth :: tail
  have actualRead := readBits_held_stream slow raw l.op.toNat extraFits
  have selectedRead : readBits l.op.toNat (stream slow raw) =
      some (lengthExtra, r2) := by
    rw [width, ← lengthInput]
    exact lengthBits
  rw [actualRead] at selectedRead
  have extraEq : lengthExtra = l.hold.toNat % 2 ^ l.op.toNat := by
    simpa only [Prod.fst, ← packet.hold] using
      (congrArg Prod.fst (Option.some.inj selectedRead)).symm
  have restEq : r2 = (stream slow raw).drop l.op.toNat := by
    simpa only [Prod.snd] using
      (congrArg Prod.snd (Option.some.inj selectedRead)).symm
  let extra : Nat := l.hold.toNat % 2 ^ l.op.toNat
  have opSmall : l.op.toNat < 32 := by omega
  have low := Zlib.Inffast.Proofs.hold_low32
    (x := l.hold) (k := l.op) opSmall
  have extraBound : extra < 2 ^ l.op.toNat := by
    exact Nat.mod_lt _ (Nat.pow_pos (by omega))
  have lenSum : l.len.toNat + extra ≤ 258 := by omega
  let delta : UInt32 := l.hold.toUInt32 &&&
    (((1 : UInt32) <<< l.op) - 1)
  have deltaEq : delta.toNat = extra := by
    simpa only [delta, extra] using low
  have lenValue : (l.len + delta).toNat =
      l.len.toNat + extra := by
    rw [Zlib.Inffast.Proofs.u32_toNat_add
      (by rw [deltaEq]; omega), deltaEq]
  have shlRun : Zlib.Inffast.shl32 1 l.op h =
      .ok ((1 : UInt32) <<< l.op, h) :=
    Zlib.Inffast.Proofs.shl32_ok opSmall
  have shrRun : Zlib.Inffast.shr64 l.hold l.op.toUInt64 h =
      .ok (l.hold >>> l.op.toUInt64, h) := by
    apply Zlib.Inffast.Proofs.shr64_ok
    rw [UInt32.toNat_toUInt64]
    omega
  let afterLen : Zlib.Inffast.L := { l with len := l.len + delta }
  have afterLenPacket : FastInputPacket h slow
      (first :: second :: third :: fourth :: tail) afterLen :=
    ⟨packet.source, packet.cursor, packet.hold, packet.bits⟩
  have within : l.op.toNat ≤ slow.bits.toNat := extraFits
  have dropped := afterLenPacket.drop_bits_default_state buffers
    l.op within (by omega)
  let slowDrop : IL := { slow with
    hold := slow.hold >>> l.op.toUInt64,
    bits := slow.bits - l.op }
  let fastDrop : Zlib.Inffast.L := { afterLen with
    hold := afterLen.hold >>> l.op.toUInt64,
    bits := afterLen.bits - l.op }
  have dropPacket : FastInputPacket h slowDrop
      (first :: second :: third :: fourth :: tail) fastDrop :=
    dropped.1
  have dropBuffers : DispatchBuffers h r slowDrop
      (first :: second :: third :: fourth :: tail) :=
    dropped.2.1
  have dropStream : stream slowDrop
      (first :: second :: third :: fourth :: tail) =
      (stream slow
        (first :: second :: third :: fourth :: tail)).drop
          l.op.toNat := dropped.2.2.1
  have dropBits : slowDrop.bits.toNat =
      slow.bits.toNat - l.op.toNat := dropped.2.2.2
  have dropBound : slowDrop.bits.toNat ≤ 30 := by omega
  have dropLength : 3 ≤ fastDrop.len.toNat ∧
      fastDrop.len.toNat ≤ 258 := by
    simpa only [fastDrop, afterLen, lenValue] using
      (show 3 ≤ l.len.toNat + extra ∧
        l.len.toNat + extra ≤ 258 by omega)
  have dropOut : fastDrop.out = .ref dest j := outPtr
  have dropPut : slowDrop.put = .ref dest oo := outputPtr
  have dropEnd : c.end_ = .ref dest
      (oo + slowDrop.left.toNat - 257) := endPtr
  have dropSize : oo + slowDrop.left.toNat ≤ output.size :=
    outputSize
  have dropGuard : C.run (Ptr.lt fastDrop.out c.end_) h =
      .ok (true, h) := guard
  have distanceSource : r2 = stream slowDrop raw := by
    rw [restEq, dropStream]
  have extraValue : extra = lengthExtra := extraEq.symm
  have lengthValue' : fastDrop.len.toNat =
      lengthBases.getD (symbol - 257) 0 + lengthExtra := by
    rw [lenValue, extraValue, lengthValue]
  obtain ⟨used, result, after, array, slowFinal,
    usedBound, usedRaw, refillRun, againD, out, broke, againL,
    finalPacket, finalSource, get, size, ro, bytes, token, cursorR⟩ :=
    dropPacket.dolenRefill_valid_token_view_cursor invariant dropBuffers
      dcodePtr codesGet safe meaning flags mask dropBound left avail
      dropLength dropOut dropPut begPtr dropEnd outputGet outputWrite
      dropSize current beginLe span dropGuard whaveBound wnextBound wsizeBound
      windowView lengthCode lengthSymbolMin lengthSymbolMax lengthBits
      distanceSource distanceCode distanceSymbolBound distanceBits lengthValue'
      dictionary dictCount written historyCount backBound
  have run : C.run (Zlib.Inffast.Proofs.dolenExt c l) h = .ok (result, after) := by
    change (Zlib.Inffast.Proofs.dolenExt c l) h = .ok (result, after)
    unfold Zlib.Inffast.Proofs.dolenExt
    rw [bind_ok shlRun, bind_ok shrRun]
    simpa only [fastDrop, afterLen, delta, C.run] using refillRun
  refine ⟨used, result, after, array, slowFinal, usedBound,
    usedRaw, run, againD, ?_, ?_, ?_, finalPacket, finalSource,
    get, size, ro, ?_, ?_, ?_⟩
  · simpa only [fastDrop, afterLen, lenValue, extraValue] using out
  · simpa only [fastDrop, afterLen] using broke
  · simpa only [fastDrop, afterLen] using againL
  · simpa only [fastDrop, afterLen, lenValue, extraValue] using bytes
  · simpa only [fastDrop, afterLen, lenValue, extraValue] using token
  · simpa only [fastDrop, afterLen] using cursorR

#print axioms FastInputPacket.dolenExt_valid_token_view_cursor
end Zlib.Inflate.Proofs
