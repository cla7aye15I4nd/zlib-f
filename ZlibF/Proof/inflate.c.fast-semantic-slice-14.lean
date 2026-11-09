import ZlibF.Proof.«inflate.c.fast-semantic-slice-13»
set_option autoImplicit false

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
private theorem dolenLen_positive_from_prefix
    {h after : Heap} {c : Zlib.Inffast.Ctx}
    {l fast result : Zlib.Inffast.L}
    (positive : l.op ≠ 0)
    (prefixRun : C.run
      (if l.bits < l.op then Zlib.Inffast.pull l else pure l) h =
      .ok (fast, h))
    (extRun : C.run (Zlib.Inffast.Proofs.dolenExt c fast) h =
      .ok (result, after)) :
    C.run (Zlib.Inffast.Proofs.dolenLen c l) h =
      .ok (result, after) := by
  have nonzero : (l.op != 0) = true := by
    simp [positive]
  by_cases needsPull : l.bits < l.op
  · have pullRun : C.run (Zlib.Inffast.pull l) h =
        .ok (fast, h) := by
      simpa only [needsPull, ite_true] using prefixRun
    change (Zlib.Inffast.Proofs.dolenLen c l) h =
      .ok (result, after)
    unfold Zlib.Inffast.Proofs.dolenLen
    simp only [nonzero, ite_true, needsPull]
    rw [bind_ok (by simpa only [C.run] using pullRun)]
    exact extRun
  · have fastEq : fast = l := by
      have pureRun : C.run (pure l : C.M Zlib.Inffast.L) h =
          .ok (fast, h) := by
        simpa only [needsPull, ite_false] using prefixRun
      have fields : fast = l ∧ h = h := by
        simpa only [C.run, pure, Except.ok.injEq,
          Prod.mk.injEq] using pureRun.symm
      exact fields.1
    change (Zlib.Inffast.Proofs.dolenLen c l) h =
      .ok (result, after)
    unfold Zlib.Inffast.Proofs.dolenLen
    simp only [nonzero, ite_true, needsPull, ite_false]
    simpa only [fastEq, C.run] using extRun

end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
open Zlib.Inftrees.Spec Zlib.Inftrees.Spec.DecodeSemantics
set_option autoImplicit false
set_option maxRecDepth 4096

/-- The actual length-extra arithmetic and bit drop transport the
independently read value into the valid distance-copy token suffix. -/
theorem FastInputPacket.dolenExt_valid_token_view
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
          ((j - bg) + (l.len.toNat + lengthExtra))) false := by
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
    finalPacket, finalSource, get, size, ro, bytes, token⟩ :=
    dropPacket.dolenRefill_valid_token_view invariant dropBuffers
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
    get, size, ro, ?_, ?_⟩
  · simpa only [fastDrop, afterLen, lenValue, extraValue] using out
  · simpa only [fastDrop, afterLen] using broke
  · simpa only [fastDrop, afterLen] using againL
  · simpa only [fastDrop, afterLen, lenValue, extraValue] using bytes
  · simpa only [fastDrop, afterLen, lenValue, extraValue] using token

#print axioms FastInputPacket.dolenExt_valid_token_view
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
open Zlib.Inftrees.Spec Zlib.Inftrees.Spec.DecodeSemantics
set_option autoImplicit false
set_option maxRecDepth 4096

/-- The actual length-extra selection, optional one-byte pull, and
distance suffix refine one independent match token on caller byte views. -/
theorem FastInputPacket.dolenLen_valid_token_view
    {h : Heap} {slow : IL}
    {first second third fourth fifth : UInt8} {tail : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow (first :: second :: third :: fourth :: fifth :: tail) l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow (first :: second :: third :: fourth :: fifth :: tail))
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff rootWidth tableUsed : Nat} {D : List Nat}
    (dcodePtr : c.dcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : DistTableSafe codes baseOff rootWidth)
    (meaning : DecodeTableInvariant.Inv DISTS codes baseOff rootWidth tableUsed D)
    (flags : FastTableFlags.QueryCompatible DISTS codes baseOff rootWidth)
    (mask : c.dmask.toUInt64.toNat = 2 ^ rootWidth - 1)
    (extraWidth : l.op.toNat ≤ 5)
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
    (lengthInput : r1 = stream slow (first :: second :: third :: fourth :: fifth :: tail))
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
      used ≤ 5 ∧ used ≤ (first :: second :: third :: fourth :: fifth :: tail).length ∧
      C.run (Zlib.Inffast.Proofs.dolenLen c l) h = .ok (result, after) ∧
      result.againD = false ∧ result.out = .ref dest (j + (l.len.toNat + lengthExtra)) ∧
      result.broke = l.broke ∧ result.againL = l.againL ∧
      FastInputPacket after slowFinal ((first :: second :: third :: fourth :: fifth :: tail).drop used) result ∧
      stream slowFinal ((first :: second :: third :: fourth :: fifth :: tail).drop used) = rest ∧
      Space.get after dest = some array ∧ array.size = output.size ∧
      Space.ro after dest = false ∧
      ZlibF.Math.LZ77Copy.writtenBytes array (j + (l.len.toNat + lengthExtra))
        ((j - bg) + (l.len.toNat + lengthExtra)) =
        copyBack dict (distBases.getD distanceSymbol 0 + distanceExtra)
          (l.len.toNat + lengthExtra) history ∧
      Token.Step L D dict history input rest
        (ZlibF.Math.LZ77Copy.writtenBytes array (j + (l.len.toNat + lengthExtra))
          ((j - bg) + (l.len.toNat + lengthExtra))) false := by
  by_cases hasExtra : l.op != 0
  · by_cases needsPull : l.bits < l.op
    · have small : slow.bits.toNat ≤ 22 := by
        have less := UInt32.lt_iff_toNat_lt.mp needsPull
        rw [packet.bits] at less
        omega
      obtain ⟨next1, fast1, slow1, pullRun, _, slow1Eq, fast1Eq,
        packet1, _, buffers1, stream1⟩ :=
        packet.pull_default_state invariant buffers small
      have opEq : fast1.op = l.op := by rw [fast1Eq]; rfl
      have lenEq : fast1.len = l.len := by rw [fast1Eq]; rfl
      have fits1 : fast1.op.toNat ≤ slow1.bits.toNat := by
        rw [opEq, slow1Eq]
        change l.op.toNat ≤ (slow.bits + 8).toNat
        rw [u32_add8 slow.bits (by omega)]
        omega
      have bound1 : slow1.bits.toNat ≤ 30 := by
        rw [slow1Eq]
        change (slow.bits + 8).toNat ≤ 30
        rw [u32_add8 slow.bits (by omega)]
        omega
      have width1 : fast1.op.toNat ≤ 5 := by rw [opEq]; exact extraWidth
      have length1 : 3 ≤ fast1.len.toNat ∧
          fast1.len.toNat + 2 ^ fast1.op.toNat ≤ 259 := by
        simpa only [opEq, lenEq] using length
      have out1 : fast1.out = .ref dest j := by
        rw [fast1Eq]
        exact outPtr
      have put1 : slow1.put = .ref dest oo := by
        rw [slow1Eq]
        exact outputPtr
      have end1 : c.end_ = .ref dest (oo + slow1.left.toNat - 257) := by
        simpa only [slow1Eq, pulled] using endPtr
      have size1 : oo + slow1.left.toNat ≤ output.size := by
        simpa only [slow1Eq, pulled] using outputSize
      have guard1 : C.run (Ptr.lt fast1.out c.end_) h = .ok (true, h) := by
        rw [out1]
        simpa only [outPtr] using guard
      have left1 : slow1.left ≠ 0 := by
        simpa only [slow1Eq, pulled] using left
      have avail1 : 258 ≤ slow1.left.toNat := by
        simpa only [slow1Eq, pulled] using avail
      have input1 : r1 = stream slow1 (second :: third :: fourth :: fifth :: tail) := by
        rw [lengthInput, stream1]
      have width1Eq : fast1.op.toNat = lengthExtras.getD (symbol - 257) 0 := by
        rw [opEq]
        exact width
      have value1 : fast1.len.toNat = lengthBases.getD (symbol - 257) 0 := by
        rw [lenEq]
        exact lengthValue
      obtain ⟨usedExt, result, after, array, slowFinal,
        usedBound, usedRaw, extRun, againD, out, broke, againL,
        finalPacket, finalSource, get, size, ro, bytes, token⟩ :=
        packet1.dolenExt_valid_token_view invariant buffers1
          dcodePtr codesGet safe meaning flags mask width1 fits1 bound1
          left1 avail1 length1 out1 put1 begPtr end1 outputGet outputWrite
          size1 current beginLe span guard1 whaveBound wnextBound wsizeBound
          windowView lengthCode lengthSymbolMin lengthSymbolMax lengthBits
          width1Eq input1 distanceCode distanceSymbolBound distanceBits value1
          dictionary dictCount written historyCount backBound
      have prefixRun : C.run
          (if l.bits < l.op then Zlib.Inffast.pull l else pure l) h =
          .ok (fast1, h) := by
        simpa only [needsPull, ite_true] using pullRun
      have positive : l.op ≠ 0 := by
        simpa only [bne_iff_ne] using hasExtra
      have run := dolenLen_positive_from_prefix positive
        prefixRun extRun
      have tailEq : (second :: third :: fourth :: fifth :: tail).drop usedExt =
          (first :: second :: third :: fourth :: fifth :: tail).drop (1 + usedExt) := by
        calc
          (second :: third :: fourth :: fifth :: tail).drop usedExt =
              ((first :: second :: third :: fourth :: fifth :: tail).drop 1).drop usedExt := rfl
          _ = (first :: second :: third :: fourth :: fifth :: tail).drop (1 + usedExt) := by
            rw [List.drop_drop]
      refine ⟨1 + usedExt, result, after, array, slowFinal,
        by omega, (by simp only [List.length_cons] at usedRaw ⊢; omega),
        run, againD, ?_, ?_, ?_,
        by simpa only [tailEq] using finalPacket,
        by simpa only [tailEq] using finalSource,
        get, size, ro, ?_, ?_⟩
      · simpa only [lenEq] using out
      · simpa only [fast1Eq, Zlib.Inffast.Proofs.pullL] using broke
      · simpa only [fast1Eq, Zlib.Inffast.Proofs.pullL] using againL
      · simpa only [lenEq] using bytes
      · simpa only [lenEq] using token
    · have fits : l.op.toNat ≤ slow.bits.toNat := by
        have noLess : ¬ l.op.toNat > l.bits.toNat := by
          intro h
          exact needsPull (UInt32.lt_iff_toNat_lt.mpr h)
        rw [packet.bits] at noLess
        omega
      obtain ⟨used, result, after, array, slowFinal,
        usedBound, usedRaw, extRun, againD, out, broke, againL,
        finalPacket, finalSource, get, size, ro, bytes, token⟩ :=
        packet.dolenExt_valid_token_view invariant buffers
          dcodePtr codesGet safe meaning flags mask extraWidth fits bitsBound
          left avail length outPtr outputPtr begPtr endPtr outputGet outputWrite
          outputSize current beginLe span guard whaveBound wnextBound wsizeBound
          windowView lengthCode lengthSymbolMin lengthSymbolMax lengthBits
          width lengthInput distanceCode distanceSymbolBound distanceBits lengthValue
          dictionary dictCount written historyCount backBound
      have run : C.run (Zlib.Inffast.Proofs.dolenLen c l) h = .ok (result, after) := by
        unfold Zlib.Inffast.Proofs.dolenLen
        simp only [hasExtra, needsPull, ite_true, ite_false]
        exact extRun
      exact ⟨used, result, after, array, slowFinal,
        by omega, usedRaw, run, againD, out, broke, againL,
        finalPacket, finalSource, get, size, ro, bytes, token⟩
  · have opZero : l.op = 0 := by simpa using hasExtra
    have lengthZero : 3 ≤ l.len.toNat ∧ l.len.toNat ≤ 258 := by
      rw [opZero] at length
      simp only [UInt32.toNat_zero, Nat.pow_zero] at length
      omega
    have zeroWidth : lengthExtras.getD (symbol - 257) 0 = 0 := by
      rw [← width, opZero]
      rfl
    have zeroRead : r2 = stream slow (first :: second :: third :: fourth :: fifth :: tail) := by
      rw [zeroWidth, lengthInput] at lengthBits
      simp only [readBits, Option.some.injEq, Prod.mk.injEq] at lengthBits
      exact lengthBits.2.symm
    have zeroValue : lengthExtra = 0 := by
      rw [zeroWidth] at lengthBits
      simp only [readBits, Option.some.injEq, Prod.mk.injEq] at lengthBits
      exact lengthBits.1.symm
    obtain ⟨used, result, after, array, slowFinal,
      usedBound, usedRaw, refillRun, againD, out, broke, againL,
      finalPacket, finalSource, get, size, ro, bytes, token⟩ :=
      packet.dolenRefill_valid_token_view invariant buffers
        dcodePtr codesGet safe meaning flags mask bitsBound left avail lengthZero
        outPtr outputPtr begPtr endPtr outputGet outputWrite outputSize current
        beginLe span guard whaveBound wnextBound wsizeBound windowView
        lengthCode lengthSymbolMin lengthSymbolMax lengthBits zeroRead
        distanceCode distanceSymbolBound distanceBits
        (by rw [zeroValue]; exact lengthValue)
        dictionary dictCount written historyCount backBound
    have run : C.run (Zlib.Inffast.Proofs.dolenLen c l) h = .ok (result, after) := by
      unfold Zlib.Inffast.Proofs.dolenLen
      simp only [opZero, bne_self_eq_false, Bool.false_eq_true, ite_false]
      exact refillRun
    refine ⟨used, result, after, array, slowFinal,
      by omega, usedRaw, run, againD, ?_, broke, againL,
      finalPacket, finalSource, get, size, ro, ?_, ?_⟩
    · simpa only [zeroValue, Nat.add_zero] using out
    · simpa only [zeroValue, Nat.add_zero] using bytes
    · simpa only [zeroValue, Nat.add_zero] using token

#print axioms FastInputPacket.dolenLen_valid_token_view
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
set_option autoImplicit false

/-- The actual selected length-base leaf reduces to its checked extra-bit
and distance suffix, with the exact bit stream after the code drop. -/
theorem FastInputPacket.dolen_base_source_prefix
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef}
    (packet : FastInputPacket h slow bs l)
    (buffers : DispatchBuffers h r slow bs)
    {codeRef : CodeRef} {codes : Array Code} {index : Nat}
    (herePtr : l.here = .ref codeRef index)
    (codesGet : Space.get h codeRef = some codes)
    (indexBound : index < codes.size)
    (codeFits : codes[index].bits.toNat ≤ slow.bits.toNat)
    (codeWidth : codes[index].bits.toNat ≤ 15)
    (base : codes[index].op &&& 16 ≠ 0) :
    let entry := codes[index]
    let slowCode : IL := { slow with hold := slow.hold >>> entry.bits.toUInt32.toUInt64, bits := slow.bits - entry.bits.toUInt32 }
    let baseLocal : Zlib.Inffast.L :=
      { l with againL := false, hold := l.hold >>> entry.bits.toUInt32.toUInt64, bits := l.bits - entry.bits.toUInt32, op := entry.op.toUInt32 &&& 15, len := entry.val.toUInt32 }
    FastInputPacket h slowCode bs baseLocal ∧
    DispatchBuffers h r slowCode bs ∧
    stream slowCode bs = (stream slow bs).drop entry.bits.toNat ∧
    C.run (Zlib.Inffast.dolen c l) h =
      C.run (Zlib.Inffast.Proofs.dolenLen c baseLocal) h := by
  let entry : Code := codes[index]
  have load : Ptr.load l.here h = .ok (entry, h) := by
    rw [herePtr]
    exact Ptr.load_ok codesGet indexBound
  let count : UInt32 := entry.bits.toUInt32
  have countFits : count.toNat ≤ slow.bits.toNat := by
    simpa only [count, entry, Zlib.Inffast.Proofs.toNat32] using codeFits
  have countSmall : count.toNat < 64 := by
    have width : count.toNat ≤ 15 := by
      simpa only [count, entry, Zlib.Inffast.Proofs.toNat32] using codeWidth
    omega
  let firstLocal : Zlib.Inffast.L := {l with againL := false, op := count}
  have firstPacket : FastInputPacket h slow bs firstLocal :=
    ⟨packet.source, packet.cursor, packet.hold, packet.bits⟩
  have dropped := firstPacket.drop_bits_default_state buffers count countFits countSmall
  let slowCode : IL := {slow with
    hold := slow.hold >>> count.toUInt64, bits := slow.bits - count}
  let afterCode : Zlib.Inffast.L := {firstLocal with
    hold := firstLocal.hold >>> count.toUInt64,
    bits := firstLocal.bits - count}
  have codePacket : FastInputPacket h slowCode bs afterCode := dropped.1
  have codeBuffers : DispatchBuffers h r slowCode bs := dropped.2.1
  have codeStream : stream slowCode bs = (stream slow bs).drop entry.bits.toNat := by
    simpa only [count, Zlib.Inffast.Proofs.toNat32] using dropped.2.2.1
  let baseLocal : Zlib.Inffast.L := {afterCode with
    op := entry.op.toUInt32 &&& 15, len := entry.val.toUInt32}
  have basePacket : FastInputPacket h slowCode bs baseLocal :=
    ⟨codePacket.source, codePacket.cursor, codePacket.hold, codePacket.bits⟩
  have baseBool : (entry.op.toUInt32 &&& 16 != 0) = true := by
    rw [Zlib.Inffast.Proofs.mask16]
    simpa only [entry, bne_iff_ne] using base
  have notLiteral : (entry.op.toUInt32 == 0) = false := by
    have nonzero : entry.op.toUInt32 ≠ 0 := by
      intro zero
      rw [zero] at baseBool
      simp at baseBool
    simp [nonzero]
  have shiftRun : Zlib.Inffast.shr64 l.hold count.toUInt64 h =
      .ok (l.hold >>> count.toUInt64, h) := by
    apply Zlib.Inffast.Proofs.shr64_ok
    rw [UInt32.toNat_toUInt64]
    exact countSmall
  have runEq : C.run (Zlib.Inffast.dolen c l) h =
      C.run (Zlib.Inffast.Proofs.dolenLen c baseLocal) h := by
    change (Zlib.Inffast.dolen c l) h =
      (Zlib.Inffast.Proofs.dolenLen c baseLocal) h
    rw [Zlib.Inffast.Proofs.dolen_eq_len]
    rw [bind_ok load, bind_ok shiftRun, bind_ok load]
    simp only [notLiteral, baseBool, Bool.false_eq_true, ite_false, ite_true]
    rw [bind_ok load]
  exact ⟨basePacket, codeBuffers, codeStream,
    by simpa only [baseLocal, afterCode, firstLocal, slowCode, count]
      using runEq⟩

#print axioms FastInputPacket.dolen_base_source_prefix
end Zlib.Inflate.Proofs

