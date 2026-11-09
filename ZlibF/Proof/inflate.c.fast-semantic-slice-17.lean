import ZlibF.Proof.«inflate.c.fast-semantic-slice-16»
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

/-- The actual optional two-byte refill preserves the independent input
stream and then executes the distance match token suffix. -/
theorem FastInputPacket.dolenRefill_three_byte_valid_token_view
    {h : Heap} {slow : IL}
    {first second third : UInt8} {tail : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow (first :: second :: third :: tail) l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow (first :: second :: third :: tail))
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff rootWidth tableUsed : Nat} {D : List Nat}
    (dcodePtr : c.dcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : DistTableSafe codes baseOff rootWidth)
    (meaning : DecodeTableInvariant.Inv DISTS codes baseOff rootWidth tableUsed D)
    (flags : FastTableFlags.QueryCompatible DISTS codes baseOff rootWidth)
    (mask : c.dmask.toUInt64.toNat = 2 ^ rootWidth - 1)
    (bitsBound : slow.bits.toNat ≤ 30)
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
    (distanceSource : r2 = stream slow (first :: second :: third :: tail))
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
      used ≤ 4 ∧ used ≤ (first :: second :: third :: tail).length ∧
      C.run (Zlib.Inffast.Proofs.dolenRefill c l) h = .ok (result, after) ∧
      result.againD = false ∧ result.out = .ref dest (j + l.len.toNat) ∧
      result.broke = l.broke ∧ result.againL = l.againL ∧
      FastInputPacket after slowFinal ((first :: second :: third :: tail).drop used) result ∧
      stream slowFinal ((first :: second :: third :: tail).drop used) = rest ∧
      Space.get after dest = some array ∧ array.size = output.size ∧
      Space.ro after dest = false ∧
      ZlibF.Math.LZ77Copy.writtenBytes array (j + l.len.toNat)
        ((j - bg) + l.len.toNat) =
        copyBack dict (distBases.getD distanceSymbol 0 + distanceExtra)
          l.len.toNat history ∧
      Token.Step L D dict history input rest
        (ZlibF.Math.LZ77Copy.writtenBytes array (j + l.len.toNat)
          ((j - bg) + l.len.toNat)) false := by
  by_cases needsPull : l.bits < 15
  · have small0 : slow.bits.toNat ≤ 22 := by
      have bitsSmall : slow.bits.toNat < 15 := by
        rw [← packet.bits]
        simpa using UInt32.lt_iff_toNat_lt.mp needsPull
      omega
    obtain ⟨next1, fast1, slow1, pull1, _, slow1Eq, fast1Eq,
      packet1, _, buffers1, stream1⟩ :=
      packet.pull_default_state invariant buffers small0
    have small1 : slow1.bits.toNat ≤ 22 := by
      rw [slow1Eq]
      change (slow.bits + 8).toNat ≤ 22
      rw [u32_add8 slow.bits (by omega)]
      have bitsSmall : slow.bits.toNat < 15 := by
        rw [← packet.bits]
        simpa using UInt32.lt_iff_toNat_lt.mp needsPull
      omega
    obtain ⟨next2, fast2, slow2, pull2, _, slow2Eq, fast2Eq,
      packet2, _, buffers2, stream2⟩ :=
      packet1.pull_default_state invariant buffers1 small1
    have held2 : 15 ≤ slow2.bits.toNat := by
      rw [slow2Eq, slow1Eq]
      change ((slow.bits + 8) + 8).toNat ≥ 15
      rw [u32_add8 (slow.bits + 8) (by
          have bound : (slow.bits + 8).toNat ≤ 22 := by
            simpa only [slow1Eq, pulled] using small1
          omega), u32_add8 slow.bits (by omega)]
      omega
    have left2 : slow2.left ≠ 0 := by
      simpa only [slow2Eq, slow1Eq, pulled] using left
    have avail2 : 258 ≤ slow2.left.toNat := by
      simpa only [slow2Eq, slow1Eq, pulled] using avail
    have length2 : 3 ≤ fast2.len.toNat ∧ fast2.len.toNat ≤ 258 := by
      simpa only [fast2Eq, fast1Eq, Zlib.Inffast.Proofs.pullL] using length
    have out2 : fast2.out = .ref dest j := by
      simpa only [fast2Eq, fast1Eq, Zlib.Inffast.Proofs.pullL] using outPtr
    have put2 : slow2.put = .ref dest oo := by
      simpa only [slow2Eq, slow1Eq, pulled] using outputPtr
    have end2 : c.end_ = .ref dest (oo + slow2.left.toNat - 257) := by
      simpa only [slow2Eq, slow1Eq, pulled] using endPtr
    have size2 : oo + slow2.left.toNat ≤ output.size := by
      simpa only [slow2Eq, slow1Eq, pulled] using outputSize
    have guard2 : C.run (Ptr.lt fast2.out c.end_) h = .ok (true, h) := by
      simpa only [fast2Eq, fast1Eq, Zlib.Inffast.Proofs.pullL] using guard
    have source2 : r2 = stream slow2 (third :: tail) := by
      rw [stream2, stream1]
      exact distanceSource
    have len2 : fast2.len.toNat = lengthBases.getD (symbol - 257) 0 + lengthExtra := by
      simpa only [fast2Eq, fast1Eq, Zlib.Inffast.Proofs.pullL] using lengthValue
    obtain ⟨usedD, result, after, array, slowFinal, usedTwo, usedLength,
      distRun, againD, out, broke, againL, packetFinal, source,
      get, size, ro, bytes, token⟩ :=
      packet2.dolenDist_valid_token_view invariant buffers2
        dcodePtr codesGet safe meaning flags mask held2 left2 avail2 length2
        out2 put2 begPtr end2 outputGet outputWrite size2 current beginLe span
        guard2 whaveBound wnextBound wsizeBound windowView
        lengthCode lengthSymbolMin lengthSymbolMax lengthBits source2
        distanceCode distanceSymbolBound distanceBits len2
        dictionary dictCount written historyCount backBound
    have run : C.run (Zlib.Inffast.Proofs.dolenRefill c l) h = .ok (result, after) := by
      unfold Zlib.Inffast.Proofs.dolenRefill
      simp only [needsPull, ite_true]
      change (Zlib.Inffast.pull l >>= fun q =>
        Zlib.Inffast.pull q >>= fun q' => Zlib.Inffast.Proofs.dolenDist c q') h =
        .ok (result, after)
      change (Zlib.Inffast.pull l) h = .ok (fast1, h) at pull1
      change (Zlib.Inffast.pull fast1) h = .ok (fast2, h) at pull2
      change (Zlib.Inffast.Proofs.dolenDist c fast2) h = .ok (result, after) at distRun
      simp only [bind_app, pull1, pull2, distRun]
    have suffix : (third :: tail).drop usedD =
        (first :: second :: third :: tail).drop (2 + usedD) := by
      calc
        (third :: tail).drop usedD =
            (List.drop 2 (first :: second :: third :: tail)).drop usedD := rfl
        _ = (first :: second :: third :: tail).drop (2 + usedD) := by
          rw [List.drop_drop]
    refine ⟨2 + usedD, result, after, array, slowFinal,
      by omega, (by simp only [List.length_cons] at usedLength ⊢; omega), run, againD, ?_, ?_, ?_,
      by simpa only [suffix] using packetFinal,
      by simpa only [suffix] using source,
      get, size, ro, ?_, ?_⟩
    · simpa only [fast2Eq, fast1Eq, Zlib.Inffast.Proofs.pullL] using out
    · simpa only [fast2Eq, fast1Eq, Zlib.Inffast.Proofs.pullL] using broke
    · simpa only [fast2Eq, fast1Eq, Zlib.Inffast.Proofs.pullL] using againL
    · simpa only [fast2Eq, fast1Eq, Zlib.Inffast.Proofs.pullL] using bytes
    · simpa only [fast2Eq, fast1Eq, Zlib.Inffast.Proofs.pullL] using token
  · have held : 15 ≤ slow.bits.toNat := by
      have h : ¬ l.bits.toNat < 15 := by
        intro less
        exact needsPull (UInt32.lt_iff_toNat_lt.mpr less)
      rw [packet.bits] at h
      omega
    obtain ⟨used, result, after, array, slowFinal, usedTwo, usedLength,
      distRun, againD, out, broke, againL, packetFinal, source,
      get, size, ro, bytes, token⟩ :=
      packet.dolenDist_valid_token_view invariant buffers
        dcodePtr codesGet safe meaning flags mask held left avail length
        outPtr outputPtr begPtr endPtr outputGet outputWrite outputSize current
        beginLe span guard whaveBound wnextBound wsizeBound windowView
        lengthCode lengthSymbolMin lengthSymbolMax lengthBits distanceSource
        distanceCode distanceSymbolBound distanceBits lengthValue
        dictionary dictCount written historyCount backBound
    have run : C.run (Zlib.Inffast.Proofs.dolenRefill c l) h = .ok (result, after) := by
      unfold Zlib.Inffast.Proofs.dolenRefill
      simp only [needsPull, ite_false]
      exact distRun
    exact ⟨used, result, after, array, slowFinal, by omega,
      usedLength, run, againD, out, broke, againL, packetFinal,
      source, get, size, ro, bytes, token⟩

#print axioms FastInputPacket.dolenRefill_three_byte_valid_token_view
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
open Zlib.Inftrees.Spec Zlib.Inftrees.Spec.DecodeSemantics
set_option autoImplicit false
set_option maxRecDepth 4096

/-- The actual length-extra arithmetic and bit drop transport the
independently read value into the valid distance-copy token suffix. -/
theorem FastInputPacket.dolenExt_three_byte_valid_token_view
    {h : Heap} {slow : IL}
    {first second third : UInt8} {tail : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow (first :: second :: third :: tail) l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow (first :: second :: third :: tail))
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
    (lengthInput : r1 = stream slow (first :: second :: third :: tail))
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
      used ≤ 4 ∧ used ≤ (first :: second :: third :: tail).length ∧
      C.run (Zlib.Inffast.Proofs.dolenExt c l) h = .ok (result, after) ∧
      result.againD = false ∧ result.out = .ref dest (j + (l.len.toNat + lengthExtra)) ∧
      result.broke = l.broke ∧ result.againL = l.againL ∧
      FastInputPacket after slowFinal ((first :: second :: third :: tail).drop used) result ∧
      stream slowFinal ((first :: second :: third :: tail).drop used) = rest ∧
      Space.get after dest = some array ∧ array.size = output.size ∧
      Space.ro after dest = false ∧
      ZlibF.Math.LZ77Copy.writtenBytes array (j + (l.len.toNat + lengthExtra))
        ((j - bg) + (l.len.toNat + lengthExtra)) =
        copyBack dict (distBases.getD distanceSymbol 0 + distanceExtra)
          (l.len.toNat + lengthExtra) history ∧
      Token.Step L D dict history input rest
        (ZlibF.Math.LZ77Copy.writtenBytes array (j + (l.len.toNat + lengthExtra))
          ((j - bg) + (l.len.toNat + lengthExtra))) false := by
  let raw := first :: second :: third :: tail
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
      (first :: second :: third :: tail) afterLen :=
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
      (first :: second :: third :: tail) fastDrop :=
    dropped.1
  have dropBuffers : DispatchBuffers h r slowDrop
      (first :: second :: third :: tail) :=
    dropped.2.1
  have dropStream : stream slowDrop
      (first :: second :: third :: tail) =
      (stream slow
        (first :: second :: third :: tail)).drop
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
    dropPacket.dolenRefill_three_byte_valid_token_view invariant dropBuffers
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

#print axioms FastInputPacket.dolenExt_three_byte_valid_token_view
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
open Zlib.Inftrees.Spec Zlib.Inftrees.Spec.DecodeSemantics
set_option autoImplicit false
set_option maxRecDepth 4096

/-- The actual length-extra selection, optional one-byte pull, and
distance suffix refine one independent match token on caller byte views. -/
theorem FastInputPacket.dolenLen_four_byte_valid_token_view
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
      used ≤ 5 ∧ used ≤ (first :: second :: third :: fourth :: tail).length ∧
      C.run (Zlib.Inffast.Proofs.dolenLen c l) h = .ok (result, after) ∧
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
      have input1 : r1 = stream slow1 (second :: third :: fourth :: tail) := by
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
        packet1.dolenExt_three_byte_valid_token_view invariant buffers1
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
      have tailEq : (second :: third :: fourth :: tail).drop usedExt =
          (first :: second :: third :: fourth :: tail).drop (1 + usedExt) := by
        calc
          (second :: third :: fourth :: tail).drop usedExt =
              ((first :: second :: third :: fourth :: tail).drop 1).drop usedExt := rfl
          _ = (first :: second :: third :: fourth :: tail).drop (1 + usedExt) := by
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
    have zeroRead : r2 = stream slow (first :: second :: third :: fourth :: tail) := by
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

#print axioms FastInputPacket.dolenLen_four_byte_valid_token_view
end Zlib.Inflate.Proofs

