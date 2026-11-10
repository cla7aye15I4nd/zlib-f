import ZlibF.Proof.«inflate.c.payload-linked-loop-cursor-stage-relinked»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
open Zlib.Inftrees.Spec Zlib.Inftrees.Spec.DecodeSemantics
set_option autoImplicit false
set_option maxRecDepth 4096

theorem FastInputPacket.dolenRefill_three_byte_valid_token_view_cursor
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
          ((j - bg) + l.len.toNat)) false ∧
      result.in_ = inputAdvance l.in_ used := by
  by_cases needsPull : l.bits < 15
  · have small0 : slow.bits.toNat ≤ 22 := by
      have bitsSmall : slow.bits.toNat < 15 := by
        rw [← packet.bits]
        simpa using UInt32.lt_iff_toNat_lt.mp needsPull
      omega
    obtain ⟨next1, fast1, slow1, pull1, next1Eq, slow1Eq, fast1Eq,
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
    obtain ⟨next2, fast2, slow2, pull2, next2Eq, slow2Eq, fast2Eq,
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
      get, size, ro, bytes, token, cursorD⟩ :=
      packet2.dolenDist_valid_token_view_cursor invariant buffers2
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
      get, size, ro, ?_, ?_, ?_⟩
    · simpa only [fast2Eq, fast1Eq, Zlib.Inffast.Proofs.pullL] using out
    · simpa only [fast2Eq, fast1Eq, Zlib.Inffast.Proofs.pullL] using broke
    · simpa only [fast2Eq, fast1Eq, Zlib.Inffast.Proofs.pullL] using againL
    · simpa only [fast2Eq, fast1Eq, Zlib.Inffast.Proofs.pullL] using bytes
    · simpa only [fast2Eq, fast1Eq, Zlib.Inffast.Proofs.pullL] using token
    · have cursor2 : fast2.in_ = inputAdvance l.in_ 2 := by
        rw [fast2Eq, fast1Eq]
        simp only [Zlib.Inffast.Proofs.pullL]
        rw [next2Eq, slow1Eq, next1Eq, ← packet.cursor]
        simp only [pulled, inputAdvance_add]
      rw [cursorD, cursor2, inputAdvance_add]
  · have held : 15 ≤ slow.bits.toNat := by
      have h : ¬ l.bits.toNat < 15 := by
        intro less
        exact needsPull (UInt32.lt_iff_toNat_lt.mpr less)
      rw [packet.bits] at h
      omega
    obtain ⟨used, result, after, array, slowFinal, usedTwo, usedLength,
      distRun, againD, out, broke, againL, packetFinal, source,
      get, size, ro, bytes, token, cursorD⟩ :=
      packet.dolenDist_valid_token_view_cursor invariant buffers
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
      source, get, size, ro, bytes, token, cursorD⟩

#print axioms FastInputPacket.dolenRefill_three_byte_valid_token_view_cursor
end Zlib.Inflate.Proofs
