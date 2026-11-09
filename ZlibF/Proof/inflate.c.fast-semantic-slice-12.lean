import ZlibF.Proof.«inflate.c.fast-semantic-slice-11»
set_option autoImplicit false

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
private theorem distance_value_bound_kernel : ∀ k, k < 30 →
    0 < distBases.getD k 0 ∧ distBases.getD k 0 + 2 ^ distExtras.getD k 0 ≤ 32769 := by
  decide +kernel

end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
/-- For a valid distance base, the actual `distCont` path consumes the same
extra bits as the independent decoder and executes the exact token copy.
This is a source-level same-run bridge through the translated suffix. -/
theorem FastInputPacket.distCont_valid_token_view_with_frame
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef}
    (packet : FastInputPacket h slow bs l)
    (buffers : DispatchBuffers h r slow bs)
    (extraBits : l.op.toNat ≤ slow.bits.toNat)
    (extraSmall : l.op.toNat < 32)
    (left : slow.left ≠ 0)
    (avail : 258 ≤ slow.left.toNat)
    (length : 3 ≤ l.len.toNat ∧ l.len.toNat ≤ 258)
    {dest : BRef} {output : Array UInt8} {oo bg j : Nat}
    (outPtr : l.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (begPtr : c.beg = .ref dest bg)
    (endPtr : c.end_ = .ref dest
      (oo + slow.left.toNat - 257))
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (current : oo ≤ j)
    (beginLe : bg ≤ j)
    (span : j - bg < 2 ^ 32)
    (guard : C.run (Ptr.lt l.out c.end_) h = .ok (true, h))
    (whaveBound : c.whave.toNat ≤ c.wsize.toNat)
    (wnextBound : c.wnext.toNat ≤ c.wsize.toNat)
    (wsizeBound : c.wsize.toNat ≤ 32768)
    {saved : Array UInt8} {woff : Nat}
    (windowData :
      let distanceLocal : Zlib.Inffast.L := { l with
        dist := l.dist + (l.hold.toUInt32 &&&
          (((1 : UInt32) <<< l.op) - 1)) }
      let afterBits : Zlib.Inffast.L := { distanceLocal with
        hold := distanceLocal.hold >>> l.op.toUInt64,
        bits := distanceLocal.bits - l.op }
      afterBits.dist >
        { afterBits with op :=
          (Int64.ofInt ((j - bg : Nat) : Int)).toUInt64.toUInt32 }.op →
      ∃ window,
        window ≠ dest ∧ c.window = .ref window woff ∧
        Space.get h window = some saved ∧
        woff + c.wsize.toNat ≤ saved.size)
    {L D : List Nat} {dict history : List UInt8}
    {input r1 r2 r3 rest : List Bool}
    {symbol distanceSymbol lengthExtra distanceExtra : Nat}
    (lengthCode : decodeSym L input = some (symbol, r1))
    (lengthSymbolMin : 257 ≤ symbol)
    (lengthSymbolMax : symbol ≤ 285)
    (lengthBits : readBits
      (lengthExtras.getD (symbol - 257) 0) r1 =
      some (lengthExtra, r2))
    (distanceCode : decodeSym D r2 = some (distanceSymbol, r3))
    (distanceSymbolBound : distanceSymbol ≤ 29)
    (distanceWidth : l.op.toNat =
      distExtras.getD distanceSymbol 0)
    (distanceInput : r3 = stream slow bs)
    (distanceBits : readBits
      (distExtras.getD distanceSymbol 0) r3 =
      some (distanceExtra, rest))
    (lengthValue : l.len.toNat =
      lengthBases.getD (symbol - 257) 0 + lengthExtra)
    (distanceBase : l.dist.toNat =
      distBases.getD distanceSymbol 0)
    (distanceNoWrap : l.dist.toNat + distanceExtra < 2 ^ 32)
    (distancePositive : 0 < l.dist.toNat + distanceExtra)
    (dictionary : Zlib.Inffast.Spec.MatchHistory.saved saved
      c.wsize.toNat c.wnext.toNat c.whave.toNat woff = dict)
    (dictCount : dict.length = c.whave.toNat)
    (written : ZlibF.Math.LZ77Copy.writtenBytes output j
      (j - bg) = history)
    (historyCount : history.length = j - bg)
    (backBound : l.dist.toNat + distanceExtra ≤
      (dict ++ history).length) :
    ∃ result after array slowNext,
      C.run (Zlib.Inffast.Proofs.distCont c l) h =
        .ok (result, after) ∧
      FastInputPacket after slowNext bs result ∧
      stream slowNext bs = rest ∧
      result.out = .ref dest (j + l.len.toNat) ∧
      result.broke = l.broke ∧ result.againD = l.againD ∧ result.againL = l.againL ∧
      Space.get after dest = some array ∧ array.size = output.size ∧ Space.ro after dest = false ∧
      ZlibF.Math.LZ77Copy.writtenBytes array
        (j + l.len.toNat) ((j - bg) + l.len.toNat) =
        ZlibF.Spec.copyBack dict
          (l.dist.toNat + distanceExtra) l.len.toNat history ∧
      ZlibF.Spec.Token.Step L D dict history input rest
        (ZlibF.Math.LZ77Copy.writtenBytes array
          (j + l.len.toNat) ((j - bg) + l.len.toNat)) false := by
  let extra := l.hold.toNat % 2 ^ l.op.toNat
  have read := readBits_held_stream slow bs l.op.toNat extraBits
  have decodedExtra : distanceExtra = extra := by
    rw [← distanceWidth, distanceInput] at distanceBits
    rw [read] at distanceBits
    simpa only [Prod.fst, extra, ← packet.hold] using
      (congrArg Prod.fst (Option.some.inj distanceBits)).symm
  let distanceLocal : Zlib.Inffast.L := { l with
    dist := l.dist + (l.hold.toUInt32 &&&
      (((1 : UInt32) <<< l.op) - 1)) }
  let slowNext : IL := { slow with
    hold := slow.hold >>> l.op.toUInt64,
    bits := slow.bits - l.op }
  let afterBits : Zlib.Inffast.L := { distanceLocal with
    hold := distanceLocal.hold >>> l.op.toUInt64,
    bits := distanceLocal.bits - l.op }
  have extraEq : (l.hold.toUInt32 &&&
      (((1 : UInt32) <<< l.op) - 1)).toNat = extra :=
    Zlib.Inffast.Proofs.hold_low32 extraSmall
  have actualDistance : afterBits.dist.toNat =
      distBases.getD distanceSymbol 0 + distanceExtra := by
    dsimp only [afterBits, distanceLocal]
    rw [UInt32.toNat_add, extraEq, ← decodedExtra,
      Nat.mod_eq_of_lt distanceNoWrap, distanceBase]
  have actualPositive : 0 < afterBits.dist.toNat := by
    rw [actualDistance, ← distanceBase]
    exact distancePositive
  have actualAvailable : afterBits.dist.toNat ≤
      c.whave.toNat + (j - bg) := by
    rw [actualDistance, ← distanceBase]
    rw [List.length_append, dictCount, historyCount] at backBound
    exact backBound
  have distancePacket : FastInputPacket h slow bs distanceLocal :=
    ⟨packet.source, packet.cursor, packet.hold, packet.bits⟩
  have dropped := distancePacket.drop_bits_default_state
    buffers l.op extraBits (by omega)
  have nextPacket : FastInputPacket h slowNext bs afterBits := dropped.1
  have nextBuffers : DispatchBuffers h r slowNext bs := dropped.2.1
  have sourceDrop : stream slowNext bs =
      (stream slow bs).drop l.op.toNat := dropped.2.2.1
  have sourceNext : stream slowNext bs = rest := by
    rw [sourceDrop, ← distanceInput]
    have nextRead : readBits l.op.toNat r3 =
        some (distanceExtra, rest) := by
      simpa only [distanceWidth] using distanceBits
    rw [distanceInput, read] at nextRead
    rw [distanceInput]
    simpa only [Prod.snd] using
      congrArg Prod.snd (Option.some.inj nextRead)
  have windowDataNext : afterBits.dist >
      { afterBits with op :=
        (Int64.ofInt ((j - bg : Nat) : Int)).toUInt64.toUInt32 }.op →
      ∃ window,
        window ≠ dest ∧ c.window = .ref window woff ∧
        Space.get h window = some saved ∧
        woff + c.wsize.toNat ≤ saved.size := by
    simpa only [afterBits, distanceLocal] using windowData
  have backBoundCopy : afterBits.dist.toNat ≤
      (dict ++ history).length := by
    rw [actualDistance, ← distanceBase]
    exact backBound
  obtain ⟨result, after, array, copyRun, finalPacket,
    out, broke, againD, againL, get, size, ro, bytes, _, token⟩ :=
    nextPacket.copy_after_diff_valid_token_view_with_frame
      nextBuffers.separate left avail length actualPositive
      outPtr outputPtr begPtr endPtr outputGet outputWrite
      outputSize current beginLe span guard actualAvailable
      whaveBound wnextBound wsizeBound windowDataNext
      sourceNext lengthCode lengthSymbolMin lengthSymbolMax
      lengthBits distanceCode distanceSymbolBound distanceBits
      lengthValue actualDistance dictionary written backBoundCopy
  have shlRun : C.run (Zlib.Inffast.shl32 1 l.op) h =
      .ok ((1 : UInt32) <<< l.op, h) :=
    Zlib.Inffast.Proofs.shl32_ok extraSmall
  have shrRun : C.run (Zlib.Inffast.shr64 l.hold l.op.toUInt64) h =
      .ok (l.hold >>> l.op.toUInt64, h) := by
    apply Zlib.Inffast.Proofs.shr64_ok
    rw [UInt32.toNat_toUInt64]
    omega
  have run : C.run (Zlib.Inffast.Proofs.distCont c l) h =
      .ok (result, after) := by
    change (Zlib.Inffast.Proofs.distCont c l) h =
      .ok (result, after)
    change Zlib.Inffast.shl32 1 l.op h =
      .ok ((1 : UInt32) <<< l.op, h) at shlRun
    change Zlib.Inffast.shr64 l.hold l.op.toUInt64 h =
      .ok (l.hold >>> l.op.toUInt64, h) at shrRun
    unfold Zlib.Inffast.Proofs.distCont
    rw [bind_ok shlRun]
    rw [bind_ok shrRun]
    simpa only [C.run, afterBits, distanceLocal] using copyRun
  refine ⟨result, after, array, slowNext, run,
    finalPacket, sourceNext, out, broke, againD, againL, get, size, ro, ?_, ?_⟩
  · simpa only [actualDistance, ← distanceBase] using bytes
  · exact token


#print axioms FastInputPacket.distCont_valid_token_view_with_frame
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
open Zlib.Inftrees.Spec Zlib.Inftrees.Spec.DecodeSemantics
/-- The actual selected distance cell, including all guarded refills, is
connected to an independent extra-bit read. The caller supplies constructor
meaning and available input bits, never an assumed callee execution. -/
theorem FastInputPacket.dodist_selected_base_semantic_prefix_with_frame
    {h : Heap} {slow : IL} {bs : List UInt8} {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow bs l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    {codeRef : CodeRef} {codes : Array Code} {index : Nat}
    (herePtr : l.here = .ref codeRef index)
    (codesGet : Space.get h codeRef = some codes) (codeIndex : index < codes.size)
    (codeBits : codes[index].bits.toNat ≤ slow.bits.toNat)
    (codeWidth : codes[index].bits.toNat ≤ 15)
    (base : (codes[index].op.toUInt32 &&& 16 != 0) = true)
    {symbol : Nat} (valid : symbol ≤ 29)
    (meaning : Zlib.Inftrees.Spec.DecodeSemantics.SymbolEntry DISTS symbol codes[index])
    (capacity : distExtras.getD symbol 0 ≤
      ((stream slow bs).drop codes[index].bits.toNat).length) :
    ∃ used slowNext fastNext extra rest,
      used ≤ 2 ∧ used ≤ bs.length ∧
      C.run (Zlib.Inffast.dodist c l) h =
        C.run (Zlib.Inffast.Proofs.distCont c fastNext) h ∧
      FastInputPacket h slowNext (bs.drop used) fastNext ∧
      DispatchBuffers h r slowNext (bs.drop used) ∧
      slowNext.left = slow.left ∧ slowNext.put = slow.put ∧ fastNext.againD = false ∧ fastNext.broke = l.broke ∧ fastNext.againL = l.againL ∧
      stream slowNext (bs.drop used) =
        (stream slow bs).drop codes[index].bits.toNat ∧
      fastNext.op.toNat = distExtras.getD symbol 0 ∧
      fastNext.op.toNat ≤ slowNext.bits.toNat ∧
      fastNext.dist.toNat = distBases.getD symbol 0 ∧
      fastNext.len = l.len ∧ fastNext.out = l.out ∧
      readBits (distExtras.getD symbol 0)
        ((stream slow bs).drop codes[index].bits.toNat) = some (extra, rest) ∧
      extra = fastNext.hold.toNat % 2 ^ fastNext.op.toNat ∧
      rest = (stream slowNext (bs.drop used)).drop fastNext.op.toNat ∧
      0 < fastNext.dist.toNat + extra ∧ fastNext.dist.toNat + extra ≤ 32768 ∧
      (fastNext.dist + (fastNext.hold.toUInt32 &&&
        (((1 : UInt32) <<< fastNext.op) - 1))).toNat = fastNext.dist.toNat + extra := by
  let entry : Code := codes[index]
  let count := entry.bits.toUInt32
  let slowCode : IL := { slow with hold := slow.hold >>> count.toUInt64, bits := slow.bits - count }
  let baseLocal : Zlib.Inffast.L := { l with againD := false, hold := l.hold >>> count.toUInt64, bits := l.bits - count, op := entry.op.toUInt32 &&& 15, dist := entry.val.toUInt32 }
  obtain ⟨sourceRun, codePacket, codeBuffers, sourceDrop⟩ :=
    packet.dodist_base_source_prefix buffers herePtr codesGet codeIndex codeBits codeWidth base
  have fields := distance_base_symbol_fields valid meaning
  have baseWidth : baseLocal.op.toNat = distExtras.getD symbol 0 := fields.1
  have widthBound : baseLocal.op.toNat ≤ 13 := fields.2.1
  have baseValue : baseLocal.dist.toNat = distBases.getD symbol 0 := fields.2.2
  have capacity0 : baseLocal.op.toNat ≤ slowCode.bits.toNat + 8 * bs.length := by
    rw [← sourceDrop] at capacity
    simpa only [← baseWidth, stream, List.length_append, natBits_length, bytesBits_length] using capacity
  obtain ⟨used, slowNext, fastNext, usedTwo, usedLength, refillRun, nextPacket,
    nextBuffers, sameStream, extraFits, fastEq, slowEq⟩ :=
    codePacket.dodistBase_distCont_prefix invariant codeBuffers widthBound capacity0
  have leftEq : slowNext.left = slow.left := by rw [slowEq]
  have putEq : slowNext.put = slow.put := by rw [slowEq]
  have againD : fastNext.againD = false := by rw [fastEq]
  have brokeEq : fastNext.broke = l.broke := by rw [fastEq]
  have againLEq : fastNext.againL = l.againL := by rw [fastEq]
  have opEq : fastNext.op = baseLocal.op := by rw [fastEq]
  have distEq : fastNext.dist = baseLocal.dist := by rw [fastEq]
  have lenEq : fastNext.len = l.len := by rw [fastEq]
  have outEq : fastNext.out = l.out := by rw [fastEq]
  have width : fastNext.op.toNat = distExtras.getD symbol 0 := by rw [opEq]; exact baseWidth
  have value : fastNext.dist.toNat = distBases.getD symbol 0 := by rw [distEq]; exact baseValue
  let extra := fastNext.hold.toNat % 2 ^ fastNext.op.toNat
  let rest := (stream slowNext (bs.drop used)).drop fastNext.op.toNat
  have read := readBits_held_stream slowNext (bs.drop used) fastNext.op.toNat extraFits
  have actualRead : readBits (distExtras.getD symbol 0)
      ((stream slow bs).drop entry.bits.toNat) = some (extra, rest) := by
    rw [← sourceDrop, ← sameStream, ← width]
    simpa only [extra, rest, nextPacket.hold] using read
  have smallExtra : extra < 2 ^ distExtras.getD symbol 0 := by
    dsimp only [extra]
    rw [width]
    exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have validValue := distance_value_bound_kernel symbol (by omega)
  have positive : 0 < fastNext.dist.toNat + extra := by rw [value]; omega
  have distanceBound : fastNext.dist.toNat + extra ≤ 32768 := by rw [value]; omega
  have opSmall : fastNext.op.toNat < 32 := by rw [opEq]; omega
  have low := Zlib.Inffast.Proofs.hold_low32 (x := fastNext.hold) opSmall
  have noWrap :
      (fastNext.dist + (fastNext.hold.toUInt32 &&&
        (((1 : UInt32) <<< fastNext.op) - 1))).toNat = fastNext.dist.toNat + extra := by
    rw [UInt32.toNat_add, low, Nat.mod_eq_of_lt (by omega)]
  exact ⟨used, slowNext, fastNext, extra, rest, usedTwo, usedLength,
    sourceRun.trans refillRun, nextPacket, nextBuffers, leftEq, putEq, againD, brokeEq, againLEq, sameStream.trans sourceDrop,
    width, extraFits, value, lenEq, outEq, actualRead, rfl, rfl, positive, distanceBound, noWrap⟩



#print axioms FastInputPacket.dodist_selected_base_semantic_prefix_with_frame
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
open Zlib.Inftrees.Spec Zlib.Inftrees.Spec.DecodeSemantics
/-- A selected real root distance base both decodes its independent symbol
and executes the translated load/drop/refill prefix on the same heap. The
capacity condition is the actual extra width, including zero extra bits. -/
theorem FastInputPacket.dodist_root_base_semantic_prefix_with_frame
    {h : Heap} {slow : IL} {bs : List UInt8} {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow bs l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    {codeRef : CodeRef} {codes : Array Code} {baseOff rootWidth used : Nat} {D : List Nat}
    (herePtr : l.here = .ref codeRef (baseOff + l.hold.toNat % 2 ^ rootWidth))
    (codesGet : Space.get h codeRef = some codes)
    (meaning : DecodeTableInvariant.Inv DISTS codes baseOff rootWidth used D)
    (flags : FastTableFlags.QueryCompatible DISTS codes baseOff rootWidth)
    (held : 15 ≤ slow.bits.toNat)
    (base : ((codes.getD (baseOff + l.hold.toNat % 2 ^ rootWidth) default).op.toUInt32 &&& 16 != 0) = true)
    (capacity :
      let entry := codes.getD (baseOff + l.hold.toNat % 2 ^ rootWidth) default
      (entry.op.toUInt32 &&& 15).toNat ≤ ((stream slow bs).drop entry.bits.toNat).length) :
    let entry := codes.getD (baseOff + l.hold.toNat % 2 ^ rootWidth) default
    ∃ symbol consumed slowNext fastNext extra rest,
      symbol ≤ 29 ∧ SymbolEntry DISTS symbol entry ∧
      consumed ≤ 2 ∧ consumed ≤ bs.length ∧
      C.run (Zlib.Inffast.dodist c l) h = C.run (Zlib.Inffast.Proofs.distCont c fastNext) h ∧
      FastInputPacket h slowNext (bs.drop consumed) fastNext ∧
      DispatchBuffers h r slowNext (bs.drop consumed) ∧
      slowNext.left = slow.left ∧ slowNext.put = slow.put ∧ fastNext.againD = false ∧ fastNext.broke = l.broke ∧ fastNext.againL = l.againL ∧
      decodeSym D (stream slow bs) = some (symbol, stream slowNext (bs.drop consumed)) ∧
      fastNext.op.toNat = distExtras.getD symbol 0 ∧
      fastNext.op.toNat ≤ slowNext.bits.toNat ∧ fastNext.dist.toNat = distBases.getD symbol 0 ∧
      fastNext.len = l.len ∧ fastNext.out = l.out ∧
      readBits (distExtras.getD symbol 0) (stream slowNext (bs.drop consumed)) = some (extra, rest) ∧
      extra = fastNext.hold.toNat % 2 ^ fastNext.op.toNat ∧
      rest = (stream slowNext (bs.drop consumed)).drop fastNext.op.toNat ∧
      0 < fastNext.dist.toNat + extra ∧ fastNext.dist.toNat + extra ≤ 32768 ∧
      (fastNext.dist + (fastNext.hold.toUInt32 &&&
        (((1 : UInt32) <<< fastNext.op) - 1))).toNat = fastNext.dist.toNat + extra := by
  let index := baseOff + l.hold.toNat % 2 ^ rootWidth
  let entry := codes.getD index default
  obtain ⟨bound, positive, width, symbol, valid, symbolMeaning, _, _, decoded, _extended⟩ :=
    packet.distance_root_base_meaning meaning flags held base
  have boundI : index < codes.size := bound
  have entryEq : entry = codes[index] := by simp [entry, Array.getD_eq_getD_getElem?, boundI]
  change entry.bits.toNat ≤ 15 at width
  rw [entryEq] at width
  have actualBase : (codes[index].op.toUInt32 &&& 16 != 0) = true := by
    simpa only [← entryEq] using base
  have actualMeaning : SymbolEntry DISTS symbol codes[index] := by
    simpa only [← entryEq] using symbolMeaning
  have actualCapacity : distExtras.getD symbol 0 ≤ ((stream slow bs).drop codes[index].bits.toNat).length := by
    have fields := distance_base_symbol_fields valid actualMeaning
    rw [← fields.1]
    simpa only [← entryEq] using capacity
  obtain ⟨consumed, slowNext, fastNext, extra, rest, consumedTwo, consumedLength,
    run, nextPacket, nextBuffers, leftEq, putEq, noAgain, brokeEq, againLEq, source, extraWidth, extraFits, value, length, out,
    read, extraValue, remainder, positiveValue, maxValue, actualValue⟩ :=
    packet.dodist_selected_base_semantic_prefix_with_frame invariant buffers herePtr codesGet bound
      (Nat.le_trans width held) width actualBase valid actualMeaning actualCapacity
  have decoder : decodeSym D (stream slow bs) = some (symbol, stream slowNext (bs.drop consumed)) := by
    rw [source, ← entryEq]
    exact decoded
  have extraRead : readBits (distExtras.getD symbol 0) (stream slowNext (bs.drop consumed)) = some (extra, rest) := by
    rw [source]
    exact read
  exact ⟨symbol, consumed, slowNext, fastNext, extra, rest, valid, symbolMeaning,
    consumedTwo, consumedLength, run, nextPacket, nextBuffers, leftEq, putEq, noAgain, brokeEq, againLEq, decoder, extraWidth,
    extraFits, value, length, out, extraRead, extraValue, remainder, positiveValue, maxValue, actualValue⟩



#print axioms FastInputPacket.dodist_root_base_semantic_prefix_with_frame
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
open Zlib.Inftrees.Spec Zlib.Inftrees.Spec.DecodeSemantics
/-- Following the actual root link and its actual base leaf produces one
independently decoded distance and its exact extra bits. Both translated
`dodist` calls and the guarded refills are from the same heap and input. -/
theorem FastInputPacket.dodist_linked_base_semantic_prefix_with_frame
    {h : Heap} {slow : IL} {bs : List UInt8} {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow bs l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    {codeRef : CodeRef} {codes : Array Code} {baseOff rootWidth used : Nat} {D : List Nat}
    (herePtr : l.here = .ref codeRef (baseOff + l.hold.toNat % 2 ^ rootWidth))
    (dcodePtr : c.dcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (meaning : DecodeTableInvariant.Inv DISTS codes baseOff rootWidth used D)
    (flags : FastTableFlags.QueryCompatible DISTS codes baseOff rootWidth)
    (held : 15 ≤ slow.bits.toNat)
    (link : Subtable.IsLink DISTS
      (codes.getD (baseOff + l.hold.toNat % 2 ^ rootWidth) default) = true)
    (base :
      let first := codes.getD (baseOff + l.hold.toNat % 2 ^ rootWidth) default
      let slice := (l.hold >>> first.bits.toUInt32.toUInt64).toNat % 2 ^ first.op.toNat
      ((codes.getD (baseOff + first.val.toNat + slice) default).op.toUInt32 &&& 16 != 0) = true)
    (capacity :
      let first := codes.getD (baseOff + l.hold.toNat % 2 ^ rootWidth) default
      let slice := (l.hold >>> first.bits.toUInt32.toUInt64).toNat % 2 ^ first.op.toNat
      let entry := codes.getD (baseOff + first.val.toNat + slice) default
      (entry.op.toUInt32 &&& 15).toNat ≤
        ((stream slow bs).drop (first.bits.toNat + entry.bits.toNat)).length) :
    let first := codes.getD (baseOff + l.hold.toNat % 2 ^ rootWidth) default
    let slice := (l.hold >>> first.bits.toUInt32.toUInt64).toNat % 2 ^ first.op.toNat
    let entry := codes.getD (baseOff + first.val.toNat + slice) default
    ∃ symbol consumed slowNext fastNext extra rest linked,
      symbol ≤ 29 ∧ SymbolEntry DISTS symbol entry ∧
      consumed ≤ 2 ∧ consumed ≤ bs.length ∧
      C.run (Zlib.Inffast.dodist c l) h = .ok (linked, h) ∧ linked.againD = true ∧
      C.run (Zlib.Inffast.dodist c linked) h = C.run (Zlib.Inffast.Proofs.distCont c fastNext) h ∧
      FastInputPacket h slowNext (bs.drop consumed) fastNext ∧
      DispatchBuffers h r slowNext (bs.drop consumed) ∧
      slowNext.left = slow.left ∧ slowNext.put = slow.put ∧ fastNext.againD = false ∧ fastNext.broke = l.broke ∧ fastNext.againL = l.againL ∧
      decodeSym D (stream slow bs) = some (symbol, stream slowNext (bs.drop consumed)) ∧
      fastNext.op.toNat = distExtras.getD symbol 0 ∧
      fastNext.op.toNat ≤ slowNext.bits.toNat ∧ fastNext.dist.toNat = distBases.getD symbol 0 ∧
      fastNext.len = l.len ∧ fastNext.out = l.out ∧
      readBits (distExtras.getD symbol 0) (stream slowNext (bs.drop consumed)) = some (extra, rest) ∧
      extra = fastNext.hold.toNat % 2 ^ fastNext.op.toNat ∧
      rest = (stream slowNext (bs.drop consumed)).drop fastNext.op.toNat ∧
      0 < fastNext.dist.toNat + extra ∧ fastNext.dist.toNat + extra ≤ 32768 ∧
      (fastNext.dist + (fastNext.hold.toUInt32 &&&
        (((1 : UInt32) <<< fastNext.op) - 1))).toNat = fastNext.dist.toNat + extra := by
  let index := baseOff + l.hold.toNat % 2 ^ rootWidth
  let first := codes.getD index default
  let slice := (l.hold >>> first.bits.toUInt32.toUInt64).toNat % 2 ^ first.op.toNat
  let target := baseOff + first.val.toNat + slice
  let entry := codes.getD target default
  obtain ⟨rootBound, leafBound, bitsRoot, leafPositive, totalBits,
    symbol, valid, symbolMeaning, decoded, _extended⟩ :=
    packet.distance_linked_base_meaning meaning flags held link base
  have rootBoundI : index < codes.size := rootBound
  have leafBoundI : target < codes.size := leafBound
  have firstEq : first = codes[index] := by simp [first, Array.getD_eq_getD_getElem?, rootBoundI]
  have entryEq : entry = codes[target] := by simp [entry, Array.getD_eq_getD_getElem?, leafBoundI]
  have idxLt : l.hold.toNat % 2 ^ rootWidth < 2 ^ rootWidth := Nat.mod_lt _ (Nat.two_pow_pos _)
  have firstCell : codes[baseOff + l.hold.toNat % 2 ^ rootWidth]? = some first := by
    simp only [firstEq]
    exact Array.getElem?_eq_getElem rootBoundI
  obtain ⟨rootBits, subSafe⟩ := meaning.subtables _ first idxLt firstCell link
  have opMask : first.op &&& 0xf0 = 0 := by
    have bool : (first.op &&& 0xf0 == 0) = true := by
      simpa only [Subtable.IsLink, show DISTS ≠ LENS by decide, ite_false] using link
    exact beq_iff_eq.mp bool
  have noBase : first.op &&& 16 = 0 := by
    have mask := congrArg (fun x : UInt8 => x &&& 16) opMask
    rw [UInt8.and_assoc] at mask
    exact mask
  have noBad : first.op &&& 64 = 0 := by
    have mask := congrArg (fun x : UInt8 => x &&& 64) opMask
    rw [UInt8.and_assoc] at mask
    exact mask
  have notBase : (codes[index].op.toUInt32 &&& 16 != 0) = false := by
    rw [← firstEq, Zlib.Inffast.Proofs.mask16, noBase]
    rfl
  have linkBool : (codes[index].op.toUInt32 &&& 64 == 0) = true := by
    rw [← firstEq, Zlib.Inffast.Proofs.mask64, noBad]
    rfl
  have firstWidth : codes[index].bits.toNat ≤ 15 := by
    rw [← firstEq, rootBits]
    exact meaning.rootTable.2.1
  have opWidth : codes[index].op.toNat ≤ 15 := by
    rw [← firstEq]
    have := subSafe.2.2.1
    omega
  have storage : baseOff + codes[index].val.toNat + 2 ^ codes[index].op.toNat ≤ codes.size := by
    rw [← firstEq]
    exact subSafe.2.2.2.1
  obtain ⟨linked, actualSlice, firstRun, sliceEq, _, here, againD, brokeRoot, out, length,
    linkPacket, _, linkBuffers, sourceLink⟩ :=
    packet.dodist_link_default_state_exact_with_slice invariant buffers herePtr dcodePtr
      codesGet rootBoundI (Nat.le_trans firstWidth held) firstWidth notBase linkBool opWidth storage
  let slowLink : IL := { slow with hold := slow.hold >>> codes[index].bits.toUInt32.toUInt64, bits := slow.bits - codes[index].bits.toUInt32 }
  have actualSliceEq : actualSlice = slice := by
    simpa only [slice, firstEq] using sliceEq
  have actualHere : linked.here = .ref codeRef target := by
    simpa only [target, firstEq, actualSliceEq] using here
  have actualBase : (codes[target].op.toUInt32 &&& 16 != 0) = true := by
    simpa only [← entryEq] using base
  have actualMeaning : SymbolEntry DISTS symbol codes[target] := by
    simpa only [← entryEq] using symbolMeaning
  have leafWidth : codes[target].bits.toNat ≤ 15 := by
    change first.bits.toNat + entry.bits.toNat ≤ 15 at totalBits
    rw [entryEq] at totalBits
    omega
  have linkBits : slowLink.bits.toNat = slow.bits.toNat - first.bits.toNat := by
    change (slow.bits - codes[index].bits.toUInt32).toNat = slow.bits.toNat - first.bits.toNat
    rw [Zlib.Inffast.Proofs.u32_toNat_sub (by rw [Zlib.Inffast.Proofs.toNat32]; omega), Zlib.Inffast.Proofs.toNat32, ← firstEq]
  have leafFits : codes[target].bits.toNat ≤ slowLink.bits.toNat := by
    rw [linkBits, ← entryEq]
    change first.bits.toNat + entry.bits.toNat ≤ 15 at totalBits
    omega
  have actualCapacity : distExtras.getD symbol 0 ≤ ((stream slowLink bs).drop codes[target].bits.toNat).length := by
    have fields := distance_base_symbol_fields valid actualMeaning
    rw [sourceLink, ← firstEq, ← entryEq, List.drop_drop, ← fields.1]
    simpa only [← entryEq] using capacity
  obtain ⟨consumed, slowNext, fastNext, extra, rest, consumedTwo, consumedLength,
    run, nextPacket, nextBuffers, leftEq, putEq, noAgain, brokeEq, againLEq, source, extraWidth, extraFits, value, resultLength, resultOut,
    read, extraValue, remainder, positiveValue, maxValue, actualValue⟩ :=
    linkPacket.dodist_selected_base_semantic_prefix_with_frame invariant linkBuffers actualHere codesGet leafBoundI
      leafFits leafWidth actualBase valid actualMeaning actualCapacity
  have finalSource : stream slowNext (bs.drop consumed) =
      (stream slow bs).drop (first.bits.toNat + entry.bits.toNat) := by
    rw [source, sourceLink, ← firstEq, ← entryEq, List.drop_drop]
  have decoder : decodeSym D (stream slow bs) = some (symbol, stream slowNext (bs.drop consumed)) := by
    rw [finalSource]
    exact decoded
  have extraRead : readBits (distExtras.getD symbol 0) (stream slowNext (bs.drop consumed)) = some (extra, rest) := by
    rw [source]
    exact read
  exact ⟨symbol, consumed, slowNext, fastNext, extra, rest, linked, valid, symbolMeaning,
    consumedTwo, consumedLength, firstRun, againD, run, nextPacket, nextBuffers, leftEq, putEq, noAgain, brokeEq.trans brokeRoot, againLEq.trans (Zlib.Inffast.Proofs.dodist_againL firstRun), decoder, extraWidth,
    extraFits, value, resultLength.trans length, resultOut.trans out, extraRead, extraValue,
    remainder, positiveValue, maxValue, actualValue⟩



#print axioms FastInputPacket.dodist_linked_base_semantic_prefix_with_frame
end Zlib.Inflate.Proofs

