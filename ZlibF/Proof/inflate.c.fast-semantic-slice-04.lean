import ZlibF.Proof.«inflate.c.fast-semantic-slice-03»
set_option autoImplicit false

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec

/-- The actual pointer difference followed by a valid `copyMatch` refines
one independent match token. The saved-window equality is an internal
history representation fact, and `Separate` permits one shared byte object. -/
theorem FastInputPacket.copy_after_diff_valid_token_view
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    (packet : FastInputPacket h slow bs l)
    (separate : Separate slow.next slow.have_.toNat
      slow.put slow.left.toNat)
    (left : slow.left ≠ 0)
    (avail : 258 ≤ slow.left.toNat)
    (length : 3 ≤ l.len.toNat ∧ l.len.toNat ≤ 258)
    (distance : 0 < l.dist.toNat)
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
    (available : l.dist.toNat ≤ c.whave.toNat + (j - bg))
    (whaveBound : c.whave.toNat ≤ c.wsize.toNat)
    (wnextBound : c.wnext.toNat ≤ c.wsize.toNat)
    (wsizeBound : c.wsize.toNat ≤ 32768)
    {saved : Array UInt8} {woff : Nat}
    (windowData : l.dist >
      { l with op := (Int64.ofInt ((j - bg : Nat) : Int)).toUInt64.toUInt32 }.op →
      ∃ window,
        window ≠ dest ∧ c.window = .ref window woff ∧
        Space.get h window = some saved ∧
        woff + c.wsize.toNat ≤ saved.size)
    {L D : List Nat} {dict history : List UInt8}
    {input r1 r2 r3 rest : List Bool}
    {symbol distanceSymbol lengthExtra distanceExtra : Nat}
    (source : stream slow bs = rest)
    (lengthCode : decodeSym L input = some (symbol, r1))
    (lengthSymbolMin : 257 ≤ symbol)
    (lengthSymbolMax : symbol ≤ 285)
    (lengthBits : readBits
      (lengthExtras.getD (symbol - 257) 0) r1 =
      some (lengthExtra, r2))
    (distanceCode : decodeSym D r2 = some (distanceSymbol, r3))
    (distanceSymbolBound : distanceSymbol ≤ 29)
    (distanceBits : readBits
      (distExtras.getD distanceSymbol 0) r3 =
      some (distanceExtra, rest))
    (lengthValue : l.len.toNat =
      lengthBases.getD (symbol - 257) 0 + lengthExtra)
    (distanceValue : l.dist.toNat =
      distBases.getD distanceSymbol 0 + distanceExtra)
    (dictionary : Zlib.Inffast.Spec.MatchHistory.saved saved
      c.wsize.toNat c.wnext.toNat c.whave.toNat woff = dict)
    (written : ZlibF.Math.LZ77Copy.writtenBytes output j
      (j - bg) = history)
    (backBound : l.dist.toNat ≤ (dict ++ history).length) :
    ∃ result after array,
      C.run (do
        let d ← Ptr.diff l.out c.beg
        Zlib.Inffast.copyMatch c
          { l with op := d.toUInt64.toUInt32 }) h =
        .ok (result, after) ∧
      FastInputPacket after slow bs result ∧
      result.out = .ref dest (j + l.len.toNat) ∧
      Space.get after dest = some array ∧
      ZlibF.Math.LZ77Copy.writtenBytes array
        (j + l.len.toNat) ((j - bg) + l.len.toNat) =
        ZlibF.Spec.copyBack dict l.dist.toNat l.len.toNat history ∧
      stream slow bs = rest ∧
      ZlibF.Spec.Token.Step L D dict history input rest
        (ZlibF.Math.LZ77Copy.writtenBytes array
          (j + l.len.toNat) ((j - bg) + l.len.toNat)) false := by
  have geometry := fast_output_room_of_guard outPtr endPtr
    outputGet outputSize current avail
    length.2 guard
  have currentBound : j ≤ output.size := geometry.1
  have outputRoom : oo ≤ j ∧
      j + l.len.toNat ≤ oo + slow.left.toNat := geometry.2
  have beginBound : bg ≤ output.size := by omega
  have diffRun : C.run (Ptr.diff l.out c.beg) h =
      .ok (Int64.ofInt ((j - bg : Nat) : Int), h) := by
    rw [outPtr, begPtr]
    have run := Ptr.diff_ok (r := dest) (a := output)
      outputGet currentBound beginBound
      (by omega : -(2 ^ 63 : Int) ≤ (j : Int) - (bg : Int) ∧
        (j : Int) - (bg : Int) < 2 ^ 63)
    have intEq : (j : Int) - (bg : Int) =
        ((j - bg : Nat) : Int) := by omega
    change (Ptr.diff (.ref dest j) (.ref dest bg)) h =
      .ok (Int64.ofInt ((j : Int) - (bg : Int)), h) at run
    simpa only [C.run, intEq] using run
  let atCopy : Zlib.Inffast.L :=
    { l with op := (Int64.ofInt ((j - bg : Nat) : Int)).toUInt64.toUInt32 }
  have produced : atCopy.op.toNat = j - bg ∧
      atCopy.op.toNat ≤ j :=
    fast_produced_of_diff (l := atCopy) outputGet
      currentBound beginBound beginLe span
      (by simpa only [outPtr, begPtr] using diffRun) rfl
  have copyPacket : FastInputPacket h slow bs atCopy :=
    packet.with_op _
  have availableCopy :
      l.dist.toNat ≤ c.whave.toNat + atCopy.op.toNat := by
    rw [produced.1]
    exact available
  have writtenCopy : ZlibF.Math.LZ77Copy.writtenBytes
      output j atCopy.op.toNat = history := by
    rw [produced.1]
    exact written
  obtain ⟨result, after, array, copyRun, next,
    out, get, bytes, inputBytes, sourceEq, token⟩ :=
    copyPacket.copyMatch_valid_token_view separate left length.1
      distance availableCopy whaveBound wnextBound wsizeBound
      outPtr outputPtr outputGet outputWrite outputSize
      outputRoom produced.2 windowData source lengthCode
      lengthSymbolMin lengthSymbolMax lengthBits distanceCode
      distanceSymbolBound distanceBits lengthValue distanceValue
      dictionary writtenCopy backBound
  have run : C.run (do
      let d ← Ptr.diff l.out c.beg
      Zlib.Inffast.copyMatch c
        { l with op := d.toUInt64.toUInt32 }) h =
      .ok (result, after) := by
    change (do
      let d ← Ptr.diff l.out c.beg
      Zlib.Inffast.copyMatch c
        { l with op := d.toUInt64.toUInt32 }) h =
      .ok (result, after)
    rw [bind_ok (by simpa only [C.run] using diffRun)]
    exact copyRun
  refine ⟨result, after, array, run, next, out, get, ?_,
    sourceEq, ?_⟩
  · rw [← produced.1]
    exact bytes
  · rw [← produced.1]
    exact token

#print axioms FastInputPacket.copy_after_diff_valid_token_view
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec

/-- For a valid distance base, the actual `distCont` path consumes the same
extra bits as the independent decoder and executes the exact token copy.
This is a source-level same-run bridge through the translated suffix. -/
theorem FastInputPacket.distCont_valid_token_view
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
      Space.get after dest = some array ∧
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
    _, get, bytes, _, token⟩ :=
    nextPacket.copy_after_diff_valid_token_view
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
    finalPacket, sourceNext, get, ?_, ?_⟩
  · simpa only [actualDistance, ← distanceBase] using bytes
  · exact token

#print axioms FastInputPacket.distCont_valid_token_view
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec

/-- The no-refill length-extra suffix reads precisely the independent
length-extra value on the same actual source run. -/
theorem FastInputPacket.dolenExt_length_extra_semantics
    {h : Heap} {slow : IL}
    {first second third fourth : UInt8} {rest : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow
      (first :: second :: third :: fourth :: rest) l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow
      (first :: second :: third :: fourth :: rest))
    (streamPtr : c.strm = some r)
    (statePtr : c.state = some (.tab zs))
    (whaveEq : c.whave = s.whave)
    (wsizeEq : c.wsize = s.wsize)
    (wnextEq : c.wnext = s.wnext)
    (windowEq : c.window = s.window)
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff rootWidth : Nat}
    (dcodePtr : c.dcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : DistTableSafe codes baseOff rootWidth)
    (mask : c.dmask.toUInt64.toNat = 2 ^ rootWidth - 1)
    (extraWidth : l.op.toNat ≤ 5)
    (extraFits : l.op.toNat ≤ slow.bits.toNat)
    (bitsBound : slow.bits.toNat ≤ 30)
    (left : slow.left ≠ 0)
    (avail : 258 ≤ slow.left.toNat)
    (length : 3 ≤ l.len.toNat ∧
      l.len.toNat + 2 ^ l.op.toNat ≤ 259)
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
    {symbol lengthExtra : Nat}
    {r1 r2 : List Bool}
    (width : l.op.toNat =
      lengthExtras.getD (symbol - 257) 0)
    (lengthInput : r1 = stream slow
      (first :: second :: third :: fourth :: rest))
    (lengthBits : readBits
      (lengthExtras.getD (symbol - 257) 0) r1 =
      some (lengthExtra, r2)) :
    lengthExtra = l.hold.toNat % 2 ^ l.op.toNat ∧
    r2 = (stream slow
      (first :: second :: third :: fourth :: rest)).drop l.op.toNat ∧
    ∃ used consumed slowNext result after,
      used ≤ 4 ∧ consumed ≤ 33 ∧
      C.run (Zlib.Inffast.Proofs.dolenExt c l) h =
        .ok (result, after) ∧
      FastInputPacket after slowNext
        ((first :: second :: third :: fourth :: rest).drop used)
        result ∧
      stream slowNext
        ((first :: second :: third :: fourth :: rest).drop used) =
        (stream slow
          (first :: second :: third :: fourth :: rest)).drop consumed ∧
      (FastDistancePost h after r zs z s slowNext
        ((first :: second :: third :: fourth :: rest).drop used)
        result dest output j (l.len.toNat + lengthExtra) ∨
       ∃ i, result.broke = true ∧
         after = badHeap h r zs z s i) := by
  let bs := first :: second :: third :: fourth :: rest
  have read := readBits_held_stream slow bs l.op.toNat extraFits
  have selected : readBits l.op.toNat (stream slow bs) =
      some (lengthExtra, r2) := by
    rw [width, ← lengthInput]
    exact lengthBits
  rw [read] at selected
  have extraEq : lengthExtra =
      l.hold.toNat % 2 ^ l.op.toNat :=
    by simpa only [Prod.fst, ← packet.hold] using
      (congrArg Prod.fst (Option.some.inj selected)).symm
  have restEq : r2 = (stream slow bs).drop l.op.toNat :=
    by simpa only [Prod.snd] using
      (congrArg Prod.snd (Option.some.inj selected)).symm
  obtain ⟨used, consumed, slowNext, result, after,
    usedBound, consumedBound, run, _, packetNext, _, _,
    sourceNext, outcome⟩ :=
    packet.dolenExt_default_state invariant buffers
      streamPtr statePtr whaveEq wsizeEq wnextEq windowEq
      dcodePtr codesGet safe mask extraWidth extraFits bitsBound
      left avail length outPtr outputPtr begPtr endPtr outputGet
      outputWrite outputSize current beginLe span guard
  refine ⟨extraEq, restEq, used, consumed, slowNext,
    result, after, usedBound, consumedBound, run,
    packetNext, sourceNext, ?_⟩
  rcases outcome with copied | bad
  · exact Or.inl (by simpa only [← extraEq] using copied)
  · rcases bad with ⟨i, broke, heapEq, _⟩
    exact Or.inr ⟨i, broke, heapEq⟩

#print axioms FastInputPacket.dolenExt_length_extra_semantics
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
open Zlib.Inftrees.Spec.DecodeSemantics
open Zlib.Inftrees.Spec.DecodeSoundness
open Zlib.Inftrees.Spec.DecodeShort
open Zlib.Inftrees.Spec.DecodeTableInvariant
open Zlib.Inftrees.Spec.Subtable

/-- A direct root length leaf selected from the actual held bits has the
independent symbol and base/extra meaning stored in the constructor's table
invariant. The bit stream is the proof-side public byte slice. -/
theorem FastInputPacket.length_root_leaf_meaning
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L}
    (packet : FastInputPacket h slow bs l)
    {codes : Array Code} {baseOff rootWidth used : Nat}
    {lens : List Nat}
    (meaning : Inv LENS codes baseOff rootWidth used lens)
    (rootFits : rootWidth ≤ slow.bits.toNat)
    (held : 15 ≤ slow.bits.toNat)
    (indexBound : baseOff +
      (l.hold.toNat % 2 ^ rootWidth) < codes.size)
    (noLink : IsLink LENS
      (codes.getD (baseOff + (l.hold.toNat % 2 ^ rootWidth)) default) = false)
    (accepted : LeafAccepted LENS
      (codes.getD (baseOff + (l.hold.toNat % 2 ^ rootWidth)) default)) :
    let entry := codes.getD
      (baseOff + (l.hold.toNat % 2 ^ rootWidth)) default
    ∃ symbol,
      ValidSymbol LENS symbol ∧
      SymbolEntry LENS symbol entry ∧
      entry.bits.toNat = lens.getD symbol 0 ∧
      decodeSym lens (stream slow bs) =
        some (symbol, (stream slow bs).drop entry.bits.toNat) := by
  let slice := l.hold.toNat % 2 ^ rootWidth
  let entry := codes.getD (baseOff + slice) default
  have rootRead := readBits_held_stream slow bs rootWidth rootFits
  have rootReadL : readBits rootWidth (stream slow bs) =
      some (slice, (stream slow bs).drop rootWidth) := by
    simpa only [slice, ← packet.hold] using rootRead
  have cell : codes[baseOff + slice]? = some entry := by
    have bound : baseOff + slice < codes.size := indexBound
    simp [entry, Array.getD_eq_getD_getElem?, bound]
  have noLinkCode :
      (entry.op != 0 && (entry.op &&& 0xf0) == 0) = false := by
    simpa [IsLink, entry, slice] using noLink
  have query : tableRead LENS codes baseOff rootWidth
      (stream slow bs) = some (entry, entry.bits.toNat) := by
    simp only [tableRead, rootReadL, bind, Option.bind, cell]
    simp only [noLinkCode]
    simp
  have long : 15 ≤ (stream slow bs).length := by
    simp only [stream, List.length_append, natBits_length]
    omega
  have padding : padded (stream slow bs) = stream slow bs := by
    simp [padded, Nat.sub_eq_zero_of_le long]
  have fit : entry.bits.toNat ≤ (stream slow bs).length := by
    obtain ⟨tableEntry, tableCell, _, tableBits⟩ :=
      meaning.rootTable.2.2.2 slice
        (Nat.mod_lt _ (Nat.pow_pos (by omega)))
    have same : tableEntry = entry :=
      Option.some.inj (tableCell.symm.trans cell)
    rw [same] at tableBits
    simp only [stream, List.length_append, natBits_length]
    omega
  obtain ⟨symbol, valid, entryMeaning, codeLen,
    decoded, _⟩ := meaning.short (stream slow bs) entry
    entry.bits.toNat (by rw [padding]; exact query) fit accepted
  exact ⟨symbol, valid, entryMeaning, codeLen, decoded⟩

#print axioms FastInputPacket.length_root_leaf_meaning
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
open Zlib.Inftrees.Spec.DecodeSemantics
open Zlib.Inftrees.Spec.DecodeSoundness
open Zlib.Inftrees.Spec.DecodeTableInvariant
open Zlib.Inftrees.Spec.Subtable

/-- The translated root pointer addition and the independent length symbol
refer to the same actual table cell on public byte views. -/
theorem FastInputPacket.length_selected_root_leaf_meaning
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    (packet : FastInputPacket h slow bs l)
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff rootWidth used : Nat} {lens : List Nat}
    (lcodePtr : c.lcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : LenTableSafe codes baseOff rootWidth)
    (meaning : Inv LENS codes baseOff rootWidth used lens)
    (mask : c.lmask.toUInt64.toNat = 2 ^ rootWidth - 1)
    (rootFits : rootWidth ≤ slow.bits.toNat)
    (held : 15 ≤ slow.bits.toNat)
    (noLink : IsLink LENS
      (codes.getD (baseOff + (l.hold.toNat % 2 ^ rootWidth)) default) = false)
    (accepted : LeafAccepted LENS
      (codes.getD (baseOff + (l.hold.toNat % 2 ^ rootWidth)) default)) :
    let rootSlice := (l.hold &&& c.lmask.toUInt64).toNat
    let selected : Zlib.Inffast.L :=
      { l with here := .ref codeRef (baseOff + rootSlice) }
    let entry := codes.getD (baseOff + rootSlice) default
    C.run (c.lcode.add rootSlice) h =
      .ok (.ref codeRef (baseOff + rootSlice), h) ∧
    FastInputPacket h slow bs selected ∧
    ∃ symbol,
      ValidSymbol LENS symbol ∧
      SymbolEntry LENS symbol entry ∧
      entry.bits.toNat = lens.getD symbol 0 ∧
      decodeSym lens (stream slow bs) =
        some (symbol, (stream slow bs).drop entry.bits.toNat) := by
  obtain ⟨_, addRun, selectedPacket⟩ :=
    packet.fast_body_root_lookup lcodePtr codesGet safe mask
  have maskIndex : (l.hold &&& c.lmask.toUInt64).toNat =
      l.hold.toNat % 2 ^ rootWidth :=
    Zlib.Inffast.Proofs.u64_and_mask mask
  have rootBound : baseOff +
      (l.hold.toNat % 2 ^ rootWidth) < codes.size := by
    have rootSize := safe.2.1
    have modBound : l.hold.toNat % 2 ^ rootWidth <
        2 ^ rootWidth :=
      Nat.mod_lt _ (Nat.pow_pos (by omega))
    omega
  obtain ⟨symbol, valid, entryMeaning, width, decoded⟩ :=
    packet.length_root_leaf_meaning meaning rootFits held
      rootBound noLink accepted
  refine ⟨addRun, selectedPacket, symbol, valid, ?_, ?_, ?_⟩
  · simpa only [maskIndex] using entryMeaning
  · simpa only [maskIndex] using width
  · simpa only [maskIndex] using decoded

#print axioms FastInputPacket.length_selected_root_leaf_meaning
end Zlib.Inflate.Proofs

