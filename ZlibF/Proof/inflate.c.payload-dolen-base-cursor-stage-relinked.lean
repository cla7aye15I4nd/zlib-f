import ZlibF.Proof.«inflate.c.payload-dolen-len-cursor-stage-relinked»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
open Zlib.Inftrees.Spec Zlib.Inftrees.Spec.DecodeSemantics
set_option autoImplicit false
set_option maxRecDepth 4096

theorem FastInputPacket.payload_dolen_base_source_prefix
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


theorem payload_length_base_symbol_fields_view {symbol : Nat} {entry : Code}
    (lo : 257 ≤ symbol) (hi : symbol ≤ 285)
    (meaning : SymbolEntry LENS symbol entry) :
    entry.op &&& 16 ≠ 0 ∧
    (entry.op &&& 15).toNat = lengthExtras.getD (symbol - 257) 0 ∧
    entry.val.toNat = lengthBases.getD (symbol - 257) 0 ∧
    (entry.op &&& 15).toNat ≤ 5 ∧
    3 ≤ entry.val.toNat ∧
    entry.val.toNat + 2 ^ (entry.op &&& 15).toNat ≤ 259 := by
  have finite : ∀ n : Fin 29,
      lengthExtras.getD n.val 0 ≤ 5 ∧
      3 ≤ lengthBases.getD n.val 0 ∧
      lengthBases.getD n.val 0 + 2 ^ lengthExtras.getD n.val 0 ≤ 259 := by
    decide +kernel
  have values := finite ⟨symbol - 257, by omega⟩
  have values' : lengthExtras.getD (symbol - 257) 0 ≤ 5 ∧
      3 ≤ lengthBases.getD (symbol - 257) 0 ∧
      lengthBases.getD (symbol - 257) 0 +
        2 ^ lengthExtras.getD (symbol - 257) 0 ≤ 259 := by
    simpa using values
  have fields : entry.op.toNat = 16 + lengthExtras.getD (symbol - 257) 0 ∧
      entry.val.toNat = lengthBases.getD (symbol - 257) 0 := by
    simpa only [SymbolEntry, ite_true,
      ite_eq_right (show ¬ symbol < 256 by omega),
      ite_eq_right (show symbol ≠ 256 by omega),
      ite_eq_left hi] using meaning
  have mask : ∀ op : UInt8, 16 ≤ op.toNat → op.toNat ≤ 21 →
      op &&& 16 ≠ 0 ∧ (op &&& 15).toNat = op.toNat - 16 := by
    apply Zlib.Inffast.Proofs.u8_forall
    decide +kernel
  obtain ⟨base, extra⟩ := mask entry.op (by omega) (by omega)
  have extraEq : (entry.op &&& 15).toNat = lengthExtras.getD (symbol - 257) 0 := by
    rw [extra, fields.1]
    omega
  refine ⟨base, extraEq, fields.2, ?_, ?_, ?_⟩
  · rw [extraEq]
    exact values'.1
  · rw [fields.2]
    exact values'.2.1
  · rw [extraEq, fields.2]
    exact values'.2.2


theorem FastInputPacket.dolen_base_valid_token_view_cursor
    {h : Heap} {slow : IL}
    {first second third fourth fifth : UInt8} {tail : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow
      (first :: second :: third :: fourth :: fifth :: tail) l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow
      (first :: second :: third :: fourth :: fifth :: tail))
    {codeRef : CodeRef} {codes : Array Code} {index : Nat}
    (herePtr : l.here = .ref codeRef index)
    (codesGet : Space.get h codeRef = some codes)
    (indexBound : index < codes.size)
    (codeFits : codes[index].bits.toNat ≤ slow.bits.toNat)
    (codeWidth : codes[index].bits.toNat ≤ 15)
    (base : codes[index].op &&& 16 ≠ 0)
    {distRef : CodeRef} {distCodes : Array Code}
    {distOff distWidth tableUsed : Nat} {D : List Nat}
    (dcodePtr : c.dcode = .ref distRef distOff)
    (distGet : Space.get h distRef = some distCodes)
    (distSafe : DistTableSafe distCodes distOff distWidth)
    (distMeaning : DecodeTableInvariant.Inv DISTS distCodes distOff distWidth tableUsed D)
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
    {L : List Nat} {dict history : List UInt8} {input r1 r2 r3 rest : List Bool}
    {symbol distanceSymbol lengthExtra distanceExtra : Nat}
    (lengthCode : decodeSym L input = some (symbol, r1))
    (lengthMin : 257 ≤ symbol) (lengthMax : symbol ≤ 285)
    (lengthMeaning : SymbolEntry LENS symbol codes[index])
    (lengthSource : input = stream slow
      (first :: second :: third :: fourth :: fifth :: tail))
    (codeRest : r1 = (stream slow
      (first :: second :: third :: fourth :: fifth :: tail)).drop codes[index].bits.toNat)
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
      used ≤ 5 ∧ used ≤ (first :: second :: third :: fourth :: fifth :: tail).length ∧
      C.run (Zlib.Inffast.dolen c l) h = .ok (result, after) ∧
      result.againL = false ∧ result.againD = false ∧
      result.out = .ref dest (j + (codes[index].val.toNat + lengthExtra)) ∧
      result.broke = l.broke ∧
      FastInputPacket after slowFinal
        ((first :: second :: third :: fourth :: fifth :: tail).drop used) result ∧
      stream slowFinal
        ((first :: second :: third :: fourth :: fifth :: tail).drop used) = rest ∧
      Space.get after dest = some array ∧ array.size = output.size ∧
      Space.ro after dest = false ∧
      ZlibF.Math.LZ77Copy.writtenBytes array
        (j + (codes[index].val.toNat + lengthExtra))
        ((j - bg) + (codes[index].val.toNat + lengthExtra)) =
        copyBack dict (distBases.getD distanceSymbol 0 + distanceExtra)
          (codes[index].val.toNat + lengthExtra) history ∧
      Token.Step L D dict history input rest
        (ZlibF.Math.LZ77Copy.writtenBytes array
          (j + (codes[index].val.toNat + lengthExtra))
          ((j - bg) + (codes[index].val.toNat + lengthExtra))) false ∧
      result.in_ = inputAdvance l.in_ used := by
  let raw := first :: second :: third :: fourth :: fifth :: tail
  let entry := codes[index]
  let slowCode : IL := { slow with hold := slow.hold >>> entry.bits.toUInt32.toUInt64, bits := slow.bits - entry.bits.toUInt32 }
  let baseLocal : Zlib.Inffast.L := { l with againL := false, hold := l.hold >>> entry.bits.toUInt32.toUInt64, bits := l.bits - entry.bits.toUInt32, op := entry.op.toUInt32 &&& 15, len := entry.val.toUInt32 }
  obtain ⟨basePacket, codeBuffers, codeStream, runEq⟩ :=
    packet.payload_dolen_base_source_prefix buffers herePtr codesGet indexBound
      codeFits codeWidth base
  have fields := payload_length_base_symbol_fields_view lengthMin lengthMax lengthMeaning
  have baseWidth : baseLocal.op.toNat ≤ 5 := by
    simpa only [baseLocal, Zlib.Inffast.Proofs.mask15] using fields.2.2.2.1
  have baseLength : 3 ≤ baseLocal.len.toNat ∧
      baseLocal.len.toNat + 2 ^ baseLocal.op.toNat ≤ 259 := by
    simpa only [baseLocal, UInt16.toNat_toUInt32, Zlib.Inffast.Proofs.mask15] using
      (And.intro fields.2.2.2.2.1 fields.2.2.2.2.2)
  have baseBits : slowCode.bits.toNat ≤ 30 := by
    change (slow.bits - entry.bits.toUInt32).toNat ≤ 30
    rw [Zlib.Inffast.Proofs.u32_toNat_sub (by
      simpa only [entry, UInt8.toNat_toUInt32] using codeFits)]
    omega
  have baseOut : baseLocal.out = .ref dest j := outPtr
  have basePut : slowCode.put = .ref dest oo := outputPtr
  have baseEnd : c.end_ = .ref dest (oo + slowCode.left.toNat - 257) := endPtr
  have baseSize : oo + slowCode.left.toNat ≤ output.size := outputSize
  have baseGuard : C.run (Ptr.lt baseLocal.out c.end_) h = .ok (true, h) := guard
  have baseWidthEq : baseLocal.op.toNat = lengthExtras.getD (symbol - 257) 0 := by
    simpa only [baseLocal, Zlib.Inffast.Proofs.mask15] using fields.2.1
  have baseValue : baseLocal.len.toNat = lengthBases.getD (symbol - 257) 0 := by
    simpa only [baseLocal, UInt16.toNat_toUInt32] using fields.2.2.1
  have codeSource : r1 = stream slowCode raw := by
    rw [codeRest, codeStream]
  have actualCode : decodeSym L (stream slow raw) = some (symbol, r1) := by
    rw [← lengthSource]
    exact lengthCode
  have inputCode : decodeSym L input = some (symbol, r1) := by
    simpa only [lengthSource] using actualCode
  obtain ⟨used, result, after, array, slowFinal,
    usedBound, usedRaw, lenRun, againD, out, broke, againL,
    finalPacket, finalSource, get, size, ro, bytes, token, cursorLen⟩ :=
    basePacket.dolenLen_valid_token_view_cursor invariant codeBuffers
      dcodePtr distGet distSafe distMeaning distFlags distMask
      baseWidth baseBits left avail baseLength baseOut basePut begPtr baseEnd
      outputGet outputWrite baseSize current beginLe span baseGuard
      whaveBound wnextBound wsizeBound windowView
      inputCode lengthMin lengthMax lengthBits baseWidthEq codeSource
      distanceCode distanceSymbolBound distanceBits baseValue
      dictionary dictCount written historyCount backBound
  have run : C.run (Zlib.Inffast.dolen c l) h = .ok (result, after) := by
    rw [runEq]
    exact lenRun
  refine ⟨used, result, after, array, slowFinal, usedBound, usedRaw,
    run, ?_, againD, ?_, ?_, finalPacket, finalSource,
    get, size, ro, ?_, ?_, ?_⟩
  · simpa only [baseLocal] using againL
  · simpa only [baseLocal, UInt16.toNat_toUInt32] using out
  · simpa only [baseLocal] using broke
  · simpa only [baseLocal, UInt16.toNat_toUInt32] using bytes
  · simpa only [baseLocal, UInt16.toNat_toUInt32] using token
  · simpa only [baseLocal] using cursorLen

#print axioms FastInputPacket.dolen_base_valid_token_view_cursor
end Zlib.Inflate.Proofs
