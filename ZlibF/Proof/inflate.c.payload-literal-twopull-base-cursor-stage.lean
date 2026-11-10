import ZlibF.Proof.«inflate.c.payload-linked-literal-twopull-cursor-stage»
namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
set_option autoImplicit false
theorem literal_body_two_pull_generic_with_packet_cursor
    {h : Heap} {slow : IL}
    {first second third fourth fifth sixth : UInt8}
    {rest : List UInt8} {l : Zlib.Inffast.L}
    {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow
      (first :: second :: third :: fourth :: fifth :: sixth :: rest) l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow
      (first :: second :: third :: fourth :: fifth :: sixth :: rest))
    (small : slow.bits.toNat < 15)
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff rootWidth index : Nat}
    (lcodePtr : c.lcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : LenTableSafe codes baseOff rootWidth)
    (mask : c.lmask.toUInt64.toNat = 2 ^ rootWidth - 1)
    (indexEq : index = baseOff +
      ((((l.hold + (first.toUInt64 <<< l.bits.toUInt64)) +
        (second.toUInt64 <<< (l.bits + 8).toUInt64)) &&&
          c.lmask.toUInt64).toNat))
    (indexBound : index < codes.size)
    (codeFits : codes[index].bits.toNat ≤ slow.bits.toNat + 16)
    (codeWidth : codes[index].bits.toNat ≤ 15)
    (literal : codes[index].op = 0)
    (left : slow.left ≠ 0)
    (avail : 258 ≤ slow.left.toNat)
    {dest : BRef} {output : Array UInt8} {oo j : Nat}
    (outPtr : l.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (endPtr : c.end_ = .ref dest (oo + slow.left.toNat - 257))
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (current : oo ≤ j)
    (guard : C.run (Ptr.lt l.out c.end_) h = .ok (true, h))
    {L D : List Nat} {dict history : List UInt8} {symbol : Nat}
    (decoded : decodeSym L
      (stream slow (first :: second :: third :: fourth :: fifth :: sixth :: rest)) =
      some (symbol,
        (stream slow (first :: second :: third :: fourth :: fifth :: sixth :: rest)).drop
          codes[index].bits.toNat))
    (smallSymbol : symbol < 256)
    (value : codes[index].val.toNat = symbol) :
    ∃ slowPrefix slowFinal result after,
      C.run (Zlib.Inffast.inflate_fast_body c l) h =
        .ok (result, after) ∧
      result.out = .ref dest (j + 1) ∧
      after = Space.put h dest
        (output.set! j codes[index].val.toUInt8) ∧
      SliceEnv h after slowPrefix slowFinal
        (third :: fourth :: fifth :: sixth :: rest) ∧
      FastInputPacket after slowFinal
        (third :: fourth :: fifth :: sixth :: rest) result ∧
      DispatchBuffers after r slowFinal
        (third :: fourth :: fifth :: sixth :: rest) ∧
      ZlibF.Spec.Token.Step L D dict history
        (stream slow (first :: second :: third :: fourth :: fifth :: sixth :: rest))
        (stream slowFinal (third :: fourth :: fifth :: sixth :: rest))
        (history ++ [codes[index].val.toUInt8]) false ∧
      result.in_ = inputAdvance l.in_ 2 := by
  obtain ⟨slow2, fast2, selected, rootSlice, prefixRun,
    selectedEq, selectedPacket, buffers2, _, source2,
    outFrame, holdFrame, putFrame, leftFrame,
    nextFrame, bitsFrame, _, _, rootSliceEq, rootBound⟩ :=
    packet.two_pull_root_prefix invariant buffers small
      lcodePtr codesGet safe mask
  have rootEq : index = baseOff + rootSlice := by
    rw [indexEq, ← holdFrame, ← rootSliceEq]
  have selectedHere : selected.here = .ref codeRef index := by
    rw [selectedEq, rootEq]
  have selectedOut : selected.out = .ref dest j :=
    outFrame.trans outPtr
  have put2 : slow2.put = .ref dest oo :=
    putFrame.trans outputPtr
  have left2 : slow2.left ≠ 0 := by
    rw [leftFrame]
    exact left
  have avail2 : 258 ≤ slow2.left.toNat := by
    rw [leftFrame]
    exact avail
  have end2 : c.end_ = .ref dest
      (oo + slow2.left.toNat - 257) := by
    rw [leftFrame]
    exact endPtr
  have size2 : oo + slow2.left.toNat ≤ output.size := by
    rw [leftFrame]
    exact outputSize
  have guard2 : C.run (Ptr.lt selected.out c.end_) h =
      .ok (true, h) := by
    rw [selectedOut]
    simpa only [outPtr] using guard
  have codeFits2 : codes[index].bits.toNat ≤ slow2.bits.toNat := by
    rw [bitsFrame]
    exact codeFits
  have decoded2 : decodeSym L
      (stream slow2 (third :: fourth :: fifth :: sixth :: rest)) =
      some (symbol,
        (stream slow2 (third :: fourth :: fifth :: sixth :: rest)).drop
          codes[index].bits.toNat) := by
    rw [source2]
    exact decoded
  have literalResult := literal_token_view_generic
    (L := L) (D := D) (dict := dict) (history := history)
    selectedPacket invariant buffers2 selectedHere codesGet
    indexBound codeFits2 codeWidth literal left2 avail2
    selectedOut put2 end2 outputGet outputWrite
    size2 current guard2 decoded2 smallSymbol value
  dsimp only at literalResult
  obtain ⟨dolenRun, slice, finalBuffers, token⟩ := literalResult
  have loopRun := dolen_loop_one dolenRun (by rfl)
  let prefixM : C.M Zlib.Inffast.L := do
    let one ← Zlib.Inffast.pull l
    let two ← Zlib.Inffast.pull one
    let here ← c.lcode.add
      (two.hold &&& c.lmask.toUInt64).toNat
    pure { two with here }
  have bodyPrefix : C.run (Zlib.Inffast.inflate_fast_body c l) h =
      C.run (prefixM >>= fun current =>
        cdoWhile (Zlib.Inffast.dolen c)
          (fun current => pure (current.againL, current)) current) h := by
    unfold Zlib.Inffast.inflate_fast_body
    have needsPull : l.bits < 15 := by
      rw [packet.bits]
      exact UInt32.lt_iff_toNat_lt.mpr small
    simp only [needsPull, ite_true]
    simp only [prefixM, C.run, payload_bind_assoc,
      payload_pure_bind]
  have bodyRun : C.run (Zlib.Inffast.inflate_fast_body c l) h =
      C.run (cdoWhile (Zlib.Inffast.dolen c)
        (fun current => pure (current.againL, current)) selected) h := by
    rw [bodyPrefix]
    change (prefixM >>= fun current =>
      cdoWhile (Zlib.Inffast.dolen c)
        (fun current => pure (current.againL, current)) current) h = _
    change prefixM h = .ok (selected, h) at prefixRun
    rw [bind_app, prefixRun]
    rfl
  have finalRun := bodyRun.trans loopRun
  have finalPacket : FastInputPacket
      (Space.put h dest (output.set! j codes[index].val.toUInt8))
      { slow2 with
        hold := slow2.hold >>> codes[index].bits.toUInt32.toUInt64,
        bits := slow2.bits - codes[index].bits.toUInt32 }
      (third :: fourth :: fifth :: sixth :: rest)
      { selected with
        againL := false, op := codes[index].op.toUInt32,
        hold := selected.hold >>> codes[index].bits.toUInt32.toUInt64,
        bits := selected.bits - codes[index].bits.toUInt32,
        out := .ref dest (j + 1) } := by
    refine ⟨slice.afterBits, ?_, ?_, ?_⟩
    · exact selectedPacket.cursor
    · exact congrArg (fun x : UInt64 =>
        x >>> codes[index].bits.toUInt32.toUInt64) selectedPacket.hold
    · exact congrArg (fun x : UInt32 =>
        x - codes[index].bits.toUInt32) selectedPacket.bits
  refine ⟨slow2, _, _, _, finalRun, ?_, ?_,
    slice, finalPacket, finalBuffers, ?_, ?_⟩
  · rfl
  · rfl
  · rw [source2] at token
    exact token
  · change selected.in_ = inputAdvance l.in_ 2
    rw [selectedPacket.cursor, nextFrame, ← packet.cursor]

#print axioms literal_body_two_pull_generic_with_packet_cursor
end Zlib.Inflate.Proofs
