import ZlibF.Proof.«inflate.c.payload-literal-twopull-cursor-stage»
namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
set_option autoImplicit false
theorem eob_body_two_pull_generic_with_packet_cursor
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
    (statePtr : c.state = some (.tab zs))
    (mode : DataTableMode s.mode)
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
    (nonzero : codes[index].op ≠ 0)
    (notBase : (codes[index].op.toUInt32 &&& 16 != 0) = false)
    (notLink : (codes[index].op.toUInt32 &&& 64 == 0) = false)
    (endCode : (codes[index].op.toUInt32 &&& 32 != 0) = true)
    {L D : List Nat} {dict history : List UInt8}
    (decoded : decodeSym L
      (stream slow (first :: second :: third :: fourth :: fifth :: sixth :: rest)) =
      some (256,
        (stream slow (first :: second :: third :: fourth :: fifth :: sixth :: rest)).drop
          codes[index].bits.toNat)) :
    ∃ slowPrefix slowFinal result after,
      C.run (Zlib.Inffast.inflate_fast_body c l) h =
        .ok (result, after) ∧
      after = setI h zs { s with mode := TYPE } ∧
      result.broke = true ∧ result.out = l.out ∧
      SliceEnv h after slowPrefix slowFinal
        (third :: fourth :: fifth :: sixth :: rest) ∧
      FastInputPacket after slowFinal
        (third :: fourth :: fifth :: sixth :: rest) result ∧
      DispatchBuffers after r slowFinal
        (third :: fourth :: fifth :: sixth :: rest) ∧
      ZlibF.Spec.Token.Step L D dict history
        (stream slow (first :: second :: third :: fourth :: fifth :: sixth :: rest))
        (stream slowFinal (third :: fourth :: fifth :: sixth :: rest))
        history true ∧ result.in_ = inputAdvance l.in_ 2 := by
  obtain ⟨slow2, fast2, selected, rootSlice, prefixRun,
    selectedEq, selectedPacket, buffers2, _, source2,
    outFrame, holdFrame, _, _, nextFrame, bitsFrame,
    _, _, rootSliceEq, _⟩ :=
    packet.two_pull_root_prefix invariant buffers small
      lcodePtr codesGet safe mask
  have rootEq : index = baseOff + rootSlice := by
    rw [indexEq, ← holdFrame, ← rootSliceEq]
  have selectedHere : selected.here = .ref codeRef index := by
    rw [selectedEq, rootEq]
  have codeFits2 : codes[index].bits.toNat ≤ slow2.bits.toNat := by
    rw [bitsFrame]
    exact codeFits
  obtain ⟨result, slowFinal, dolenRun, broke, noAgain,
    inputFrame, outputFrame, finalPacket, _, finalBuffers,
    _, sourceDrop⟩ :=
    selectedPacket.dolen_end_leaf_default_state
      invariant buffers2 statePtr mode selectedHere codesGet
      indexBound codeFits2 codeWidth nonzero notBase
      notLink endCode
  have cursorEq : slowFinal.next = slow2.next := by
    rw [← finalPacket.cursor, inputFrame]
    exact selectedPacket.cursor
  have countEq : slowFinal.have_ = slow2.have_ := by
    apply UInt32.toNat_inj.mp
    rw [finalPacket.source.have_eq, selectedPacket.source.have_eq]
  have slice : SliceEnv h (setI h zs { s with mode := TYPE })
      slow2 slowFinal (third :: fourth :: fifth :: sixth :: rest) :=
    ⟨selectedPacket.source, finalPacket.source,
      cursorEq, countEq⟩
  have loopRun := dolen_loop_one dolenRun noAgain
  have needsPull : l.bits < 15 := by
    rw [packet.bits]
    exact UInt32.lt_iff_toNat_lt.mpr small
  have bodyRun := body_from_two_pull_root needsPull prefixRun loopRun
  have decoded2 : decodeSym L
      (stream slow2 (third :: fourth :: fifth :: sixth :: rest)) =
      some (256,
        (stream slow2 (third :: fourth :: fifth :: sixth :: rest)).drop
          codes[index].bits.toNat) := by
    rw [source2]
    exact decoded
  have token : ZlibF.Spec.Token.Step L D dict history
      (stream slow (first :: second :: third :: fourth :: fifth :: sixth :: rest))
      (stream slowFinal (third :: fourth :: fifth :: sixth :: rest))
      history true := by
    rw [sourceDrop, source2]
    exact ZlibF.Spec.Token.Step.eob decoded
  refine ⟨slow2, slowFinal, result,
    setI h zs { s with mode := TYPE }, bodyRun, rfl,
    broke, outputFrame.trans outFrame, slice, finalPacket,
    finalBuffers, token, ?_⟩
  rw [inputFrame, selectedPacket.cursor, nextFrame, ← packet.cursor]

#print axioms eob_body_two_pull_generic_with_packet_cursor
end Zlib.Inflate.Proofs
