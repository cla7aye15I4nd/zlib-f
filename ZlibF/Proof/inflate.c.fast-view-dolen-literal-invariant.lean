import ZlibF.Proof.«inflate.c.fast-view-literal-write-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- The actual translated `dolen` literal branch reads the selected code,
consumes its bits and writes its byte on a caller output view. -/
theorem FastInputPacket.dolen_literal_default_state
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow bs l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    {lenRef : CodeRef} {lenCodes : Array Code} {index : Nat}
    (herePtr : l.here = .ref lenRef index)
    (lenGet : Space.get h lenRef = some lenCodes)
    (indexBound : index < lenCodes.size)
    (codeFits : lenCodes[index].bits.toNat ≤ slow.bits.toNat)
    (codeWidth : lenCodes[index].bits.toNat ≤ 15)
    (literal : lenCodes[index].op = 0)
    (left : slow.left ≠ 0)
    (avail : 258 ≤ slow.left.toNat)
    {dest : BRef} {output : Array UInt8} {oo j : Nat}
    (outPtr : l.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (endPtr : c.end_ = .ref dest
      (oo + slow.left.toNat - 257))
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (current : oo ≤ j)
    (guard : C.run (Ptr.lt l.out c.end_) h = .ok (true, h)) :
    let entry := lenCodes[index]
    let count : UInt32 := entry.bits.toUInt32
    let slowNext : IL := { slow with
      hold := slow.hold >>> count.toUInt64,
      bits := slow.bits - count }
    let result : Zlib.Inffast.L := { l with
      againL := false,
      op := entry.op.toUInt32,
      hold := l.hold >>> count.toUInt64,
      bits := l.bits - count,
      out := .ref dest (j + 1) }
    let after := Space.put h dest (output.set! j entry.val.toUInt8)
    C.run (Zlib.Inffast.dolen c l) h = .ok (result, after) ∧
      result.againL = false ∧
      FastInputPacket after slowNext bs result ∧
      DefaultStateJ after r zs z s ∧
      DispatchBuffers after r slowNext bs ∧
      ByteViewSizes h after ∧
      stream slowNext bs = List.drop entry.bits.toNat (stream slow bs) ∧
      Space.get after dest = some (output.set! j entry.val.toUInt8) ∧
      Space.ro after dest = false ∧
      BufferFrame h after (fun _ => False)
        [⟨slow.put, slow.left.toNat⟩] := by
  let entry : Code := lenCodes[index]
  let count : UInt32 := entry.bits.toUInt32
  have load : Ptr.load l.here h = .ok (entry, h) := by
    rw [herePtr]
    exact Ptr.load_ok lenGet indexBound
  have countFits : count.toNat ≤ slow.bits.toNat := by
    simpa only [count, entry, Zlib.Inffast.Proofs.toNat32]
      using codeFits
  have countSmall : count.toNat < 64 := by
    have width : count.toNat ≤ 15 := by
      simpa only [count, entry, Zlib.Inffast.Proofs.toNat32]
        using codeWidth
    omega
  let firstLocal : Zlib.Inffast.L :=
    { l with againL := false, op := count }
  have firstPacket : FastInputPacket h slow bs firstLocal :=
    ⟨packet.source, packet.cursor, packet.hold, packet.bits⟩
  have dropped := firstPacket.drop_bits_default_state
    buffers count countFits countSmall
  let slowNext : IL := { slow with
    hold := slow.hold >>> count.toUInt64,
    bits := slow.bits - count }
  let afterCode : Zlib.Inffast.L := { firstLocal with
    hold := firstLocal.hold >>> count.toUInt64,
    bits := firstLocal.bits - count }
  have codePacket : FastInputPacket h slowNext bs afterCode := dropped.1
  have codeBuffers : DispatchBuffers h r slowNext bs := dropped.2.1
  have codeStream : stream slowNext bs =
      List.drop entry.bits.toNat (stream slow bs) := by
    simpa only [count, Zlib.Inffast.Proofs.toNat32]
      using dropped.2.2.1
  let literalLocal : Zlib.Inffast.L :=
    { afterCode with op := entry.op.toUInt32 }
  have literalPacket : FastInputPacket h slowNext bs literalLocal :=
    ⟨codePacket.source, codePacket.cursor,
      codePacket.hold, codePacket.bits⟩
  let one : Zlib.Inffast.L := { l with len := 1 }
  have oneGuard : C.run (Ptr.lt one.out c.end_) h = .ok (true, h) := guard
  have oneRoom := fast_output_room_of_guard
    (l := one) (slow := slow) outPtr endPtr outputGet
    outputSize current avail (by simp [one]) oneGuard
  have inside : oo ≤ j ∧ j < oo + slow.left.toNat := by
    constructor
    · exact current
    · have room := oneRoom.2.2
      change j + 1 ≤ oo + slow.left.toNat at room
      omega
  have literalOut : literalLocal.out = .ref dest j := outPtr
  have literalPut : slowNext.put = .ref dest oo := outputPtr
  have literalSize : oo + slowNext.left.toNat ≤ output.size := outputSize
  obtain ⟨writeRun, finalPacket, finalState, finalBuffers,
    sizes, finalGet, finalWrite, frame⟩ :=
    literalPacket.literal_write_default_state invariant codeBuffers
      left literalOut literalPut outputGet outputWrite literalSize
      inside entry.val.toUInt8
  have shiftRun : Zlib.Inffast.shr64 l.hold count.toUInt64 h =
      .ok (l.hold >>> count.toUInt64, h) := by
    apply Zlib.Inffast.Proofs.shr64_ok
    rw [UInt32.toNat_toUInt64]
    exact countSmall
  have literalBool : (entry.op.toUInt32 == 0) = true := by
    simp [entry, literal]
  have run : C.run (Zlib.Inffast.dolen c l) h =
      .ok ({ literalLocal with out := .ref dest (j + 1) },
        Space.put h dest (output.set! j entry.val.toUInt8)) := by
    change (Zlib.Inffast.dolen c l) h = _
    rw [Zlib.Inffast.Proofs.dolen_eq_len]
    rw [bind_ok load]
    rw [bind_ok shiftRun]
    rw [bind_ok load]
    simp only [literalBool, ite_true]
    rw [bind_ok load]
    simpa only [C.run, literalLocal, afterCode, firstLocal,
      count, entry] using writeRun
  exact ⟨run, rfl, finalPacket, finalState, finalBuffers,
    sizes, codeStream, finalGet, finalWrite, frame⟩

end Zlib.Inflate.Proofs
