import ZlibF.Proof.«inflate.c.fast-view-diff-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Dropping consumed fast bits preserves the synchronized public input
packet and all caller buffer ranges. The remaining bit stream is exact. -/
theorem FastInputPacket.drop_bits_default_state
    {h : Heap} {slow : IL} {bs : List UInt8}
    {fastLocal : Zlib.Inffast.L} {r : ZStreamRef}
    (packet : FastInputPacket h slow bs fastLocal)
    (buffers : DispatchBuffers h r slow bs)
    (count : UInt32)
    (within : count.toNat ≤ slow.bits.toNat)
    (small : count.toNat < 64) :
    let slowNext : IL := { slow with
      hold := slow.hold >>> count.toUInt64,
      bits := slow.bits - count }
    let fastNext : Zlib.Inffast.L := { fastLocal with
      hold := fastLocal.hold >>> count.toUInt64,
      bits := fastLocal.bits - count }
    FastInputPacket h slowNext bs fastNext ∧
      DispatchBuffers h r slowNext bs ∧
      stream slowNext bs = (stream slow bs).drop count.toNat ∧
      slowNext.bits.toNat = slow.bits.toNat - count.toNat := by
  have dropped := DROPBITS_inv packet.source count within small
  let slowNext : IL := { slow with
    hold := slow.hold >>> count.toUInt64,
    bits := slow.bits - count }
  let fastNext : Zlib.Inffast.L := { fastLocal with
    hold := fastLocal.hold >>> count.toUInt64,
    bits := fastLocal.bits - count }
  have nextPacket : FastInputPacket h slowNext bs fastNext :=
    ⟨dropped.1, packet.cursor,
      by simp only [fastNext, slowNext, packet.hold],
      by simp only [fastNext, slowNext, packet.bits]⟩
  have outputNext : OutputCursorInvariant h r slowNext :=
    ⟨buffers.output.range, buffers.output.nonnull,
      buffers.output.count, buffers.output.produced⟩
  have nextBuffers : DispatchBuffers h r slowNext bs :=
    ⟨buffers.input, outputNext, buffers.separate, dropped.1⟩
  exact ⟨nextPacket, nextBuffers, dropped.2.1, dropped.2.2⟩

end Zlib.Inflate.Proofs
