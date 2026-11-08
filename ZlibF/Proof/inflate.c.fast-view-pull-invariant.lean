import ZlibF.Proof.«inflate.c.fast-view-dist-cont-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- A translated fast input pull advances the public caller range and keeps
the complete default state and unread-input packet. -/
theorem FastInputPacket.pull_default_state
    {h : Heap} {slow : IL} {b : UInt8} {bs : List UInt8}
    {fastLocal : Zlib.Inffast.L}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow (b :: bs) fastLocal)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow (b :: bs))
    (small : slow.bits.toNat ≤ 22) :
    ∃ next fastNext slowNext,
      C.run (Zlib.Inffast.pull fastLocal) h = .ok (fastNext, h) ∧
      next = inputAdvance slow.next 1 ∧
      slowNext = pulled slow b next ∧
      fastNext = Zlib.Inffast.Proofs.pullL fastLocal b next ∧
      FastInputPacket h slowNext bs fastNext ∧
      DefaultStateJ h r zs z s ∧
      DispatchBuffers h r slowNext bs ∧
      stream slowNext bs = stream slow (b :: bs) := by
  obtain ⟨next, fastNext, slowNext, run, nextEq,
    slowEq, fastEq, nextPacket, sameStream⟩ := packet.pull small
  have used : slowNext.have_.toNat + 1 = slow.have_.toNat := by
    rw [slowEq]
    have count := packet.source.have_eq
    simp only [pulled, List.length_cons] at count ⊢
    rw [UInt32.toNat_sub_of_le _ _
      (by rw [UInt32.le_iff_toNat_le]; simp; omega)]
    simp only [UInt32.toNat_ofNat] at *
    omega
  have nextBuffers : DispatchBuffers h r slowNext bs :=
    buffers.advance_both invariant.good invariant.good rfl
      (ByteViewSizes.refl h) (fun _ => rfl)
      (by rw [slowEq, nextEq]; rfl) used
      (by rw [slowEq]; exact (inputAdvance_zero slow.put).symm)
      (by rw [slowEq]; rfl)
      (by rw [slowEq]; rfl) nextPacket.source
  exact ⟨next, fastNext, slowNext, run, nextEq,
    slowEq, fastEq, nextPacket, invariant, nextBuffers,
    sameStream⟩

end Zlib.Inflate.Proofs
