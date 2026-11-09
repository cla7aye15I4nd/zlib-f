import ZlibF.Proof.«inflate.c.local-fast-input-frame»
import ZlibF.Proof.«inflate.c.fast-memory-shape-source»

namespace Zlib.Inflate.Local
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- The loop's ghost registers use the physical fast input cursor and
retain the original output capacity until the actual callee writeback. -/
def canonicalFastSlow (slow : IL) (result : Zlib.Inffast.L) (pulled : Nat) : IL :=
  { slow with
    next := result.in_
    have_ := UInt32.ofNat (slow.have_.toNat - pulled)
    hold := result.hold
    bits := result.bits }

/-- Reconstruct the internal packet from an actual body run and its
source-proved effects. The old existential packet supplies only its checked
held-bit bound; no equality of arbitrary ghost output fields is assumed. -/
theorem canonical_fast_body_packet
    {h after : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z zNext : ZStream} {s sNext : InflateState} {slow : IL} {bs : List UInt8}
    {initial result : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {dest : BRef} {output : Array UInt8} {oo start : Nat}
    {witness : IL} {witnessBytes : List UInt8}
    (invariant : LocalStateJ h cutoff r zs z s)
    (current : LocalStateJ after cutoff r zs zNext sNext)
    (buffers : DispatchBuffers h r slow bs)
    (initialPacket : FastInputPacket h slow bs initial)
    (finalPacket : FastInputPacket after witness witnessBytes result)
    (streamPtr : c.strm = some r)
    (run : C.run (Zlib.Inffast.inflate_fast_body c initial) h = .ok (result, after))
    (effect : FastExecEffect h after r zs z s slow dest start initial result 6 258)
    (sizes : ByteViewSizes h after)
    (outputPtr : slow.put = .ref dest oo) (outputGet : Space.get h dest = some output)
    (margin : 6 ≤ slow.have_.toNat) (bitsBound : slow.bits.toNat ≤ 30) :
    ∃ pulled, pulled ≤ 6 ∧ pulled ≤ bs.length ∧
      let regs := canonicalFastSlow slow result pulled
      FastInputPacket after regs (bs.drop pulled) result ∧
      DispatchBuffers after r regs (bs.drop pulled) ∧
      regs.next = inputAdvance slow.next pulled ∧
      regs.have_.toNat + pulled = slow.have_.toNat ∧
      regs.put = slow.put ∧ regs.left = slow.left ∧ regs.out_ = slow.out_ ∧
      regs.bits.toNat ≤ slow.bits.toNat + 8 * pulled ∧
      (result.broke = false → regs.bits.toNat ≤ 30) := by
  obtain ⟨pulled, pulledBound, cursor, budget⟩ := effect.input
  have usedBound : pulled ≤ bs.length := by rw [← buffers.bits.have_eq]; omega
  let regs := canonicalFastSlow slow result pulled
  have remainingWidth : slow.have_.toNat - pulled < 2 ^ 32 := by
    have := UInt32.toNat_lt slow.have_
    omega
  have count : regs.have_.toNat + pulled = slow.have_.toNat := by
    change (UInt32.ofNat (slow.have_.toNat - pulled)).toNat + pulled = _
    rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt remainingWidth]
    omega
  have next : regs.next = inputAdvance slow.next pulled := by
    change result.in_ = _
    rw [← initialPacket.cursor]
    exact cursor
  have held : regs.hold.toNat < 2 ^ regs.bits.toNat := by
    change result.hold.toNat < 2 ^ result.bits.toNat
    rw [finalPacket.hold, finalPacket.bits]
    exact finalPacket.source.hold_lt
  have narrow := effect.heap.output_effect.buffer_frame invariant.good.live.hz invariant.good.live.hs
  have frame : BufferFrame h after (fun b => StreamRoot r b ∨ InflateOwned zs s b)
      [⟨slow.put, slow.left.toNat⟩] := by
    apply bufferFrame_weaken (frame := narrow)
    intro b changed
    rcases changed with root | state
    · exact Or.inl root
    · exact Or.inr (Or.inl state)
  have memoryFacts := fastMemoryMetaFrameM_fast_body r c streamPtr initial h result after run
  simp only [FastMemoryMetaFrame, fastMemoryMeta, Prod.mk.injEq] at memoryFacts
  have readonly : ∀ ref : BRef, Space.ro after ref = Space.ro h ref := by
    intro ref
    cases ref <;> simp only [Space.ro, memoryFacts.1]
  have window := (effect.heap.window_mode invariant.good.live.hs current).1
  have packet : DispatchBuffers after r regs (bs.drop pulled) :=
    output_frame_advance_packet buffers invariant current.good window sizes readonly outputPtr outputGet
      frame next count (by change slow.put = inputAdvance slow.put 0; rw [inputAdvance_zero])
      (made := 0) (by change slow.left.toNat + 0 = slow.left.toNat; omega) rfl held
  refine ⟨pulled, pulledBound, usedBound, ⟨packet.bits, rfl, rfl, rfl⟩, packet,
    next, count, rfl, rfl, rfl, ?_, ?_⟩
  · change result.bits.toNat ≤ slow.bits.toNat + 8 * pulled
    rw [← initialPacket.bits]
    exact budget
  · intro notBroken
    change result.bits.toNat ≤ 30
    have bounded := effect.held notBroken
    rw [initialPacket.bits] at bounded
    omega

end Zlib.Inflate.Local
