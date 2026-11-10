import ZlibF.Proof.«inflate.c.stored-block-producer»
import ZlibF.Proof.«inflate.c.input-base-modes»

namespace Zlib.Inflate.Proofs.StoredBlockProducer
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.StoredHistory Zlib.Inflate.Proofs.WrapperGlue
open Zlib.Inflate.Proofs.StoredGeneric
set_option autoImplicit false

/-- COPY_ preserves both saved per-call counter bases. Its uncredited
output count grows by exactly the actual copied amount, even when earlier
blocks already wrote bytes in this call. -/
theorem stored_inline_copy_register_ledger
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {l regs : IL} {bs : List UInt8}
    {outcome : Except Ex Unit} {made : Nat}
    (packet : DispatchBuffers h r l bs)
    (actual : runX (inflate_COPY_ c) l h = .ok ((outcome, regs), after))
    (count : regs.left.toNat + made = l.left.toNat) :
    regs.out_ = l.out_ ∧ regs.in_ = l.in_ ∧
      (regs.out_ - regs.left).toNat = (l.out_ - l.left).toNat + made := by
  have outBase := outputBaseX_inflate_COPY_ l.out_ c l h outcome regs after rfl actual
  have inBase := inputBaseX_inflate_COPY_ l.in_ c l h outcome regs after rfl actual
  refine ⟨outBase, inBase, ?_⟩
  have oldBound := packet.output.count
  have nextBound : regs.left.toNat ≤ regs.out_.toNat := by rw [outBase]; omega
  rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr nextBound),
    UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr oldBound), outBase]
  omega

/-- Closed arbitrary-capacity stored copying produces the physical new
output slice and its common uncredited-count ledger. The exact prior Adler
credit remains unchanged until actual CHECK or leave; already-written
current-call bytes are counted separately from the new payload prefix. -/
theorem stored_inline_copy_output_ledger
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs future payload credited : List UInt8} {rest : List Bool}
    (E : Env c h r zs z s) (initial : DefaultOriginState h r zs z s)
    (packet : DispatchBuffers h r l bs) (mode : s.mode = COPY_)
    (length : s.length.toNat = payload.length) (credit : AdlerCredit z s credited)
    (source : readBytes payload.length (bytesBits (bs ++ future)) = some (payload, rest)) :
    ∃ outcome regs after state made,
      made ≤ bs.length ∧ made ≤ payload.length ∧
      runX (inflate_COPY_ c) l h = .ok ((outcome, regs), after) ∧
      DefaultOriginState after r zs z state ∧ DispatchBuffers after r regs (bs.drop made) ∧
      BufferFrame h after (fun b => StreamRoot r b ∨ b = zs) [⟨l.put, made⟩] ∧
      Bytes after l.put made (payload.take made) ∧
      regs.next = inputAdvance l.next made ∧ regs.have_.toNat + made = l.have_.toNat ∧
      regs.put = inputAdvance l.put made ∧ regs.left.toNat + made = l.left.toNat ∧
      regs.out_ = l.out_ ∧ regs.in_ = l.in_ ∧
      (regs.out_ - regs.left).toNat = (l.out_ - l.left).toNat + made ∧
      state.length.toNat + made = payload.length ∧ AdlerCredit z state credited ∧
      readBytes (payload.length - made) (bytesBits (bs.drop made ++ future)) =
        some (payload.drop made, rest) ∧
      ∃ ref off array,
        l.put = .ref ref off ∧ regs.put = .ref ref (off + made) ∧
        Space.get after ref = some array ∧ off + made ≤ array.size ∧
        ZlibF.Math.LZ77Copy.writtenBytes array (off + made) made = payload.take made := by
  obtain ⟨outcome, regs, after, state, made, bound, payloadBound, actual, current, currentPacket,
    copied, frame, next, haveCount, put, leftCount, _bits, _hold, debt, currentCredit,
    continuation, _kinds⟩ := stored_payload_phase_consumer E initial packet mode length credit source
  obtain ⟨outBase, inBase, amount⟩ := stored_inline_copy_register_ledger packet actual leftCount
  refine ⟨outcome, regs, after, state, made, bound, payloadBound, actual, current, currentPacket,
    frame, copied, next, haveCount, put, leftCount, outBase, inBase, amount,
    debt, currentCredit, continuation, ?_⟩
  rcases copied with ⟨null, _zero, _empty⟩ | ⟨ref, off, array, pointer, get, room, values⟩
  · exact False.elim (packet.output.nonnull null)
  · refine ⟨ref, off, array, pointer, ?_, get, room, ?_⟩
    · rw [put, pointer]; rfl
    · have observed : Bytes after (.ref ref ((off + made) - made)) made (payload.take made) := by
        rw [Nat.add_sub_cancel]
        exact Or.inr ⟨ref, off, array, rfl, get, room, values⟩
      exact (writtenBytes_matches_output get (by omega) room observed).symm

#print axioms stored_inline_copy_register_ledger
#print axioms stored_inline_copy_output_ledger
end Zlib.Inflate.Proofs.StoredBlockProducer
