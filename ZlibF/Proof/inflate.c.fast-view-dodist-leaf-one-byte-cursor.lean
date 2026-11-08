import ZlibF.Proof.«inflate.c.fast-view-dodist-leaf-one-byte-invariant»
import ZlibF.Proof.«inflate.c.fast-view-pull-count-account»
import ZlibF.Proof.«inffast.c.dist-bit-ledger»
import ZlibF.Proof.«inffast.c.flags»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- A base-distance table entry with five bits left after its code uses at
most one caller byte in the translated refill/copy suffix. -/
theorem FastInputPacket.dodist_base_leaf_one_byte_input_cursor
    {h : Heap} {slow : IL} {first : UInt8}
    {rest : List UInt8} {l : Zlib.Inffast.L}
    {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow (first :: rest) l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow (first :: rest))
    (streamPtr : c.strm = some r)
    (statePtr : c.state = some (.tab zs))
    (whaveEq : c.whave = s.whave)
    (wsizeEq : c.wsize = s.wsize)
    (wnextEq : c.wnext = s.wnext)
    (windowEq : c.window = s.window)
    {codeRef : CodeRef} {codes : Array Code} {index : Nat}
    (herePtr : l.here = .ref codeRef index)
    (codesGet : Space.get h codeRef = some codes)
    (codeIndex : index < codes.size)
    (codeBits : codes[index].bits.toNat ≤ slow.bits.toNat)
    (codeWidth : codes[index].bits.toNat ≤ 15)
    (held : 5 + codes[index].bits.toNat ≤ slow.bits.toNat)
    (base : (codes[index].op.toUInt32 &&& 16 != 0) = true)
    (extraBound : (codes[index].op.toUInt32 &&& 15).toNat ≤ 13)
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
    (guard : C.run (Ptr.lt l.out c.end_) h = .ok (true, h)) :
    ∃ used slowNext result after,
      used ≤ 1 ∧
      C.run (Zlib.Inffast.dodist c l) h = .ok (result, after) ∧
      FastDistancePost h after r zs z s slowNext
        ((first :: rest).drop used) result
        dest output j l.len.toNat ∧
      stream slowNext ((first :: rest).drop used) =
        ((stream slow (first :: rest)).drop
          codes[index].bits.toNat).drop
            (codes[index].op.toUInt32 &&& 15).toNat ∧
      result.in_ = inputAdvance l.in_ used := by
  obtain ⟨used, slowNext, result, after, usedBound,
    run, post, source⟩ :=
    packet.dodist_base_leaf_one_byte_default_state invariant buffers
      streamPtr statePtr whaveEq wsizeEq wnextEq windowEq
      herePtr codesGet codeIndex codeBits codeWidth held base extraBound
      left avail length outPtr outputPtr begPtr endPtr outputGet
      outputWrite outputSize current beginLe span guard
  have loaded : Ptr.load l.here h = .ok (codes[index], h) := by
    rw [herePtr]
    exact Ptr.load_ok codesGet codeIndex
  obtain ⟨pulled, pulledBound, cursor, bits⟩ :=
    Zlib.Inffast.Proofs.dodist_base_one_pull_bit_ledger
      loaded codeWidth (by rw [packet.bits]; exact held)
      base extraBound (by simpa only [C.run] using run)
  have usedLength : used ≤ (first :: rest).length := by simp; omega
  have pulledLength : pulled ≤ (first :: rest).length := by simp; omega
  have budget : slowNext.bits.toNat +
      (codes[index].bits.toNat + (codes[index].op.toUInt32 &&& 15).toNat) =
      slow.bits.toNat + 8 * pulled := by
    rw [post.1.bits, packet.bits] at bits
    omega
  have trace : stream slowNext ((first :: rest).drop used) =
      (stream slow (first :: rest)).drop
        (codes[index].bits.toNat + (codes[index].op.toUInt32 &&& 15).toNat) := by
    simpa only [List.drop_drop] using source
  have count : used = pulled :=
    stream_pull_count_eq usedLength pulledLength trace budget
  exact ⟨used, slowNext, result, after, usedBound,
    run, post, source, by rw [count]; exact cursor⟩

#print axioms FastInputPacket.dodist_base_leaf_one_byte_input_cursor
end Zlib.Inflate.Proofs
