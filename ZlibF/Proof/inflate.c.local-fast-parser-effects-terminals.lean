import ZlibF.Proof.«inflate.c.local-fast-parser-dolen-literal-invariant»
import ZlibF.Proof.«inflate.c.local-fast-parser-dolen-end-invariant»
import ZlibF.Proof.«inflate.c.local-fast-parser-dolen-invalid-invariant»
import ZlibF.Proof.«inflate.c.local-fast-copy-distance-effects-common»

namespace Zlib.Inflate.Local
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Inffast.Spec ZlibF.Spec.Public
set_option autoImplicit false

theorem FastInputPacket.dolen_literal_effect
    {h : Heap} {cutoff : Nat} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow bs l)
    (invariant : LocalStateJ h cutoff r zs z s)
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
    (guard : C.run (Ptr.lt l.out c.end_) h = .ok (true, h))
    {result : Zlib.Inffast.L} {after : Heap}
    (observed : C.run (Zlib.Inffast.dolen c l) h = .ok (result, after)) :
    FastExecEffect h after r zs z s slow dest j l result 0 1 := by
  obtain ⟨run, _, finalPacket, _, _, _, source, _, _, frame⟩ :=
    Zlib.Inflate.Local.FastInputPacket.dolen_literal_local_state packet invariant buffers
      herePtr lenGet indexBound codeFits codeWidth literal left avail outPtr outputPtr
      endPtr outputGet outputWrite outputSize current guard
  rw [run] at observed
  cases observed
  have budget : (l.bits - lenCodes[index].bits.toUInt32).toNat ≤ l.bits.toNat := by
    rw [UInt32.toNat_sub_of_le _ _ (by
      rw [UInt32.le_iff_toNat_le, packet.bits, UInt8.toNat_toUInt32]
      exact codeFits)]
    omega
  refine ⟨Or.inl ⟨_, rfl, frame, rfl⟩, ⟨j + 1, rfl, by omega, by omega⟩,
    ?_, ⟨0, by omega, ?_, ?_⟩, ?_⟩
  · intro _
    exact ⟨j + 1, rfl, by omega⟩
  · exact (inputAdvance_zero l.in_).symm
  · simpa only [Nat.mul_zero, Nat.add_zero] using budget
  · intro _
    exact Nat.le_trans budget (Nat.le_max_left _ _)

theorem FastInputPacket.dolen_end_leaf_effect
    {h : Heap} {cutoff : Nat} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow bs l)
    (invariant : LocalStateJ h cutoff r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    (statePtr : c.state = some (.tab zs))
    (mode : DataTableMode s.mode)
    {codeRef : CodeRef} {codes : Array Code} {index : Nat}
    (herePtr : l.here = .ref codeRef index)
    (codesGet : Space.get h codeRef = some codes)
    (codeIndex : index < codes.size)
    (codeBits : codes[index].bits.toNat ≤ slow.bits.toNat)
    (codeWidth : codes[index].bits.toNat ≤ 15)
    (nonzero : codes[index].op ≠ 0)
    (notBase : (codes[index].op.toUInt32 &&& 16 != 0) = false)
    (notLink : (codes[index].op.toUInt32 &&& 64 == 0) = false)
    (endCode : (codes[index].op.toUInt32 &&& 32 != 0) = true)
    {dest : BRef} {j : Nat} (outPtr : l.out = .ref dest j)
    {result : Zlib.Inffast.L} {after : Heap}
    (observed : C.run (Zlib.Inffast.dolen c l) h = .ok (result, after)) :
    FastExecEffect h after r zs z s slow dest j l result 0 0 := by
  obtain ⟨result0, slowNext, run, broke, _, input, output, finalPacket, _, _, _, source⟩ :=
    Zlib.Inflate.Local.FastInputPacket.dolen_end_leaf_local_state packet invariant buffers
      statePtr mode herePtr codesGet codeIndex codeBits codeWidth nonzero notBase notLink endCode
  have budget : result0.bits.toNat ≤ l.bits.toNat := by
    have lengths := congrArg List.length source
    simp only [stream, List.length_append, natBits_length, bytesBits_length, List.length_drop] at lengths
    rw [finalPacket.bits, packet.bits]
    omega
  rw [run] at observed
  cases observed
  refine ⟨Or.inr (Or.inr ⟨broke, rfl⟩), ⟨j, output.trans outPtr, by omega, by omega⟩,
    ?_, ⟨0, by omega, ?_, ?_⟩, ?_⟩
  · intro notBroken
    rw [broke] at notBroken
    contradiction
  · simpa only [inputAdvance_zero] using input
  · simpa only [Nat.mul_zero, Nat.add_zero] using budget
  · intro notBroken
    rw [broke] at notBroken
    contradiction

theorem FastInputPacket.dolen_invalid_leaf_effect
    {h : Heap} {cutoff : Nat} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow bs l)
    (invariant : LocalStateJ h cutoff r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    (streamPtr : c.strm = some r)
    (statePtr : c.state = some (.tab zs))
    {codeRef : CodeRef} {codes : Array Code} {index : Nat}
    (herePtr : l.here = .ref codeRef index)
    (codesGet : Space.get h codeRef = some codes)
    (codeIndex : index < codes.size)
    (codeBits : codes[index].bits.toNat ≤ slow.bits.toNat)
    (codeWidth : codes[index].bits.toNat ≤ 15)
    (nonzero : codes[index].op ≠ 0)
    (notBase : (codes[index].op.toUInt32 &&& 16 != 0) = false)
    (notLink : (codes[index].op.toUInt32 &&& 64 == 0) = false)
    (notEnd : (codes[index].op.toUInt32 &&& 32 != 0) = false)
    {dest : BRef} {j : Nat} (outPtr : l.out = .ref dest j)
    {result : Zlib.Inffast.L} {after : Heap}
    (observed : C.run (Zlib.Inffast.dolen c l) h = .ok (result, after)) :
    FastExecEffect h after r zs z s slow dest j l result 0 0 := by
  obtain ⟨i, after0, result0, slowNext, run, heapEq, broke, _, input, output,
    finalPacket, _, _, _, source⟩ :=
    Zlib.Inflate.Local.FastInputPacket.dolen_invalid_leaf_local_state packet invariant buffers
      streamPtr statePtr herePtr codesGet codeIndex codeBits codeWidth nonzero notBase notLink notEnd
  have budget : result0.bits.toNat ≤ l.bits.toNat := by
    have lengths := congrArg List.length source
    simp only [stream, List.length_append, natBits_length, bytesBits_length, List.length_drop] at lengths
    rw [finalPacket.bits, packet.bits]
    omega
  rw [run] at observed
  cases observed
  refine ⟨Or.inr (Or.inl ⟨i, broke, heapEq⟩), ⟨j, output.trans outPtr, by omega, by omega⟩,
    ?_, ⟨0, by omega, ?_, ?_⟩, ?_⟩
  · intro notBroken
    rw [broke] at notBroken
    contradiction
  · simpa only [inputAdvance_zero] using input
  · simpa only [Nat.mul_zero, Nat.add_zero] using budget
  · intro notBroken
    rw [broke] at notBroken
    contradiction

end Zlib.Inflate.Local
