import ZlibF.Proof.«inflate.c.local-fast-parser-effects-terminals»
import ZlibF.Proof.«inflate.c.local-fast-exact-output-interface»
import ZlibF.Proof.«inflate.c.fast-view-terminal-frame»
import ZlibF.Proof.«inflate.c.fast-view-bad-data-frame»

namespace Zlib.Inflate.Local
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Inffast.Spec ZlibF.Spec.Public
set_option autoImplicit false

theorem FastInputPacket.dolen_literal_exact_output
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
    FastExactOutput h after r zs dest j result := by
  obtain ⟨run, _, finalPacket, _, _, _, source, _, _, frame⟩ :=
    Zlib.Inflate.Local.FastInputPacket.dolen_literal_local_state packet invariant buffers
      herePtr lenGet indexBound codeFits codeWidth literal left avail outPtr outputPtr
      endPtr outputGet outputWrite outputSize current guard
  rw [run] at observed
  cases observed
  refine ⟨j + 1, rfl, by omega, ?_⟩
  have written : BufferFrame h (Space.put h dest (output.set! j lenCodes[index].val.toUInt8))
      (fun _ => False) [⟨.ref dest j, 1⟩] := by
    apply output_view_buffer_frame rfl outputGet outputWrite (by simp only [Array.size_set!])
    intro k outside
    have different : j ≠ k := by omega
    simp [Array.set!, different]
  have privateFrame := bufferFrame_weaken (wider := fun b => StreamRoot r b ∨ b = zs) (fun _ impossible => False.elim impossible) written
  simpa only [Nat.add_sub_cancel_left] using privateFrame

theorem FastInputPacket.dolen_end_leaf_exact_output
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
    FastExactOutput h after r zs dest j result := by
  obtain ⟨result0, slowNext, run, broke, _, input, output, finalPacket, _, _, _, source⟩ :=
    Zlib.Inflate.Local.FastInputPacket.dolen_end_leaf_local_state packet invariant buffers
      statePtr mode herePtr codesGet codeIndex codeBits codeWidth nonzero notBase notLink endCode
  rw [run] at observed
  cases observed
  refine ⟨j, output.trans outPtr, by omega, ?_⟩
  exact (fast_terminal_buffer_frame invariant.good.live.hz invariant.good.live.hs
    [⟨.ref dest j, j - j⟩]).1

theorem FastInputPacket.dolen_invalid_leaf_exact_output
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
    FastExactOutput h after r zs dest j result := by
  obtain ⟨i, after0, result0, slowNext, run, heapEq, broke, _, input, output,
    finalPacket, _, _, _, source⟩ :=
    Zlib.Inflate.Local.FastInputPacket.dolen_invalid_leaf_local_state packet invariant buffers
      streamPtr statePtr herePtr codesGet codeIndex codeBits codeWidth nonzero notBase notLink notEnd
  rw [run] at observed
  cases observed
  refine ⟨j, output.trans outPtr, by omega, ?_⟩
  rw [heapEq]
  exact (badHeap_buffer_frame invariant.good.live.hz invariant.good.live.hs i
    [⟨.ref dest j, j - j⟩]).1

end Zlib.Inflate.Local
