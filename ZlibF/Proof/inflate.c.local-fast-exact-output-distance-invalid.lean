import ZlibF.Proof.«inflate.c.local-fast-parser-dodist-invalid-invariant»
import ZlibF.Proof.«inflate.c.local-fast-exact-output-interface»
import ZlibF.Proof.«inflate.c.fast-view-bad-data-frame»
namespace Zlib.Inflate.Local
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false
theorem FastInputPacket.dodist_invalid_leaf_exact_output
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
    (notBase : (codes[index].op.toUInt32 &&& 16 != 0) = false)
    (notLink : (codes[index].op.toUInt32 &&& 64 == 0) = false)
    {dest : BRef} {j : Nat} (outPtr : l.out = .ref dest j)
    {value : Zlib.Inffast.L} {finalHeap : Heap}
    (observed : C.run (Zlib.Inffast.dodist c l) h = .ok (value, finalHeap)) :
    FastExactOutput h finalHeap r zs dest j value := by
  obtain ⟨i, after, result, slowNext, run, heapEq, broke, _, cursor, out,
    nextPacket, _, _, _, source⟩ :=
    Zlib.Inflate.Local.FastInputPacket.dodist_invalid_leaf_local_state packet invariant buffers
      streamPtr statePtr herePtr codesGet codeIndex codeBits codeWidth notBase notLink
  have same := Prod.mk.inj (Except.ok.inj (run.symm.trans observed))
  rcases same with ⟨rfl, rfl⟩
  refine ⟨j, out.trans outPtr, by omega, ?_⟩
  rw [heapEq]
  exact (badHeap_buffer_frame invariant.good.live.hz invariant.good.live.hs i
    [⟨.ref dest j, j - j⟩]).1

end Zlib.Inflate.Local
