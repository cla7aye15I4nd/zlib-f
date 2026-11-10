import ZlibF.Proof.«inflate.c.fast-view-invalid-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The translated match copier preserves the default decoder relation on
both valid distances and the invalid-distance transition to BAD. -/
theorem FastInputPacket.copyMatch_default_state
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow bs l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    (streamPtr : c.strm = some r)
    (statePtr : c.state = some (.tab zs))
    (left : slow.left ≠ 0)
    (length : 3 ≤ l.len.toNat)
    (whaveBound : c.whave.toNat ≤ c.wsize.toNat)
    (wnextBound : c.wnext.toNat ≤ c.wsize.toNat)
    (wsizeBound : c.wsize.toNat ≤ 32768)
    {dest : BRef} {output : Array UInt8} {oo j : Nat}
    (outPtr : l.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (outputRoom : oo ≤ j ∧
      j + l.len.toNat ≤ oo + slow.left.toNat)
    (produced : l.op.toNat ≤ j)
    (windowData : l.dist > l.op →
      ¬ l.dist - l.op > c.whave →
      ∃ (window : BRef) (saved : Array UInt8) (woff : Nat),
        window ≠ dest ∧
        c.window = .ref window woff ∧
        Space.get h window = some saved ∧
        woff + c.wsize.toNat ≤ saved.size) :
    ∃ result after,
      C.run (Zlib.Inffast.copyMatch c l) h = .ok (result, after) ∧
      FastInputPacket after slow bs result ∧
      DispatchBuffers after r slow bs ∧
      ByteViewSizes h after ∧
      result.againD = l.againD ∧
      result.againL = l.againL ∧
      ((∃ i, result.broke = true ∧
        after = setI
          (r.put h { z with msg := .ref (.str i) 0 }) zs
          { s with mode := BAD } ∧
        DefaultStateJ after r zs
          { z with msg := .ref (.str i) 0 } { s with mode := BAD } ∧
        Space.get after dest = some output ∧
        Space.ro after dest = false) ∨
       (∃ array, result.broke = l.broke ∧
        DefaultStateJ after r zs z s ∧
        result.out = .ref dest (j + l.len.toNat) ∧
        Space.get after dest = some array ∧
        array.size = output.size ∧
        Space.ro after dest = false ∧
        after = Space.put h dest array ∧
        BufferFrame h after (fun _ => False)
          [⟨slow.put, slow.left.toNat⟩])) := by
  by_cases windowBranch : l.dist > l.op
  · by_cases invalidBack : l.dist - l.op > c.whave
    · obtain ⟨i, after, run, heapEq, resultPacket,
          nextInvariant, nextBuffers, sizes, bytes, write⟩ :=
        packet.copyMatch_invalid_default_state invariant buffers
          streamPtr statePtr windowBranch invalidBack
          outputGet outputWrite
      exact ⟨{ l with op := l.dist - l.op, broke := true },
        after, run, resultPacket, nextBuffers, sizes, rfl, rfl,
        Or.inl ⟨i, rfl, heapEq, nextInvariant, bytes, write⟩⟩
    · obtain ⟨result, after, array, run, resultPacket,
          nextInvariant, nextBuffers, sizes, out, broke,
          againD, againL, bytes, size, write, heapEq, frame⟩ :=
        packet.copyMatch_valid_default_state invariant buffers
          left length whaveBound wnextBound wsizeBound
          outPtr outputPtr outputGet outputWrite outputSize
          outputRoom produced (fun _ => invalidBack) windowData
      exact ⟨result, after, run, resultPacket, nextBuffers,
        sizes, againD, againL,
        Or.inr ⟨array, broke, nextInvariant, out, bytes,
          size, write, heapEq, frame⟩⟩
  · obtain ⟨result, after, array, run, resultPacket,
        nextInvariant, nextBuffers, sizes, out, broke,
        againD, againL, bytes, size, write, heapEq, frame⟩ :=
      packet.copyMatch_valid_default_state invariant buffers
        left length whaveBound wnextBound wsizeBound
        outPtr outputPtr outputGet outputWrite outputSize
        outputRoom produced
        (fun selected => False.elim (windowBranch selected))
        windowData
    exact ⟨result, after, run, resultPacket, nextBuffers,
      sizes, againD, againL,
      Or.inr ⟨array, broke, nextInvariant, out, bytes,
        size, write, heapEq, frame⟩⟩

end Zlib.Inflate.Proofs
