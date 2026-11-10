import ZlibF.Proof.«inflate.c.fast-view-invalid»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The translated `copyMatch` on a live sane stream either copies a valid
match or enters BAD for a distance beyond available history. -/
theorem FastInputPacket.copyMatch_view
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {s : InflateState}
    (packet : FastInputPacket h slow bs l)
    (good : Good h r zs z s)
    (streamPtr : c.strm = some r)
    (statePtr : c.state = some (.tab zs))
    (sane : s.sane ≠ 0)
    (separate : Separate slow.next slow.have_.toNat
      slow.put slow.left.toNat)
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
      C.run (Zlib.Inffast.copyMatch c l) h =
        .ok (result, after) ∧
      FastInputPacket after slow bs result ∧
      result.againD = l.againD ∧
      result.againL = l.againL ∧
      ((result.broke = true ∧
        ∃ i, after = setI
          (r.put h { z with msg := .ref (.str i) 0 }) zs
          { s with mode := BAD } ∧
          Space.get after dest = some output ∧
          Space.ro after dest = false) ∨
       (result.broke = l.broke ∧
        ∃ array,
          result.out = .ref dest (j + l.len.toNat) ∧
          Space.get after dest = some array ∧
          array.size = output.size ∧
          Space.ro after dest = false)) := by
  by_cases windowBranch : l.dist > l.op
  · by_cases invalidBack : l.dist - l.op > c.whave
    · obtain ⟨i, after, run, heapEq, resultPacket,
          bytes, write⟩ :=
        packet.copyMatch_invalid_view good streamPtr statePtr sane
          windowBranch invalidBack outputGet outputWrite
      exact ⟨{ l with op := l.dist - l.op, broke := true },
        after, run, resultPacket, rfl, rfl,
        Or.inl ⟨rfl, i, heapEq, bytes, write⟩⟩
    · obtain ⟨result, after, array, run, resultPacket,
          out, broke, againD, againL, bytes, size, write⟩ :=
        packet.copyMatch_valid_view separate left length
          whaveBound wnextBound wsizeBound outPtr outputPtr
          outputGet outputWrite outputSize outputRoom produced
          (fun _ => invalidBack) windowData
      exact ⟨result, after, run, resultPacket, againD,
        againL, Or.inr ⟨broke, array, out, bytes, size,
          write⟩⟩
  · obtain ⟨result, after, array, run, resultPacket,
        out, broke, againD, againL, bytes, size, write⟩ :=
      packet.copyMatch_valid_view separate left length
        whaveBound wnextBound wsizeBound outPtr outputPtr
        outputGet outputWrite outputSize outputRoom produced
        (fun h => False.elim (windowBranch h)) windowData
    exact ⟨result, after, run, resultPacket, againD,
      againL, Or.inr ⟨broke, array, out, bytes, size,
        write⟩⟩

end Zlib.Inflate.Proofs
