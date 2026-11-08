import ZlibF.Proof.«inflate.c.fast-view-window-cases»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- A valid translated `copyMatch` returns a synchronized packet and a
writable output view of the original size. Window facts are needed only when
the distance actually reaches into the window. -/
theorem FastInputPacket.copyMatch_valid_view
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    (packet : FastInputPacket h slow bs l)
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
    (distanceValid : l.dist > l.op →
      ¬ l.dist - l.op > c.whave)
    (windowData : l.dist > l.op →
      ¬ l.dist - l.op > c.whave →
      ∃ (window : BRef) (saved : Array UInt8) (woff : Nat),
        window ≠ dest ∧
        c.window = .ref window woff ∧
        Space.get h window = some saved ∧
        woff + c.wsize.toNat ≤ saved.size) :
    ∃ result after array,
      C.run (Zlib.Inffast.copyMatch c l) h =
        .ok (result, after) ∧
      FastInputPacket after slow bs result ∧
      result.out = .ref dest (j + l.len.toNat) ∧
      result.broke = l.broke ∧
      result.againD = l.againD ∧
      result.againL = l.againL ∧
      Space.get after dest = some array ∧
      array.size = output.size ∧
      Space.ro after dest = false := by
  by_cases windowBranch : l.dist > l.op
  · obtain ⟨window, saved, woff, different,
        windowPtr, windowGet, windowSize⟩ :=
      windowData windowBranch (distanceValid windowBranch)
    exact packet.copyMatch_window_valid_view
      separate left windowBranch (distanceValid windowBranch)
      whaveBound wnextBound wsizeBound different
      windowPtr windowGet windowSize outPtr outputPtr
      outputGet outputWrite outputSize outputRoom produced
  · have distance : l.dist.toNat ≤ j := by
      have hnot : ¬ l.op.toNat < l.dist.toNat := by
        intro hlt
        exact windowBranch (UInt32.lt_iff_toNat_lt.mpr hlt)
      omega
    obtain ⟨result, after, run, resultPacket,
        resultEq, bytes, write⟩ :=
      packet.copyMatch_direct_view separate left windowBranch
        distance length outPtr outputPtr outputGet
        outputWrite outputSize outputRoom
    exact ⟨result, after,
      Zlib.Inffast.Proofs.cpyN l.len.toNat
        (j - l.dist.toNat) j output,
      run, resultPacket, by rw [resultEq],
      by rw [resultEq], by rw [resultEq],
      by rw [resultEq], bytes,
      Zlib.Inffast.Proofs.cpyN_size _ _ _ _, write⟩

end Zlib.Inflate.Proofs
