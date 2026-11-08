import ZlibF.Proof.«inflate.c.fast-view-window-cases-invariant»
import ZlibF.Proof.«inflate.c.fast-view-direct-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Every valid translated `copyMatch` branch retains the default state,
caller buffers, exact output heap update and caller output frame. -/
theorem FastInputPacket.copyMatch_valid_default_state
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow bs l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs)
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
      DefaultStateJ after r zs z s ∧
      DispatchBuffers after r slow bs ∧
      ByteViewSizes h after ∧
      result.out = .ref dest (j + l.len.toNat) ∧
      result.broke = l.broke ∧
      result.againD = l.againD ∧
      result.againL = l.againL ∧
      Space.get after dest = some array ∧
      array.size = output.size ∧
      Space.ro after dest = false ∧
      after = Space.put h dest array ∧
      BufferFrame h after (fun _ => False)
        [⟨slow.put, slow.left.toNat⟩] := by
  by_cases windowBranch : l.dist > l.op
  · obtain ⟨window, saved, woff, different,
        windowPtr, windowGet, windowSize⟩ :=
      windowData windowBranch (distanceValid windowBranch)
    exact packet.copyMatch_window_valid_default_state
      invariant buffers left windowBranch
      (distanceValid windowBranch)
      whaveBound wnextBound wsizeBound different
      windowPtr windowGet windowSize outPtr outputPtr
      outputGet outputWrite outputSize outputRoom produced
  · have distance : l.dist.toNat ≤ j := by
      have hnot : ¬ l.op.toNat < l.dist.toNat := by
        intro hlt
        exact windowBranch (UInt32.lt_iff_toNat_lt.mpr hlt)
      omega
    obtain ⟨result, after, run, resultPacket,
        resultInvariant, resultBuffers, sizes, resultEq,
        bytes, write, heapEq, frame⟩ :=
      packet.copyMatch_direct_default_state invariant buffers
        left windowBranch distance length outPtr outputPtr
        outputGet outputWrite outputSize outputRoom
    exact ⟨result, after,
      Zlib.Inffast.Proofs.cpyN l.len.toNat
        (j - l.dist.toNat) j output,
      run, resultPacket, resultInvariant, resultBuffers, sizes,
      by rw [resultEq], by rw [resultEq],
      by rw [resultEq], by rw [resultEq], bytes,
      Zlib.Inffast.Proofs.cpyN_size _ _ _ _, write,
      heapEq, frame⟩

end Zlib.Inflate.Proofs
