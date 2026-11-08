import ZlibF.Proof.«inflate.c.fast-view-window-cases-exact-frame»
import ZlibF.Proof.«inflate.c.fast-view-direct-exact-frame»
import ZlibF.Proof.«inflate.c.fast-view-copy-match-frame»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- A valid translated match changes only the output prefix through its
actual final cursor, for either window or direct copying. -/
theorem FastInputPacket.copyMatch_valid_exact_frame
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
        window ≠ dest ∧ c.window = .ref window woff ∧
        Space.get h window = some saved ∧
        woff + c.wsize.toNat ≤ saved.size) :
    ∃ result after,
      C.run (Zlib.Inffast.copyMatch c l) h = .ok (result, after) ∧
      result.out = .ref dest (j + l.len.toNat) ∧
      BufferFrame h after (fun b => StreamRoot r b ∨ b = zs)
        [⟨slow.put, j + l.len.toNat - oo⟩] := by
  by_cases windowBranch : l.dist > l.op
  · obtain ⟨window, saved, woff, different,
      windowPtr, windowGet, windowSize⟩ :=
      windowData windowBranch (distanceValid windowBranch)
    obtain ⟨result, after, array, run, _, _, _, _, out,
      _, _, _, bytes, _, _, _, broad, segment⟩ :=
      packet.copyMatch_window_valid_segment_frame
        invariant buffers left windowBranch
        (distanceValid windowBranch)
        whaveBound wnextBound wsizeBound different
        windowPtr windowGet windowSize outPtr outputPtr
        outputGet outputWrite outputSize outputRoom produced
    have narrow : BufferFrame h after (fun _ => False)
        [⟨slow.put, j + l.len.toNat - oo⟩] := by
      rw [outputPtr]
      exact BufferFrame.narrow_to_segment_end
        (by simpa only [outputPtr] using broad) outputGet
        bytes outputRoom.1 segment
    exact ⟨result, after, run, out,
      bufferFrame_weaken (fun _ impossible => False.elim impossible)
        narrow⟩
  · have distance : l.dist.toNat ≤ j := by
      have hnot : ¬ l.op.toNat < l.dist.toNat := by
        intro hlt
        exact windowBranch (UInt32.lt_iff_toNat_lt.mpr hlt)
      omega
    exact packet.copyMatch_direct_exact_frame invariant buffers
      left windowBranch distance length outPtr outputPtr
      outputGet outputWrite outputSize outputRoom

#print axioms FastInputPacket.copyMatch_valid_exact_frame

/-- Actual `copyMatch` writes only through its returned output cursor;
invalid distances preserve every output byte and return at the entry cursor. -/
theorem FastInputPacket.copyMatch_exact_frame
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
        window ≠ dest ∧ c.window = .ref window woff ∧
        Space.get h window = some saved ∧
        woff + c.wsize.toNat ≤ saved.size) :
    ∃ result after k,
      C.run (Zlib.Inffast.copyMatch c l) h = .ok (result, after) ∧
      result.out = .ref dest k ∧
      oo ≤ k ∧
      BufferFrame h after (fun b => StreamRoot r b ∨ b = zs)
        [⟨slow.put, k - oo⟩] := by
  by_cases windowBranch : l.dist > l.op
  · by_cases invalidBack : l.dist - l.op > c.whave
    · obtain ⟨i, after, run, heapEq, _, _, _, _, _, _⟩ :=
        packet.copyMatch_invalid_default_state invariant buffers
          streamPtr statePtr windowBranch invalidBack
          outputGet outputWrite
      refine ⟨{ l with op := l.dist - l.op, broke := true },
        after, j, run, ?_, outputRoom.1, ?_⟩
      · simpa only [outPtr]
      · rw [heapEq]
        exact (badHeap_buffer_frame invariant.good.live.hz
          invariant.good.live.hs i [⟨slow.put, j - oo⟩]).1
    · obtain ⟨result, after, run, out, frame⟩ :=
        packet.copyMatch_valid_exact_frame invariant buffers left
          length whaveBound wnextBound wsizeBound outPtr
          outputPtr outputGet outputWrite outputSize outputRoom
          produced (fun _ => invalidBack) windowData
      exact ⟨result, after, j + l.len.toNat, run, out,
        by omega, frame⟩
  · obtain ⟨result, after, run, out, frame⟩ :=
      packet.copyMatch_valid_exact_frame invariant buffers left
        length whaveBound wnextBound wsizeBound outPtr
        outputPtr outputGet outputWrite outputSize outputRoom
        produced (fun yes => False.elim (windowBranch yes))
        windowData
    exact ⟨result, after, j + l.len.toNat, run, out,
      by omega, frame⟩

#print axioms FastInputPacket.copyMatch_exact_frame

end Zlib.Inflate.Proofs
