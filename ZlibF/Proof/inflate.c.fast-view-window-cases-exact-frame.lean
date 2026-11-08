import ZlibF.Proof.«inflate.c.fast-view-window-short-invariant»
import ZlibF.Proof.«inflate.c.fast-view-window-nowwrap-short-invariant»
import ZlibF.Proof.«inflate.c.fast-view-window-mixed-invariant»
import ZlibF.Proof.«inflate.c.fast-view-window-contiguous-mixed-invariant»
import ZlibF.Proof.«inflate.c.fast-view-array-segment-frame»
import ZlibF.Proof.«inflate.c.fast-view-window-wrapped-short-invariant»
import ZlibF.Proof.«inflate.c.fast-view-window-wrapped-two-invariant»
import ZlibF.Proof.«inflate.c.fast-view-window-wrapped-three-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The valid-window cases of translated `copyMatch` share one packet,
output-cursor, writable-view and buffer-size postcondition. -/
theorem FastInputPacket.copyMatch_window_valid_segment_frame
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow bs l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    (left : slow.left ≠ 0)
    (windowBranch : l.dist > l.op)
    (validBack : ¬ l.dist - l.op > c.whave)
    (whaveBound : c.whave.toNat ≤ c.wsize.toNat)
    (wnextBound : c.wnext.toNat ≤ c.wsize.toNat)
    (wsizeBound : c.wsize.toNat ≤ 32768)
    {window dest : BRef} (different : window ≠ dest)
    {saved output : Array UInt8} {woff oo j : Nat}
    (windowPtr : c.window = .ref window woff)
    (windowGet : Space.get h window = some saved)
    (windowSize : woff + c.wsize.toNat ≤ saved.size)
    (outPtr : l.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (outputRoom : oo ≤ j ∧
      j + l.len.toNat ≤ oo + slow.left.toNat)
    (produced : l.op.toNat ≤ j) :
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
        [⟨slow.put, slow.left.toNat⟩] ∧
      ArraySegmentFrame output array j l.len.toNat := by
  have backSize : (l.dist - l.op).toNat ≤ c.wsize.toNat := by
    have backLeWhave : (l.dist - l.op).toNat ≤ c.whave.toNat := by
      by_cases hle : (l.dist - l.op).toNat ≤ c.whave.toNat
      · exact hle
      · have hgt : c.whave.toNat < (l.dist - l.op).toNat := by
          omega
        exact False.elim (validBack (UInt32.lt_iff_toNat_lt.mpr hgt))
    omega
  have sumFits : c.wsize.toNat + c.wnext.toNat < 2 ^ 32 := by
    omega
  have finish {result : Zlib.Inffast.L} {after : Heap}
      {array : Array UInt8}
      (run : C.run (Zlib.Inffast.copyMatch c l) h =
        .ok (result, after))
      (resultPacket : FastInputPacket after slow bs result)
      (resultInvariant : DefaultStateJ after r zs z s)
      (resultBuffers : DispatchBuffers after r slow bs)
      (sizes : ByteViewSizes h after)
      (out : result.out = .ref dest (j + l.len.toNat))
      (broke : result.broke = l.broke)
      (againD : result.againD = l.againD)
      (againL : result.againL = l.againL)
      (bytes : Space.get after dest = some array)
      (size : array.size = output.size)
      (write : Space.ro after dest = false)
      (heapEq : after = Space.put h dest array)
      (frame : BufferFrame h after (fun _ => False)
        [⟨slow.put, slow.left.toNat⟩])
      (segment : ArraySegmentFrame output array j l.len.toNat) :
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
          [⟨slow.put, slow.left.toNat⟩] ∧
        ArraySegmentFrame output array j l.len.toNat :=
    ⟨result, after, array, run, resultPacket,
      resultInvariant, resultBuffers, sizes, out,
      broke, againD, againL, bytes, size, write, heapEq,
      frame, segment⟩
  by_cases noWrap : c.wnext = 0
  · by_cases mixed : l.dist - l.op < l.len
    · obtain ⟨result, after, run, resultPacket,
          resultInvariant, resultBuffers, sizes, resultEq,
          bytes, write, heapEq, frame⟩ :=
        packet.copyMatch_window_nowrap_mixed_default_state
          invariant buffers left windowBranch validBack noWrap backSize
          mixed different windowPtr windowGet windowSize outPtr
          outputPtr outputGet outputWrite outputSize outputRoom
          produced
      exact finish run resultPacket resultInvariant resultBuffers sizes (by rw [resultEq])
        (by rw [resultEq]) (by rw [resultEq])
        (by rw [resultEq]) bytes
        (by simp [Zlib.Inffast.Proofs.cpyN_size,
          Zlib.Inffast.Proofs.blitN_size]) write heapEq frame
        (by
          have seg := ArraySegmentFrame.blit_then_cpy saved
            (l.dist - l.op).toNat
            (l.len.toNat - (l.dist - l.op).toNat)
            (woff + (c.wsize.toNat - (l.dist - l.op).toNat))
            (j + (l.dist - l.op).toNat - l.dist.toNat) j output
          have hm : (l.dist - l.op).toNat < l.len.toNat :=
            UInt32.lt_iff_toNat_lt.mp mixed
          have count : (l.dist - l.op).toNat +
              (l.len.toNat - (l.dist - l.op).toNat) = l.len.toNat := by
            omega
          simpa only [count] using seg)
    · have wholeWindow : l.len.toNat ≤
          (l.dist - l.op).toNat := by
        have hnot : ¬ (l.dist - l.op).toNat < l.len.toNat := by
          intro hlt
          exact mixed (UInt32.lt_iff_toNat_lt.mpr hlt)
        omega
      obtain ⟨result, after, run, resultPacket,
          resultInvariant, resultBuffers, sizes, resultEq,
          bytes, write, heapEq, frame⟩ :=
        packet.copyMatch_window_nowrap_short_default_state
          invariant buffers left windowBranch validBack noWrap backSize
          wholeWindow different windowPtr windowGet windowSize
          outPtr outputPtr outputGet outputWrite outputSize
          outputRoom
      exact finish run resultPacket resultInvariant resultBuffers sizes (by rw [resultEq])
        (by rw [resultEq]) (by rw [resultEq])
        (by rw [resultEq]) bytes
        (by simp [Zlib.Inffast.Proofs.blitN_size]) write heapEq frame
        (ArraySegmentFrame.blit saved l.len.toNat
          (woff + (c.wsize.toNat - (l.dist - l.op).toNat)) j output)
  · by_cases wrap : c.wnext < l.dist - l.op
    · by_cases mixed : l.dist - l.op - c.wnext < l.len
      · by_cases third : c.wnext <
            l.len - (l.dist - l.op - c.wnext)
        · obtain ⟨result, after, run, resultPacket,
              resultInvariant, resultBuffers, sizes, resultEq,
          bytes, write, heapEq, frame⟩ :=
            packet.copyMatch_window_wrapped_three_default_state
              invariant buffers left windowBranch validBack noWrap wrap
              backSize sumFits mixed third different
              windowPtr windowGet windowSize outPtr outputPtr
              outputGet outputWrite outputSize outputRoom produced
          exact finish run resultPacket resultInvariant resultBuffers sizes (by rw [resultEq])
            (by rw [resultEq]) (by rw [resultEq])
            (by rw [resultEq]) bytes
            (by simp [Zlib.Inffast.Proofs.cpyN_size,
              Zlib.Inffast.Proofs.blitN_size]) write heapEq frame
            (by
              have wrapNat : c.wnext.toNat < (l.dist - l.op).toNat :=
                UInt32.lt_iff_toNat_lt.mp wrap
              have lastNat : (l.dist - l.op - c.wnext).toNat =
                  (l.dist - l.op).toNat - c.wnext.toNat :=
                Zlib.Inffast.Proofs.u32_toNat_sub (by omega)
              have split : (l.dist - l.op - c.wnext).toNat +
                  c.wnext.toNat = (l.dist - l.op).toNat := by
                omega
              have mixedNat : (l.dist - l.op - c.wnext).toNat <
                  l.len.toNat := UInt32.lt_iff_toNat_lt.mp mixed
              have thirdNat : c.wnext.toNat < l.len.toNat -
                  (l.dist - l.op - c.wnext).toNat := by
                have h := UInt32.lt_iff_toNat_lt.mp third
                rw [Zlib.Inffast.Proofs.u32_toNat_sub (by omega)] at h
                exact h
              have count : (l.dist - l.op - c.wnext).toNat +
                  c.wnext.toNat +
                  (l.len.toNat - (l.dist - l.op).toNat) =
                  l.len.toNat := by omega
              have nextAt : j + (l.dist - l.op - c.wnext).toNat +
                  c.wnext.toNat = j + (l.dist - l.op).toNat := by
                omega
              have seg := ArraySegmentFrame.blit_blit_cpy saved
                (l.dist - l.op - c.wnext).toNat c.wnext.toNat
                (l.len.toNat - (l.dist - l.op).toNat)
                (woff + (c.wsize.toNat + c.wnext.toNat -
                  (l.dist - l.op).toNat))
                woff (j + (l.dist - l.op).toNat - l.dist.toNat)
                j output
              simpa only [nextAt, count] using seg)
        · obtain ⟨result, after, run, resultPacket,
              resultInvariant, resultBuffers, sizes, resultEq,
          bytes, write, heapEq, frame⟩ :=
            packet.copyMatch_window_wrapped_two_default_state
              invariant buffers left windowBranch validBack noWrap wrap
              backSize sumFits mixed third different
              windowPtr windowGet windowSize outPtr outputPtr
              outputGet outputWrite outputSize outputRoom
          exact finish run resultPacket resultInvariant resultBuffers sizes (by rw [resultEq])
            (by rw [resultEq]) (by rw [resultEq])
            (by rw [resultEq]) bytes
            (by simp [Zlib.Inffast.Proofs.blitN_size]) write heapEq frame
            (by
              have mixedNat : (l.dist - l.op - c.wnext).toNat <
                  l.len.toNat := UInt32.lt_iff_toNat_lt.mp mixed
              have count : (l.dist - l.op - c.wnext).toNat +
                  (l.len.toNat - (l.dist - l.op - c.wnext).toNat) =
                  l.len.toNat := by omega
              have seg := ArraySegmentFrame.blit_then_blit saved
                (l.dist - l.op - c.wnext).toNat
                (l.len.toNat - (l.dist - l.op - c.wnext).toNat)
                (woff + (c.wsize.toNat + c.wnext.toNat -
                  (l.dist - l.op).toNat)) woff j output
              simpa only [count] using seg)
      · have wholeWindow : l.len.toNat ≤
            (l.dist - l.op - c.wnext).toNat := by
          have hnot : ¬ (l.dist - l.op - c.wnext).toNat <
              l.len.toNat := by
            intro hlt
            exact mixed (UInt32.lt_iff_toNat_lt.mpr hlt)
          omega
        obtain ⟨result, after, run, resultPacket,
            resultInvariant, resultBuffers, sizes, resultEq,
          bytes, write, heapEq, frame⟩ :=
          packet.copyMatch_window_wrapped_short_default_state
            invariant buffers left windowBranch validBack noWrap wrap
            backSize sumFits wholeWindow different windowPtr
            windowGet windowSize outPtr outputPtr outputGet
            outputWrite outputSize outputRoom
        exact finish run resultPacket resultInvariant resultBuffers sizes (by rw [resultEq])
          (by rw [resultEq]) (by rw [resultEq])
          (by rw [resultEq]) bytes
          (by simp [Zlib.Inffast.Proofs.blitN_size]) write heapEq frame
          (ArraySegmentFrame.blit saved l.len.toNat
            (woff + (c.wsize.toNat + c.wnext.toNat -
              (l.dist - l.op).toNat)) j output)
    · by_cases mixed : l.dist - l.op < l.len
      · obtain ⟨result, after, run, resultPacket,
            resultInvariant, resultBuffers, sizes, resultEq,
          bytes, write, heapEq, frame⟩ :=
          packet.copyMatch_window_contiguous_mixed_default_state
            invariant buffers left windowBranch validBack noWrap wrap
            wnextBound mixed different windowPtr windowGet
            windowSize outPtr outputPtr outputGet outputWrite
            outputSize outputRoom produced
        exact finish run resultPacket resultInvariant resultBuffers sizes (by rw [resultEq])
          (by rw [resultEq]) (by rw [resultEq])
          (by rw [resultEq]) bytes
          (by simp [Zlib.Inffast.Proofs.cpyN_size,
            Zlib.Inffast.Proofs.blitN_size]) write heapEq frame
          (by
            have mixedNat : (l.dist - l.op).toNat < l.len.toNat :=
              UInt32.lt_iff_toNat_lt.mp mixed
            have count : (l.dist - l.op).toNat +
                (l.len.toNat - (l.dist - l.op).toNat) = l.len.toNat := by
              omega
            have seg := ArraySegmentFrame.blit_then_cpy saved
              (l.dist - l.op).toNat
              (l.len.toNat - (l.dist - l.op).toNat)
              (woff + (c.wnext.toNat - (l.dist - l.op).toNat))
              (j + (l.dist - l.op).toNat - l.dist.toNat) j output
            simpa only [count] using seg)
      · have wholeWindow : l.len.toNat ≤
            (l.dist - l.op).toNat := by
          have hnot : ¬ (l.dist - l.op).toNat < l.len.toNat := by
            intro hlt
            exact mixed (UInt32.lt_iff_toNat_lt.mpr hlt)
          omega
        obtain ⟨result, after, run, resultPacket,
            resultInvariant, resultBuffers, sizes, resultEq,
          bytes, write, heapEq, frame⟩ :=
          packet.copyMatch_window_contiguous_short_default_state
            invariant buffers left windowBranch validBack noWrap wrap
            wnextBound wholeWindow different windowPtr
            windowGet windowSize outPtr outputPtr outputGet
            outputWrite outputSize outputRoom
        exact finish run resultPacket resultInvariant resultBuffers sizes (by rw [resultEq])
          (by rw [resultEq]) (by rw [resultEq])
          (by rw [resultEq]) bytes
          (by simp [Zlib.Inffast.Proofs.blitN_size]) write heapEq frame
          (ArraySegmentFrame.blit saved l.len.toNat
            (woff + (c.wnext.toNat - (l.dist - l.op).toNat)) j output)

#print axioms FastInputPacket.copyMatch_window_valid_segment_frame

end Zlib.Inflate.Proofs
