import ZlibF.Proof.«inflate.c.fast-view-window-wrapped-three»
import ZlibF.Proof.«inflate.c.fast-view-window-contiguous-mixed»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The valid-window cases of translated `copyMatch` share one packet,
output-cursor, writable-view and buffer-size postcondition. -/
theorem FastInputPacket.copyMatch_window_valid_view
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    (packet : FastInputPacket h slow bs l)
    (separate : Separate slow.next slow.have_.toNat
      slow.put slow.left.toNat)
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
      result.out = .ref dest (j + l.len.toNat) ∧
      result.broke = l.broke ∧
      result.againD = l.againD ∧
      result.againL = l.againL ∧
      Space.get after dest = some array ∧
      array.size = output.size ∧
      Space.ro after dest = false := by
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
      (out : result.out = .ref dest (j + l.len.toNat))
      (broke : result.broke = l.broke)
      (againD : result.againD = l.againD)
      (againL : result.againL = l.againL)
      (bytes : Space.get after dest = some array)
      (size : array.size = output.size)
      (write : Space.ro after dest = false) :
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
        Space.ro after dest = false :=
    ⟨result, after, array, run, resultPacket, out,
      broke, againD, againL,
      bytes, size, write⟩
  by_cases noWrap : c.wnext = 0
  · by_cases mixed : l.dist - l.op < l.len
    · obtain ⟨result, after, run, resultPacket,
          resultEq, bytes, write⟩ :=
        packet.copyMatch_window_nowrap_mixed_view
          separate left windowBranch validBack noWrap backSize
          mixed different windowPtr windowGet windowSize outPtr
          outputPtr outputGet outputWrite outputSize outputRoom
          produced
      exact finish run resultPacket (by rw [resultEq])
        (by rw [resultEq]) (by rw [resultEq])
        (by rw [resultEq]) bytes
        (by simp [Zlib.Inffast.Proofs.cpyN_size,
          Zlib.Inffast.Proofs.blitN_size]) write
    · have wholeWindow : l.len.toNat ≤
          (l.dist - l.op).toNat := by
        have hnot : ¬ (l.dist - l.op).toNat < l.len.toNat := by
          intro hlt
          exact mixed (UInt32.lt_iff_toNat_lt.mpr hlt)
        omega
      obtain ⟨result, after, run, resultPacket,
          resultEq, bytes, write⟩ :=
        packet.copyMatch_window_nowrap_short_view
          separate left windowBranch validBack noWrap backSize
          wholeWindow different windowPtr windowGet windowSize
          outPtr outputPtr outputGet outputWrite outputSize
          outputRoom
      exact finish run resultPacket (by rw [resultEq])
        (by rw [resultEq]) (by rw [resultEq])
        (by rw [resultEq]) bytes
        (by simp [Zlib.Inffast.Proofs.blitN_size]) write
  · by_cases wrap : c.wnext < l.dist - l.op
    · by_cases mixed : l.dist - l.op - c.wnext < l.len
      · by_cases third : c.wnext <
            l.len - (l.dist - l.op - c.wnext)
        · obtain ⟨result, after, run, resultPacket,
              resultEq, bytes, write⟩ :=
            packet.copyMatch_window_wrapped_three_view
              separate left windowBranch validBack noWrap wrap
              backSize sumFits mixed third different
              windowPtr windowGet windowSize outPtr outputPtr
              outputGet outputWrite outputSize outputRoom produced
          exact finish run resultPacket (by rw [resultEq])
            (by rw [resultEq]) (by rw [resultEq])
            (by rw [resultEq]) bytes
            (by simp [Zlib.Inffast.Proofs.cpyN_size,
              Zlib.Inffast.Proofs.blitN_size]) write
        · obtain ⟨result, after, run, resultPacket,
              resultEq, bytes, write⟩ :=
            packet.copyMatch_window_wrapped_two_view
              separate left windowBranch validBack noWrap wrap
              backSize sumFits mixed third different
              windowPtr windowGet windowSize outPtr outputPtr
              outputGet outputWrite outputSize outputRoom
          exact finish run resultPacket (by rw [resultEq])
            (by rw [resultEq]) (by rw [resultEq])
            (by rw [resultEq]) bytes
            (by simp [Zlib.Inffast.Proofs.blitN_size]) write
      · have wholeWindow : l.len.toNat ≤
            (l.dist - l.op - c.wnext).toNat := by
          have hnot : ¬ (l.dist - l.op - c.wnext).toNat <
              l.len.toNat := by
            intro hlt
            exact mixed (UInt32.lt_iff_toNat_lt.mpr hlt)
          omega
        obtain ⟨result, after, run, resultPacket,
            resultEq, bytes, write⟩ :=
          packet.copyMatch_window_wrapped_short_view
            separate left windowBranch validBack noWrap wrap
            backSize sumFits wholeWindow different windowPtr
            windowGet windowSize outPtr outputPtr outputGet
            outputWrite outputSize outputRoom
        exact finish run resultPacket (by rw [resultEq])
          (by rw [resultEq]) (by rw [resultEq])
          (by rw [resultEq]) bytes
          (by simp [Zlib.Inffast.Proofs.blitN_size]) write
    · by_cases mixed : l.dist - l.op < l.len
      · obtain ⟨result, after, run, resultPacket,
            resultEq, bytes, write⟩ :=
          packet.copyMatch_window_contiguous_mixed_view
            separate left windowBranch validBack noWrap wrap
            wnextBound mixed different windowPtr windowGet
            windowSize outPtr outputPtr outputGet outputWrite
            outputSize outputRoom produced
        exact finish run resultPacket (by rw [resultEq])
          (by rw [resultEq]) (by rw [resultEq])
          (by rw [resultEq]) bytes
          (by simp [Zlib.Inffast.Proofs.cpyN_size,
            Zlib.Inffast.Proofs.blitN_size]) write
      · have wholeWindow : l.len.toNat ≤
            (l.dist - l.op).toNat := by
          have hnot : ¬ (l.dist - l.op).toNat < l.len.toNat := by
            intro hlt
            exact mixed (UInt32.lt_iff_toNat_lt.mpr hlt)
          omega
        obtain ⟨result, after, run, resultPacket,
            resultEq, bytes, write⟩ :=
          packet.copyMatch_window_contiguous_short_view
            separate left windowBranch validBack noWrap wrap
            wnextBound wholeWindow different windowPtr
            windowGet windowSize outPtr outputPtr outputGet
            outputWrite outputSize outputRoom
        exact finish run resultPacket (by rw [resultEq])
          (by rw [resultEq]) (by rw [resultEq])
          (by rw [resultEq]) bytes
          (by simp [Zlib.Inffast.Proofs.blitN_size]) write

end Zlib.Inflate.Proofs
