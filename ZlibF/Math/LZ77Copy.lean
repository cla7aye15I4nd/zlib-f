import ZlibF.Math.LZ77CopySpec

/-!
# Bytewise array copies implement the independent LZ77 operation

The proof follows one byte at a time. The source of an overlapping copy
is read from the updated array, exactly as copyBack reads growing output.
-/

set_option autoImplicit false

namespace ZlibF.Math.LZ77Copy
open C ZlibF.Spec Zlib.Inffast.Proofs

private theorem written_length (bytes : Array UInt8) (offset count : Nat)
    (hc : count ≤ offset) (hb : offset ≤ bytes.size) :
    (writtenBytes bytes offset count).length = count := by
  simp only [writtenBytes, List.length_take, List.length_drop, Array.length_toList]
  omega

private theorem written_get (bytes : Array UInt8) (offset count i : Nat) :
    (writtenBytes bytes offset count)[i]? =
      if i < count then bytes[offset - count + i]? else none := by
  simp only [writtenBytes, List.getElem?_take, List.getElem?_drop, Array.getElem?_toList]

private theorem written_set_append (bytes : Array UInt8) (offset count : Nat)
    (value : UInt8) (hc : count ≤ offset) (hb : offset < bytes.size) :
    writtenBytes (bytes.set! offset value) (offset + 1) (count + 1) =
      writtenBytes bytes offset count ++ [value] := by
  apply List.ext_getElem?
  intro i
  rw [written_get, List.getElem?_append, written_length bytes offset count hc (by omega)]
  have hstart : offset + 1 - (count + 1) = offset - count := by omega
  rw [hstart]
  by_cases hi : i < count
  · have hne : offset ≠ offset - count + i := by omega
    simp [hi, show i < count + 1 by omega, written_get, Array.set!_eq_setIfInBounds,
      Array.getElem?_setIfInBounds, hne]
  · by_cases he : i = count
    · subst i
      have hs : offset - count + count = offset := by omega
      simp [show ¬ count < count by omega, show count < count + 1 by omega, hs,
        Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, hb]
    · have hn : ¬ i < count + 1 := by omega
      have hz : i - count ≠ 0 := by omega
      simp [hi, hn, List.getElem?_singleton, hz]

private theorem output_source (dict : List UInt8) (bytes : Array UInt8)
    (offset count dist : Nat) (hc : count ≤ offset) (hb : offset ≤ bytes.size)
    (hd : 0 < dist) (hcount : dist ≤ count) :
    (dict ++ writtenBytes bytes offset count).getD
      ((dict ++ writtenBytes bytes offset count).length - dist) 0 =
        bytes.getD (offset - dist) 0 := by
  rw [List.length_append, written_length bytes offset count hc hb]
  have hidx : dict.length + count - dist = dict.length + (count - dist) := by omega
  have hright : dict.length ≤ dict.length + (count - dist) := by omega
  have hsmall : count - dist < count := by omega
  have hsource : offset - count + (count - dist) = offset - dist := by omega
  simp only [List.getD_eq_getElem?_getD, hidx,
    List.getElem?_append_right hright, Nat.add_sub_cancel_left, written_get,
    hsmall, ite_true, hsource, Array.getD_eq_getD_getElem?]

/-- The byte source is in the current output; reads of earlier writes
implement arbitrary overlapping matches. -/
theorem output_copy_refines_lz77 : Goal.output_copy_refines_lz77 := by
  intro dict bytes offset count dist n
  induction n generalizing bytes offset count with
  | zero => intro _ _ _ _; simp [cpyN, copyBack]
  | succ n ih =>
    intro hc hd hdist hb
    have ho : offset < bytes.size := by omega
    have hsrc : offset - dist + 1 = offset + 1 - dist := by omega
    rw [cpyN, hsrc]
    rw [show offset + (n + 1) = offset + 1 + n by omega,
      show count + (n + 1) = count + 1 + n by omega]
    rw [ih (bytes.set! offset (bytes.getD (offset - dist) 0)) (offset + 1) (count + 1)
      (by omega) hd (by omega) (by simp only [Array.size_set!]; omega)]
    rw [copyBack, written_set_append bytes offset count _ hc ho]
    rw [output_source dict bytes offset count dist hc (by omega) hd hdist]

private theorem window_source (dict : List UInt8) (bytes : Array UInt8)
    (offset count dist : Nat) (hc : count ≤ offset) (hb : offset ≤ bytes.size)
    (hd : count < dist) (hbound : dist ≤ dict.length + count) :
    (dict ++ writtenBytes bytes offset count).getD
      ((dict ++ writtenBytes bytes offset count).length - dist) 0 =
        dict.getD (dict.length + count - dist) 0 := by
  rw [List.length_append, written_length bytes offset count hc hb]
  have hi : dict.length + count - dist < dict.length := by omega
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private theorem window_copy (dict : List UInt8) (window : Array UInt8)
    (dist : Nat) : ∀ n (bytes : Array UInt8) (offset count sourceOffset : Nat),
    count ≤ offset → count ≤ dist → dist ≤ dict.length + count →
    n ≤ dist - count → offset + n ≤ bytes.size → sourceOffset + n ≤ window.size →
    (∀ i, i < n → window.getD (sourceOffset + i) 0 =
      dict.getD (dict.length + count - dist + i) 0) →
    writtenBytes (blitN window n sourceOffset offset bytes) (offset + n) (count + n) =
      copyBack dict dist n (writtenBytes bytes offset count) := by
  intro n
  induction n with
  | zero => intro bytes offset count sourceOffset _ _ _ _ _ _ _; simp [blitN, copyBack]
  | succ n ih =>
    intro bytes offset count sourceOffset hc hd hbound hn hb hw hcells
    have hlt : count < dist := by omega
    have ho : offset < bytes.size := by omega
    rw [blitN]
    rw [show offset + (n + 1) = offset + 1 + n by omega,
      show count + (n + 1) = count + 1 + n by omega]
    rw [ih (bytes.set! offset (window.getD sourceOffset 0)) (offset + 1) (count + 1)
      (sourceOffset + 1) (by omega) (by omega) (by omega) (by omega)
      (by simp only [Array.size_set!]; omega) (by omega) ?_]
    · rw [copyBack, written_set_append bytes offset count _ hc ho]
      have h0 := hcells 0 (by omega)
      simp only [Nat.add_zero] at h0
      rw [window_source dict bytes offset count dist hc (by omega) hlt hbound, h0]
    · intro i hi
      have hnext := hcells (i + 1) (by omega)
      have hp : dict.length + (count + 1) - dist + i =
          dict.length + count - dist + (i + 1) := by omega
      simpa only [hp, Nat.add_assoc, Nat.add_comm 1 i] using hnext

/-- A fixed saved-window segment agrees with the same growing-history copy
until the source reaches the current output. -/
theorem window_copy_refines_lz77 : Goal.window_copy_refines_lz77 := by
  intro dict bytes window offset count sourceOffset dist n hc hd hbound hn hb hw hcells
  exact window_copy dict window dist n bytes offset count sourceOffset hc (by omega) hbound hn hb hw hcells

end ZlibF.Math.LZ77Copy
