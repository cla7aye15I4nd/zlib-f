import ZlibF.Proof.«inflate.c.global-fast-prefix-ready»
import ZlibF.Proof.«inflate.c.window-physical-history»
import ZlibF.Proof.«inflate.c.caller-buffers»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public ZlibF.Spec
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- The public logical dictionary at a live data-mode cut is precisely the
fast decoder's physical saved ring. A zero `whave` permits lazy NULL storage;
otherwise the caller output range excludes the private window object. -/
theorem fast_saved_of_dictionary
    {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {slow : IL}
    {dest : BRef} {oo : Nat} {dict : List UInt8}
    (good : Good h r zs z s)
    (outputRange : CallerRange h r slow.put slow.left.toNat true)
    (putPtr : slow.put = .ref dest oo)
    (dictionary : InflateDictionary h s dict) :
    ∃ (saved : Array UInt8) (woff : Nat),
      (0 < s.whave.toNat → ∃ window,
        window ≠ dest ∧ s.window = .ref window woff ∧
        Space.get h window = some saved ∧
        woff + s.wsize.toNat ≤ saved.size) ∧
      MatchHistory.saved saved s.wsize.toNat s.wnext.toNat
        s.whave.toNat woff = dict ∧
      dict.length = s.whave.toNat := by
  by_cases positive : 0 < s.whave.toNat
  · rcases good.inv.win.block with null | ⟨w, saved, window,
      get, _writable, size⟩
    · have zero := good.inv.win.nullws null
      have bound := good.inv.win.hv
      rw [zero] at bound
      simp at bound
      omega
    have windowData : (.blk w : BRef) ≠ dest :=
      (callerRange_private_window good outputRange putPtr w window).symm
    have fullSize : s.wsize.toNat = 2 ^ s.wbits.toNat := by
      rcases good.inv.win.ws with empty | full
      · have bound := good.inv.win.hv
        rw [empty] at bound
        omega
      · exact full
    have savedEq :=
      (WindowHistory.dictionary_eq_saved good window get size).mp dictionary
    refine ⟨saved, 0, ?_, savedEq.symm, ?_⟩
    · intro _
      refine ⟨.blk w, windowData, window, ?_, ?_⟩
      · simpa only [Space.get, BRef.get_blk] using get
      · simp only [Nat.zero_add, fullSize, size, Nat.le_refl]
    · rw [savedEq]
      simp only [MatchHistory.saved, List.length_map,
        List.length_range]
  · have zero : s.whave = 0 := UInt32.toNat_inj.mp
      (Nat.eq_zero_of_not_pos positive)
    have nextZero : s.wnext = 0 := by
      apply UInt32.toNat_inj.mp
      by_cases noSize : s.wsize.toNat = 0
      · rcases good.inv.win.wn with lt | pair
        · simp only [UInt32.toNat_zero]
          omega
        · simp only [UInt32.toNat_zero]
          omega
      · have lt : s.whave.toNat < s.wsize.toNat := by omega
        rw [good.inv.win.eq lt, zero]
    have empty : dict = [] := by
      rcases dictionary with ⟨_, eq⟩ | ⟨ref, off, array,
        ptr, get, bound, values⟩
      · exact eq
      · rw [zero, nextZero] at values
        simp only [UInt32.sub_self, UInt32.toNat_zero,
          List.take_zero, List.nil_append] at values
        exact values
    refine ⟨#[], 0, ?_, ?_, ?_⟩
    · intro contradiction
      rw [zero] at contradiction
      simp at contradiction
    · rw [empty, zero]
      simp only [UInt32.toNat_zero, MatchHistory.saved,
        List.range_zero, List.map_nil]
    · rw [empty, zero]
      rfl

#print axioms fast_saved_of_dictionary
end Zlib.Inflate.Proofs
