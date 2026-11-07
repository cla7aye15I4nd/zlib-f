import ZlibF.Math.DeflateFixedPayload

/-! # Actual fixed-block tags and the independent block sequence grammar -/

namespace Zlib.Trees.Proofs.Out
open C ZlibF.Spec
set_option autoImplicit false

/-- BFINAL followed by BTYPE = 1, in the source's low-bit write order. -/
def fixedTag (last : Bool) : List Bool := natBits (if last then 3 else 2) 3

theorem fixedTag_wire (last : Bool) :
    fixedTag last = natBits (if last then 1 else 0) 1 ++ natBits 1 2 := by
  cases last <;> decide +kernel

theorem fixedTag_length (last : Bool) : (fixedTag last).length = 3 := by
  simp [fixedTag]

/-- A final fixed block uses the independent final-block rule. A suffix
may contain terminal padding and wrapper trailer bits. -/
theorem fixed_last_grammar {history out : List UInt8} {payload : List Bool}
    (body : ∀ suffix, Body [] 1 history (payload ++ suffix) suffix out) (suffix : List Bool) :
    Blocks [] history ((fixedTag true ++ payload) ++ suffix) suffix out := by
  rw [fixedTag_wire, List.append_assoc, List.append_assoc]
  exact Blocks.last (readBits_natBits 1 1 _ (by decide))
    (readBits_natBits 2 1 _ (by decide)) (body suffix)

/-- A non-final fixed block retains the complete next-block continuation. -/
theorem fixed_more_grammar {history middle out : List UInt8} {payload suffix rest : List Bool}
    (body : ∀ tail, Body [] 1 history (payload ++ tail) tail middle)
    (next : Blocks [] middle suffix rest out) :
    Blocks [] history ((fixedTag false ++ payload) ++ suffix) rest out := by
  rw [fixedTag_wire, List.append_assoc, List.append_assoc]
  exact Blocks.more (readBits_natBits 1 0 _ (by decide))
    (readBits_natBits 2 1 _ (by decide)) (body suffix) next

end Zlib.Trees.Proofs.Out
