import ZlibF.Proof.«trees.c.dynamic-header»

/-! # Actual dynamic tags and the independent block-sequence grammar -/

namespace Zlib.Trees.Proofs
open C ZlibF.Spec Out
set_option autoImplicit false

theorem dynamicTag_wire (last : Bool) :
    dynamicTag last = natBits (if last then 1 else 0) 1 ++ natBits 2 2 := by
  cases last <;> decide +kernel

/-- The actual final dynamic tag precedes the independently parsed body.
Any following terminal padding or wrapper trailer remains a suffix. -/
theorem dynamic_last_grammar {history out : List UInt8} {payload : List Bool}
    (body : ∀ suffix, Body [] 2 history (payload ++ suffix) suffix out) (suffix : List Bool) :
    Blocks [] history ((dynamicTag true ++ payload) ++ suffix) suffix out := by
  rw [dynamicTag_wire, List.append_assoc, List.append_assoc]
  exact Blocks.last (readBits_natBits 1 1 _ (by decide +kernel))
    (readBits_natBits 2 2 _ (by decide +kernel)) (body suffix)

/-- A non-final dynamic block retains the entire next-block continuation. -/
theorem dynamic_more_grammar {history middle out : List UInt8} {payload suffix rest : List Bool}
    (body : ∀ tail, Body [] 2 history (payload ++ tail) tail middle)
    (next : Blocks [] middle suffix rest out) :
    Blocks [] history ((dynamicTag false ++ payload) ++ suffix) rest out := by
  rw [dynamicTag_wire, List.append_assoc, List.append_assoc]
  exact Blocks.more (readBits_natBits 1 0 _ (by decide +kernel))
    (readBits_natBits 2 2 _ (by decide +kernel)) (body suffix) next

end Zlib.Trees.Proofs
