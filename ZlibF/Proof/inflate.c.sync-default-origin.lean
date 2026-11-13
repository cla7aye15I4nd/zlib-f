import ZlibF.Proof.«inflate.c.sync-search-origin»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Actual four-byte local cleanup retains both history origins. -/
theorem DefaultOriginState.free_local {h : Heap} {r : ZStreamRef} {zs block : Nat}
    {z : ZStream} {s : InflateState} {array : Array UInt8}
    (before : DefaultOriginState h r zs z s) (get : h.bytes block = some array) (size : array.size = 4) :
    DefaultOriginState (freeWin h (.ref (.blk block) 0)) r zs z s :=
  ⟨before.toDefaultStateJ.free_local get size, before.tableOrigin⟩

end Zlib.Inflate.Proofs
