import ZlibF.Proof.«inflate.c.copy-generic-state»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The common final heap of either successful windowed table-origin branch.
Only the code-pointer repair differs between those branches. -/
def copiedWindowHeap (h : Heap) (dest : ZStreamRef) (z : ZStream)
    (s copied : InflateState) (sourceArray : Array UInt8) : Heap :=
  let size := 2 ^ s.wbits.toNat
  let zNext := { z with state := some (.inflate h.nextBlk) }
  let stateHeap := allocIstHeap (dest.put h zNext) copied
  let freshArray : Array UInt8 := Array.ofFn (n := size)
    (fun i => Junk.of (h.garbage (h.nalloc + 1) i.val))
  let allocated := Zlib.Zutil.Proofs.allocHeap stateHeap size
  { allocated with bytes := (upd allocated.bytes (h.nextBlk + 1)
      (some (copyRange freshArray sourceArray 0 0 s.whave.toNat))) }

end Zlib.Inflate.Proofs
