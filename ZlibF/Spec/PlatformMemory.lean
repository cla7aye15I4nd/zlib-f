import ZlibF.Runtime.Ptr

/-!
# Byte-object sizes for the initial LP64 platform scope

The signed 64-bit pointer-difference limit is distinct from the unsigned
64-bit address width. These predicates state an explicit environment scope;
they do not alter the allocator or establish that scope for arbitrary heaps.
-/

namespace ZlibF.PlatformMemory
open C
set_option autoImplicit false

/-- One past the largest admitted byte-object size. The initial platform
scope uses `PTRDIFF_MAX = 2^63 - 1`, not the unsigned `SIZE_MAX`. -/
def byteObjectLimit : Nat := 2 ^ 63

/-- Every live represented byte array, including static and embedded views,
fits the signed pointer-difference range. This is an explicit platform
premise. For caller storage not obtained from the default allocator, it is
an additional object-realizability requirement, not a malloc conclusion.
It does not bound the sum of allocations or the total stream length. -/
def ByteObjectsFit (h : Heap) : Prop :=
  ∀ (ref : BRef) (a : Array UInt8), Space.get h ref = some a →
    a.size < byteObjectLimit

end ZlibF.PlatformMemory
