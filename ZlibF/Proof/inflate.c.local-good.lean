import ZlibF.Proof.«inflate.c.base»

/-! Local decoder representation. Caller objects below the allocation boundary
may occupy more than one typed table. No global uniqueness is asserted. -/
namespace Zlib.Inflate.Local
open C Zlib.Inflate.Spec

/-- Only objects allocated from `first` onwards have disjoint typed slots. -/
def UniqueFrom (h : Heap) (first : Nat) : Prop := ∀ b, first ≤ b →
  cnt (h.bytes b) + cnt (h.words b) + cnt (h.streams b) + cnt (h.gzheaders b) +
    cnt (h.dstates b) + cnt (h.istates b) + cnt (h.gzstates b) ≤ 1

/-- The established local representation, without global caller uniqueness.
This is a proof relation, separate from the unchanged public specification. -/
structure LocalGood (h : Heap) (first : Nat) (r : ZStreamRef) (zs : Nat)
    (z : ZStream) (s : InflateState) : Prop where
  live : Live h r zs z s
  inv : StInv h zs s
  fresh : Fresh h
  unique : UniqueFrom h first

end Zlib.Inflate.Local
