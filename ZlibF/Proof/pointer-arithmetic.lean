import ZlibF.Runtime.Ptr

/-!
# Natural-offset pointer arithmetic for implementation proofs

These helpers use the runtime's checked pointer addition. The rules retain the
same live-array, bounds and subtraction premises as the runtime lemmas.
-/

namespace ZlibF.Proof.PointerArithmetic
open C

/-- `p + n` for a pointer into an array. -/
def addNat {R T : Type} [Space Heap R T] (p : Ptr R) (n : Nat) : M (Ptr R) := Ptr.add p (n : Int)
/-- `p - n` for a pointer into an array. -/
def subNat {R T : Type} [Space Heap R T] (p : Ptr R) (n : Nat) : M (Ptr R) := Ptr.add p (-(n : Int))

theorem addNat_ok {R T : Type} [Space Heap R T] {h : Heap} {r : R} {a : Array T} {off n : Nat}
    (hg : Space.get h r = some a) (hn : off + n ≤ a.size) : addNat (.ref r off) n h = .ok (.ref r (off + n), h) :=
  Ptr.add_nat_ok hg hn
theorem subNat_ok {R T : Type} [Space Heap R T] {h : Heap} {r : R} {a : Array T} {off n : Nat}
    (hg : Space.get h r = some a) (h1 : n ≤ off) (h2 : off ≤ a.size) :
    subNat (.ref r off) n h = .ok (.ref r (off - n), h) :=
  Ptr.sub_nat_ok hg h1 h2

end ZlibF.Proof.PointerArithmetic
