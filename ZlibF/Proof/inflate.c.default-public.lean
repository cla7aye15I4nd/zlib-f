import ZlibF.Proof.«inflate.c.leave-local»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The four-byte local object cannot be the default decoder's window. -/
theorem default_local_not_window {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {s : InflateState} {block : Nat} {array : Array UInt8} (good : Good h r zs z s)
    (get : h.bytes block = some array) (size : array.size = 4) (bits : 8 ≤ s.wbits.toNat) :
    s.window ≠ .ref (.blk block) 0 := by
  intro window
  rcases good.inv.win.block with null | ⟨w, bytes, win, bytesGet, ro, bytesSize⟩
  · rw [window] at null
    cases null
  · rw [window] at win
    cases win
    have same : bytes = array := Option.some.inj (bytesGet.symm.trans get)
    subst bytes
    rw [size] at bytesSize
    have big : 2 ^ 8 ≤ 2 ^ s.wbits.toNat := Nat.pow_le_pow_right (by decide) bits
    omega

/-- A live byte object is distinct from the stream root and private state.
Its concrete size also excludes the default window. -/
theorem default_local_outside {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {s : InflateState} {block : Nat} {array : Array UInt8} (good : Good h r zs z s)
    (get : h.bytes block = some array) (size : array.size = 4) (width : 8 ≤ s.wbits.toNat ∨ s.window = .null) :
    ¬ (StreamRoot r block ∨ InflateOwned zs s block) := by
  have notState : block ≠ zs := by
    intro same
    subst block
    have unique := good.uniq zs
    simp only [get, good.live.hs, cnt_some] at unique
    omega
  have notRoot : ¬ StreamRoot r block := by
    cases r with
    | tab index =>
      intro same
      change block = index at same
      subst block
      have unique := good.uniq index
      have hz : h.streams index = some z := good.live.hz
      simp only [get, hz, cnt_some] at unique
      omega
    | in_gzstate_strm index =>
      intro same
      change block = index at same
      subst block
      obtain ⟨g, gzGet, eq⟩ := Option.map_eq_some_iff.mp good.live.hz
      have unique := good.uniq index
      simp only [get, gzGet, cnt_some] at unique
      omega
  rintro (root | (state | window))
  · exact notRoot root
  · exact notState state
  · rcases width with bits | null
    · exact default_local_not_window good get size bits window
    · rw [null] at window
      cases window

end Zlib.Inflate.Proofs
