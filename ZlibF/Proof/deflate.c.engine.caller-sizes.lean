import ZlibF.Proof.«deflate.c.engine.caller-frame»

/-! # Caller range validity after length-preserving output writes

Buffer safety uses object extents and read-only flags. Contents may change
in an output range. This relation does not assert content preservation.
-/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

structure ByteSizes (before after : Heap) : Prop where
  get : ∀ (ref : BRef) (a : Array UInt8), Space.get before ref = some a →
    ∃ next, Space.get after ref = some next ∧ next.size = a.size
  ro : ∀ ref : BRef, Space.ro after ref = Space.ro before ref

theorem caller_range_sizes {h g : Heap} {r : ZStreamRef} {p : BPtr} {n used remaining : Nat} {write : Bool}
    (range : CallerRange h r p n write) (sizes : ByteSizes h g)
    (owned : ∀ b, StreamOwned g r b ↔ StreamOwned h r b)
    (bound : used + remaining ≤ n) :
    CallerRange g r (advance p used) remaining write := by
  rcases range with null | ⟨⟨xs, bytes⟩, writable, unowned⟩
  · subst p
    exact Or.inl rfl
  · cases p with
    | null => exact Or.inl rfl
    | ref ref off =>
      rcases bytes with ⟨null, _, _⟩ | ⟨ref0, off0, a, pointer, get, size, values⟩
      · cases null
      · have equal : ref0 = ref ∧ off0 = off := by simpa only [Ptr.ref.injEq] using pointer.symm
        rcases equal with ⟨refEq, offEq⟩
        subst ref0 off0
        obtain ⟨next, getA, sizeA⟩ := sizes.get ref a get
        refine Or.inr ⟨⟨(next.toList.drop (off + used)).take remaining,
          Or.inr ⟨ref, off + used, next, rfl, getA, by omega, rfl⟩⟩, ?_, ?_⟩
        · intro yes
          rcases writable yes with ⟨null, _⟩ | ⟨ref1, off1, a1, pointer1, get1, ro, size1⟩
          · cases null
          · have equal : ref1 = ref ∧ off1 = off := by simpa only [Ptr.ref.injEq] using pointer1.symm
            rcases equal with ⟨refEq, offEq⟩
            subst ref1 off1
            exact Or.inr ⟨ref, off + used, next, rfl, getA, (sizes.ro ref).trans ro, by omega⟩
        · intro b root now
          have original : ByteRoot (.ref ref off) b := by cases ref <;> exact root
          exact unowned b original ((owned b).mp now)

theorem separate_advance_right {p q : BPtr} {n m used remaining : Nat}
    (separate : Separate p n q m) (bound : used + remaining ≤ m) :
    Separate p n (advance q used) remaining := by
  rcases separate with empty | empty | disjoint
  · exact Or.inl empty
  · right; left
    omega
  · right; right
    cases p <;> cases q <;> simp only [Separate, advance] at disjoint ⊢
    rcases disjoint with apart | before | after
    · exact Or.inl apart
    · exact Or.inr (Or.inl (by omega))
    · exact Or.inr (Or.inr (by omega))

/-- Both caller ranges remain valid after actual input/output accounting
and size-preserving byte writes. This includes separated ranges sharing
one allocation. Data preservation is a separate claim. -/
theorem stream_buffers_sizes {h g : Heap} {r : ZStreamRef} {z z' : ZStream} {used produced : Nat}
    (get : r.get h = some z) (getA : r.get g = some z')
    (buffers : StreamBuffers h r) (sizes : ByteSizes h g)
    (owned : ∀ b, StreamOwned g r b ↔ StreamOwned h r b)
    (account : StreamAccounting z z' used produced) : StreamBuffers g r := by
  obtain ⟨old, get0, input, output, separate⟩ := buffers
  have equal : old = z := Option.some.inj (get0.symm.trans get)
  subst old
  have countIn := account.2.2.1
  have countOut := account.2.2.2.1
  have inputA := caller_range_sizes input sizes owned (used := used) (remaining := z'.avail_in.toNat) (by omega)
  have outputA := caller_range_sizes output sizes owned (used := produced) (remaining := z'.avail_out.toNat) (by omega)
  have inputPtr := account.2.2.2.2.1
  have outputPtr := account.2.2.2.2.2.1
  refine ⟨z', getA, ?_, ?_, ?_⟩
  · rw [inputPtr]
    exact inputA
  · rw [outputPtr]
    exact outputA
  · rw [inputPtr, outputPtr]
    exact separate_advance_right
      (separate_advance_left separate (used := used) (remaining := z'.avail_in.toNat) (by omega)) (by omega)

end Zlib.Deflate.Engine.Proofs
