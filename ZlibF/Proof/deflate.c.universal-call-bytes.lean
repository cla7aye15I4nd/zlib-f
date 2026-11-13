import ZlibF.Proof.«deflate.c.universal-call-early»

/-!
# deflate.c: the bytes a call delivers

Owner 2 of the deflate split (`deflate_call`). A call that wrote `produced` bytes into the caller's
output range (its call frame) leaves a list of `produced` bytes readable at `next_out`.
-/

namespace Zlib.Deflate.Universal.Call
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- **The delivered bytes** (T4): the output block keeps its size across the call (buffer frame), and
the delivered range lies inside the caller's output range. -/
theorem bytes_out {h after : Heap} {r : ZStreamRef} {z z' : ZStream} {changed : Nat → Prop} {used produced : Nat}
    (buffers : StreamBuffers h r) (hz : r.get h = some z) (account : StreamAccounting z z' used produced)
    (frame : BufferFrame h after changed [⟨z.next_out, produced⟩]) (out : z.next_out ≠ .null) :
    ∃ xs : List UInt8, xs.length = produced ∧ Bytes after z.next_out produced xs := by
  obtain ⟨z0, get0, _, outRange, _⟩ := buffers
  have same : z0 = z := Option.some.inj (get0.symm.trans hz)
  subst same
  rcases outRange with null | ⟨⟨xs, bytes⟩, _, _⟩
  · exact absurd null out
  rcases bytes with ⟨null, _, _⟩ | ⟨ref, i, a, ptr, get, size, _⟩
  · exact absurd null out
  obtain ⟨a', get', size', _⟩ := frame.2 ⟨z0.next_out, produced⟩ (List.mem_singleton.mpr rfl) ref i a ptr get
  have le : produced ≤ z0.avail_out.toNat := account.2.1
  refine ⟨(a'.toList.drop i).take produced, ?_, Or.inr ⟨ref, i, a', ptr, get', by omega, rfl⟩⟩
  simp; omega

end Zlib.Deflate.Universal.Call
