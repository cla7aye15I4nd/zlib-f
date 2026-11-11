import ZlibF.Proof.«inflate.c.need-dict-sourcecut»

/-!
# inflate.c: no output before the dictionary stage

A default loop that stops in HEAD, DICTID or DICT has written nothing: the
saved output count is the remaining output space. inf_leave uses this to
skip `updatewindow` when the width is still 0.
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

theorem inflate_run_default_low_out
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s returned : InflateState} {regs : IL} {exit : Ex}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : StreamBuffers h r) (nonnull : z.next_out ≠ .null)
    (inputValid : z.next_in = .null → z.avail_in = 0)
    (local_ : HeaderLocal c h r s (dispatchRegs z s))
    (run : runX (inflate_run c) IL.init h = .ok ((.error exit, regs), after))
    (get : after.istates zs = some returned) :
    returned.mode ≤ DICT → regs.out_ = regs.left := by
  intro low
  obtain ⟨_, left⟩ :=
    ActiveSourceCut.run_dictionary_output_unchanged E invariant buffers nonnull inputValid local_ run get low
  obtain ⟨lower, upper⟩ := inflate_run_default_view_output_base E invariant buffers nonnull inputValid local_ run
  apply UInt32.toNat_inj.mp
  rw [left] at lower ⊢
  omega

/-- An entry bit packet: a null input pointer has no input. -/
theorem BitInv.input_valid {h : Heap} {z : ZStream} {s : InflateState} {bs : List UInt8}
    (input : BitInv h (dispatchRegs z s) bs) : z.next_in = .null → z.avail_in = 0 := by
  intro null
  rcases input.next with empty | ⟨_, _, _, pointer, _⟩
  · have count := input.have_eq
    rw [empty] at count
    exact UInt32.toNat_inj.mp (by simpa [dispatchRegs] using count)
  · change z.next_in = _ at pointer
    rw [null] at pointer
    cases pointer

#print axioms inflate_run_default_low_out
end Zlib.Inflate.Proofs
