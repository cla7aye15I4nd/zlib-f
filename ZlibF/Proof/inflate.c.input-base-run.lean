import ZlibF.Proof.«inflate.c.input-base-modes»
import ZlibF.Proof.«inflate.c.default-view-run»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate
set_option autoImplicit false

theorem inputBaseX_inflate_dispatch (base : UInt32) (c : Ctx) : InputBaseX base (inflate_dispatch c) := by
  unfold inflate_dispatch
  repeat' first
    | with_reducible exact inputBaseX_LOAD base _ _
    | with_reducible exact inputBaseX_inflate_DONE base _
    | with_reducible exact inputBaseX_inflate_LENGTH base _
    | with_reducible exact inputBaseX_inflate_CHECK base _
    | with_reducible exact inputBaseX_inflate_LIT base _
    | with_reducible exact inputBaseX_inflate_MATCH base _
    | with_reducible exact inputBaseX_inflate_DISTEXT base _
    | with_reducible exact inputBaseX_inflate_DIST base _
    | with_reducible exact inputBaseX_inflate_LENEXT base _
    | with_reducible exact inputBaseX_inflate_LEN base _
    | with_reducible exact inputBaseX_inflate_LEN_ base _
    | with_reducible exact inputBaseX_inflate_CODELENS base _
    | with_reducible exact inputBaseX_inflate_LENLENS base _
    | with_reducible exact inputBaseX_inflate_TABLE base _
    | with_reducible exact inputBaseX_inflate_COPY base _
    | with_reducible exact inputBaseX_inflate_COPY_ base _
    | with_reducible exact inputBaseX_inflate_STORED base _
    | with_reducible exact inputBaseX_inflate_TYPEDO base _
    | with_reducible exact inputBaseX_inflate_TYPE base _
    | with_reducible exact inputBaseX_inflate_DICT base _
    | with_reducible exact inputBaseX_inflate_DICTID base _
    | with_reducible exact inputBaseX_inflate_HCRC base _
    | with_reducible exact inputBaseX_inflate_COMMENT base _
    | with_reducible exact inputBaseX_inflate_NAME base _
    | with_reducible exact inputBaseX_inflate_EXTRA base _
    | with_reducible exact inputBaseX_inflate_EXLEN base _
    | with_reducible exact inputBaseX_inflate_OS base _
    | with_reducible exact inputBaseX_inflate_TIME base _
    | with_reducible exact inputBaseX_inflate_FLAGS base _
    | with_reducible exact inputBaseX_inflate_HEAD base _
    | input_base_source



/-- The complete actual mode loop retains its saved input count, including
all control exits. This observer supplies no callee safety assumption. -/
theorem inputBaseX_inflate_loop (base : UInt32) (c : Ctx) :
    InputBaseX base (xwhile (pure true) (inflate_dispatch c)) :=
  inputBaseX_xwhile (inputBaseX_pure base true) (inputBaseX_inflate_dispatch base c)

/-- LOAD initializes the saved input count from the original caller stream;
every actual mode then preserves it. No direct-return case is excluded. -/
theorem inflate_run_default_view_input_base
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {exit : Except Ex Unit} {regs : IL} {after : Heap}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : ZlibF.Spec.Public.StreamBuffers h r) (nonnull : z.next_out ≠ .null)
    (inputValid : z.next_in = .null → z.avail_in = 0)
    (run : runX (inflate_run c) IL.init h = .ok ((exit, regs), after)) :
    regs.in_ = z.avail_in := by
  obtain ⟨entryHeap, entryState, bs, cut, _, _, _, _, _, _, _⟩ :=
    inflate_run_default_view_entry E invariant buffers nonnull inputValid
  rw [cut] at run
  exact inputBaseX_inflate_loop z.avail_in c _ _ _ _ _ rfl run

#print axioms inputBaseX_inflate_dispatch
#print axioms inflate_run_default_view_input_base

end Zlib.Inflate.Proofs
