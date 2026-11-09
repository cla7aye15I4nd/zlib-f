import ZlibF.Proof.«inflate.c.borrow-stable-dispatch-modes»

/-! The actual mode selector and real dispatch loop preserve the libc borrow
on every .ok heap result, including modeled goto and error returns. -/
namespace Zlib.Inflate.BorrowProofs
open C C.LibcBorrow Zlib.Inflate

/-- Every actual switch arm retains borrowed libc metadata. -/
theorem stable_x_inflate_dispatch (c : Ctx) : StableX (inflate_dispatch c) := by
  unfold inflate_dispatch
  repeat' first
    | with_reducible exact stable_x_inflate_DONE _
    | with_reducible exact stable_x_inflate_LENGTH _
    | with_reducible exact stable_x_inflate_CHECK _
    | with_reducible exact stable_x_inflate_LIT _
    | with_reducible exact stable_x_inflate_MATCH _
    | with_reducible exact stable_x_inflate_DISTEXT _
    | with_reducible exact stable_x_inflate_DIST _
    | with_reducible exact stable_x_inflate_LENEXT _
    | with_reducible exact stable_x_inflate_LEN _
    | with_reducible exact stable_x_inflate_LEN_ _
    | with_reducible exact stable_x_inflate_CODELENS _
    | with_reducible exact stable_x_inflate_LENLENS _
    | with_reducible exact stable_x_inflate_TABLE _
    | with_reducible exact stable_x_inflate_COPY _
    | with_reducible exact stable_x_inflate_COPY_ _
    | with_reducible exact stable_x_inflate_STORED _
    | with_reducible exact stable_x_inflate_TYPEDO _
    | with_reducible exact stable_x_inflate_TYPE _
    | with_reducible exact stable_x_inflate_DICT _
    | with_reducible exact stable_x_inflate_DICTID _
    | with_reducible exact stable_x_inflate_HCRC _
    | with_reducible exact stable_x_inflate_COMMENT _
    | with_reducible exact stable_x_inflate_NAME _
    | with_reducible exact stable_x_inflate_EXTRA _
    | with_reducible exact stable_x_inflate_EXLEN _
    | with_reducible exact stable_x_inflate_OS _
    | with_reducible exact stable_x_inflate_TIME _
    | with_reducible exact stable_x_inflate_FLAGS _
    | with_reducible exact stable_x_inflate_HEAD _
    | inflate_borrow_x_step

/-- The actual infinite-source loop is modeled by the real finite-fuel loop;
all returning outcomes retain metadata. This is not a termination theorem. -/
theorem stable_x_inflate_run (c : Ctx) : StableX (inflate_run c) := by
  unfold inflate_run
  repeat' first
    | with_reducible exact stable_x_inflate_dispatch _
    | inflate_borrow_x_step

/-- Equality for the same actual dispatch result, with arbitrary heap/registers. -/
theorem inflate_dispatch_borrow_eq (c : Ctx) (l regs : IL) (h after : Heap)
    (outcome : Except Ex Unit)
    (run : StateT.run (ExceptT.run (inflate_dispatch c)) l h = .ok ((outcome, regs), after)) :
    after.libcErrorBorrow = h.libcErrorBorrow := stable_x_inflate_dispatch c l h _ after run

theorem inflate_run_borrow_eq (c : Ctx) (l regs : IL) (h after : Heap)
    (outcome : Except Ex Unit)
    (run : StateT.run (ExceptT.run (inflate_run c)) l h = .ok ((outcome, regs), after)) :
    after.libcErrorBorrow = h.libcErrorBorrow := stable_x_inflate_run c l h _ after run

#print axioms stable_x_inflate_dispatch
#print axioms stable_x_inflate_run
#print axioms inflate_run_borrow_eq
end Zlib.Inflate.BorrowProofs
