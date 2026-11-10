import ZlibF.Proof.«inflate.c.header-payload-interface»
namespace Zlib.Inflate.Proofs.HeaderSourceTrace
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs
set_option autoImplicit false

/-- An actual finite continuing steps either has no trips, or starts
with the unique observed first normal trip. No fuel reset is assumed. -/
theorem DispatchPrefix.drop_first {c : Ctx} {start next finish : IL} {before heap after : Heap}
    (first : runX (inflate_dispatch c) start before = .ok ((.ok (), next), heap))
    (trace : DispatchPrefix c start before finish after) :
    (finish = start ∧ after = before) ∨ DispatchPrefix c next heap finish after := by
  induction trace with
  | begin => exact Or.inl ⟨rfl, rfl⟩
  | @step l result h h1 prior actual ih =>
    rcases ih with ⟨rfl, rfl⟩ | tail
    · have same := Except.ok.inj (first.symm.trans actual)
      cases same
      exact Or.inr .begin
    · exact Or.inr (.step tail actual)

/-- A real completed switch trace can be cut after one observed normal
trip, retaining its identical exception, local registers and final heap. -/
theorem DispatchExit.drop_first {c : Ctx} {start next regs : IL} {before heap after : Heap} {exit : Ex}
    (first : runX (inflate_dispatch c) start before = .ok ((.ok (), next), heap))
    (trace : DispatchExit c start before exit regs after) : DispatchExit c next heap exit regs after := by
  obtain ⟨finish, endHeap, steps, stop⟩ := trace
  rcases steps.drop_first first with ⟨rfl, rfl⟩ | tail
  · rw [first] at stop
    cases stop
  · exact ⟨finish, endHeap, tail, stop⟩

/-- Any selected actual normal prefix can be removed from the completed
actual source trace, without changing the final source observation. -/
theorem DispatchPrefix.exit_tail {c : Ctx} {start finish regs : IL} {before heap after : Heap} {exit : Ex}
    (steps : DispatchPrefix c start before finish heap)
    (complete : DispatchExit c start before exit regs after) : DispatchExit c finish heap exit regs after := by
  induction steps with
  | begin => exact complete
  | step prior normal ih => exact ih.drop_first normal

/-- Finite actual switch execution has a unique final source observation,
independently of the implementation's fuel accounting. -/
theorem DispatchExit.unique {c : Ctx} {start regs regs1 : IL} {before after after1 : Heap} {exit exit1 : Ex}
    (left : DispatchExit c start before exit regs after)
    (right : DispatchExit c start before exit1 regs1 after1) :
    exit = exit1 ∧ regs = regs1 ∧ after = after1 := by
  obtain ⟨finish, heap, steps, stop⟩ := left
  obtain ⟨finish1, heap1, steps1, stop1⟩ := steps.exit_tail right
  have stopped : ∀ {result : IL} {heap2 : Heap}, DispatchPrefix c finish heap result heap2 → result = finish ∧ heap2 = heap := by
    intro result heap2 trace
    induction trace with
    | begin => exact ⟨rfl, rfl⟩
    | @step l next h h1 prior normal ih =>
      obtain ⟨rfl, rfl⟩ := ih
      rw [stop] at normal
      cases normal
  obtain ⟨rfl, rfl⟩ := stopped steps1
  have same := Except.ok.inj (stop.symm.trans stop1)
  cases same
  exact ⟨rfl, rfl, rfl⟩

#print axioms DispatchPrefix.drop_first
#print axioms DispatchExit.drop_first
#print axioms DispatchPrefix.exit_tail
#print axioms DispatchExit.unique
end Zlib.Inflate.Proofs.HeaderSourceTrace

namespace Zlib.Inflate.Proofs.HeaderSourceTrace
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs
set_option autoImplicit false

/-- The closed source loop proofs make a genuine internal continuation
cut. Both whole and remaining loops are proved terminating; finite actual
trace uniqueness identifies their final observation. No fuel reset or
postcondition about the caller's final mode/output/window is assumed. -/
theorem loop_prefix_continuation
    {c : Ctx} {start finish : IL} {before heap : Heap} {r : ZStreamRef} {zs : Nat}
    {z z1 : ZStream} {s s1 : InflateState} {bs bs1 : List UInt8}
    (E : Env c before r zs z s) (initial : DefaultOriginState before r zs z s)
    (packet : DispatchBuffers before r start bs) (bits : start.bits.toNat ≤ 39)
    (E1 : Env c heap r zs z1 s1) (current : DefaultOriginState heap r zs z1 s1)
    (packet1 : DispatchBuffers heap r finish bs1) (bits1 : finish.bits.toNat ≤ 39)
    (steps : DispatchPrefix c start before finish heap) :
    runX (xwhile (pure true) (inflate_dispatch c)) start before =
      runX (xwhile (pure true) (inflate_dispatch c)) finish heap := by
  obtain ⟨exit, regs, after, _z, _s, _used, _made, _bound, whole, _current,
    _packet, _bits, _sizes, _next, _count, _put, _left, trace⟩ := loop_actual_trace E initial packet bits
  obtain ⟨exit1, regs1, after1, _z1, _s1, _used1, _made1, _bound1, tail,
    _current1, _packet1, _bits1, _sizes1, _next1, _count1, _put1, _left1, trace1⟩ := loop_actual_trace E1 current packet1 bits1
  obtain ⟨rfl, rfl, rfl⟩ := (steps.exit_tail trace).unique trace1
  exact whole.trans tail.symm

#print axioms loop_prefix_continuation
end Zlib.Inflate.Proofs.HeaderSourceTrace
