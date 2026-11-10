import ZlibF.Proof.«inflate.c.whole-epoch-call-cut»
import ZlibF.Proof.«inflate.c.header-loop-continuation»
namespace Zlib.Inflate.Proofs.HeaderSourceTrace
open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

/-- An inline prefix has the same first dispatch result. Replacing that
first source cut retains every later actual normal trip. -/
theorem DispatchPrefix.replace_initial {c : Ctx} {start next finish : IL} {h after final : Heap}
    (same : runX (inflate_dispatch c) start h = runX (inflate_dispatch c) next after)
    (trace : DispatchPrefix c start h finish final) :
    (finish = start ∧ final = h) ∨ DispatchPrefix c next after finish final := by
  induction trace with
  | begin => exact Or.inl ⟨rfl, rfl⟩
  | step prior normal ih =>
    rcases ih with ⟨rfl, rfl⟩ | replaced
    · exact Or.inr (.step .begin (same.symm.trans normal))
    · exact Or.inr (.step replaced normal)

/-- The finite source trace is preserved even if the first dispatch is
itself the terminal return/leave. No extra loop trip is introduced. -/
theorem DispatchExit.replace_initial {c : Ctx} {start next regs : IL} {h after final : Heap} {exit : Ex}
    (same : runX (inflate_dispatch c) start h = runX (inflate_dispatch c) next after)
    (trace : DispatchExit c start h exit regs final) : DispatchExit c next after exit regs final := by
  obtain ⟨finish, heap, steps, stop⟩ := trace
  rcases steps.replace_initial same with ⟨rfl, rfl⟩ | replaced
  · exact ⟨next, after, .begin, same.symm.trans stop⟩
  · exact ⟨finish, heap, replaced, stop⟩
end Zlib.Inflate.Proofs.HeaderSourceTrace

namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.HeaderSourceTrace
set_option autoImplicit false

/-- A real inline control prefix changes the first dispatch cut without
consuming a mainwhile trip. Existing actual safety produces both bounded
runs; source trace uniqueness identifies their final results. No fresh
fuel or functional callee specification is assumed. -/
theorem while_inline_cut {c : Ctx} {start next : IL} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z zNext : ZStream} {s state : InflateState} {bs bsNext : List UInt8}
    (E : Env c h r zs z s) (origin : DefaultOriginState h r zs z s)
    (buffers : DispatchBuffers h r start bs) (bits : start.bits.toNat ≤ 39)
    (nextE : Env c after r zs zNext state) (nextOrigin : DefaultOriginState after r zs zNext state)
    (nextBuffers : DispatchBuffers after r next bsNext) (nextBits : next.bits.toNat ≤ 39)
    (same : runX (inflate_dispatch c) start h = runX (inflate_dispatch c) next after) :
    runX (xwhile (pure true) (inflate_dispatch c)) start h =
      runX (xwhile (pure true) (inflate_dispatch c)) next after := by
  obtain ⟨exit, regs, final, _z, _s, _used, _made, _bound, run, _current,
    _buffers, _bits, _sizes, _next, _count, _put, _left, trace⟩ := loop_actual_trace E origin buffers bits
  obtain ⟨exitNext, regsNext, finalNext, _zNext, _sNext, _usedNext, _madeNext, _boundNext,
    runNext, _currentNext, _buffersNext, _bitsNext, _sizesNext, _nextNext, _countNext,
    _putNext, _leftNext, traceNext⟩ := loop_actual_trace nextE nextOrigin nextBuffers nextBits
  obtain ⟨rfl, rfl, rfl⟩ := (trace.replace_initial same).unique traceNext
  exact run.trans runNext.symm

#print axioms DispatchPrefix.replace_initial
#print axioms DispatchExit.replace_initial
#print axioms while_inline_cut
end Zlib.Inflate.Proofs.WholeEpoch
