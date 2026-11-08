import ZlibF.Proof.«inflate.c.fast-view-public-buffers»
import ZlibF.Proof.«inflate.c.fast-view-callee-progress»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The actual fast call retains its complete buffer packet and either
reaches a block/error boundary or produces bytes, with the same public count. -/
theorem inflate_fast_default_view_buffers_progress
    {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {slow : IL} {bs : List UInt8}
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs) (mode : DataTableMode s.mode)
    (inputCursor : z.next_in = slow.next) (inputCount : z.avail_in = slow.have_)
    (outputCursor : z.next_out = slow.put) (outputCount : z.avail_out = slow.left)
    (stateHold : s.hold = slow.hold) (stateBits : s.bits = slow.bits)
    (fast : (slow.have_ >= 6 && slow.left >= 258 && slow.bits < 8) = true) :
    ∃ finished zNext sNext used made regs, used ≤ bs.length ∧
      C.run (Zlib.Inffast.inflate_fast (some r) slow.out_) h = .ok ((), finished) ∧
      DefaultStateJ finished r zs zNext sNext ∧
      DispatchBuffers finished r regs (bs.drop used) ∧ ByteViewSizes h finished ∧
      regs.next = inputAdvance slow.next used ∧ regs.have_.toNat + used = slow.have_.toNat ∧
      regs.put = inputAdvance slow.put made ∧ regs.left.toNat + made = slow.left.toNat ∧
      regs.bits.toNat < 8 ∧ regs.bits.toNat ≤ slow.bits.toNat + 8 * used ∧
      sNext.window = s.window ∧
      (sNext.mode = s.mode ∨ sNext.mode = TYPE ∨ sNext.mode = BAD) ∧
      regs = { slow with
        put := zNext.next_out, left := zNext.avail_out,
        next := zNext.next_in, have_ := zNext.avail_in, hold := sNext.hold, bits := sNext.bits } ∧
      (sNext.mode = BAD ∨ sNext.mode = TYPE ∨ 0 < made) := by
  obtain ⟨finished, zNext, sNext, used, made, regs, bound, run, current,
    packet, sizes, next, count, put, left, small, budget, window, modes, shape⟩ :=
    inflate_fast_default_view_buffers invariant buffers mode inputCursor
      inputCount outputCursor outputCount stateHold stateBits fast
  obtain ⟨progHeap, progZ, progS, progUsed, progMade, progRun,
    progJ, progAccounting, progress⟩ :=
    inflate_fast_default_view_progress invariant buffers mode inputCursor
      inputCount outputCursor outputCount stateHold stateBits fast
  have sameHeap : finished = progHeap := congrArg Prod.snd
    (Except.ok.inj (run.symm.trans progRun))
  subst progHeap
  have sameZ : progZ = zNext := Option.some.inj
    (progJ.good.live.hz.symm.trans current.good.live.hz)
  have sameS : progS = sNext := Option.some.inj
    (progJ.good.live.hs.symm.trans current.good.live.hs)
  subst progZ
  subst progS
  have sameMade : progMade = made := by
    have leftEq : regs.left = zNext.avail_out := congrArg IL.left shape
    have first := left
    rw [leftEq] at first
    have second : zNext.avail_out.toNat + progMade = slow.left.toNat := by
      simpa only [outputCount] using progAccounting.2.2.2.1
    omega
  subst progMade
  exact ⟨finished, zNext, sNext, used, made, regs, bound, run, current,
    packet, sizes, next, count, put, left, small, budget, window, modes, shape, progress⟩

#print axioms inflate_fast_default_view_buffers_progress
end Zlib.Inflate.Proofs
