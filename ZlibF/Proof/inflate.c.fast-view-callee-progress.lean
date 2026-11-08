import ZlibF.Proof.«inflate.c.fast-view-whole-break-mode»
import ZlibF.Proof.«inflate.c.fast-view-public-accounting»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- A successful actual fast call either reaches BAD or TYPE or produces
at least one output byte. The byte count is the public stream account. -/
theorem inflate_fast_default_view_progress
    {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState}
    {slow : IL} {bs : List UInt8}
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    (mode : DataTableMode s.mode)
    (inputCursor : z.next_in = slow.next)
    (inputCount : z.avail_in = slow.have_)
    (outputCursor : z.next_out = slow.put)
    (outputCount : z.avail_out = slow.left)
    (stateHold : s.hold = slow.hold)
    (stateBits : s.bits = slow.bits)
    (fast : (slow.have_ >= 6 && slow.left >= 258 &&
      slow.bits < 8) = true) :
    ∃ finished zNext sNext used made,
      C.run (Zlib.Inffast.inflate_fast (some r) slow.out_) h =
        .ok ((), finished) ∧
      DefaultStateJ finished r zs zNext sNext ∧
      StreamAccounting z zNext used made ∧
      (sNext.mode = BAD ∨ sNext.mode = TYPE ∨ 0 < made) := by
  obtain ⟨finished, zNext, sNext, used, made,
    run, current, accounting⟩ :=
    inflate_fast_default_view_public_core invariant buffers mode
      inputCursor inputCount outputCursor outputCount
      stateHold stateBits fast
  obtain ⟨modeFinished, modeZ, modeS, result,
    modeRun, modeJ, storedOut, advanced, brokenMode⟩ :=
    inflate_fast_default_view_broken_mode invariant buffers mode
      inputCursor inputCount outputCursor outputCount
      stateHold stateBits fast
  have sameHeap : finished = modeFinished :=
    congrArg Prod.snd (Except.ok.inj (run.symm.trans modeRun))
  subst modeFinished
  have sameZ : zNext = modeZ := Option.some.inj
    (current.good.live.hz.symm.trans modeJ.good.live.hz)
  have sameS : sNext = modeS := Option.some.inj
    (current.good.live.hs.symm.trans modeJ.good.live.hs)
  refine ⟨finished, zNext, sNext, used, made,
    run, current, accounting, ?_⟩
  by_cases broken : result.broke = true
  · have kinds := brokenMode broken
    rw [← sameS] at kinds
    rcases kinds with bad | terminal
    · exact Or.inl bad
    · exact Or.inr (Or.inl terminal)
  · have clear : result.broke = false := by
      cases flag : result.broke <;> simp_all
    have moved := advanced clear
    rw [← sameZ] at moved
    have pointer := accounting.2.2.2.2.2.1
    by_cases zero : made = 0
    · rw [zero] at pointer
      have unchanged : advance z.next_out 0 = z.next_out := by
        cases z.next_out <;> rfl
      rw [unchanged] at pointer
      exact False.elim (moved pointer)
    · exact Or.inr (Or.inr (by omega))

#print axioms inflate_fast_default_view_progress

end Zlib.Inflate.Proofs
