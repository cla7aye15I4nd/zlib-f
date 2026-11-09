import ZlibF.Proof.«inflate.c.local-fast-exact-output-callee»

namespace Zlib.Inflate.Local
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- The actual fast call's exact output interval has precisely the count
reported by its public stream accounting. -/
theorem inflate_fast_default_view_public_exact_frame
    {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState}
    {slow : IL} {bs : List UInt8}
    (invariant : LocalStateJ h cutoff r zs z s)
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
    ∃ finished zNext sNext used produced,
      C.run (Zlib.Inffast.inflate_fast (some r) slow.out_) h =
        .ok ((), finished) ∧
      LocalStateJ finished cutoff r zs zNext sNext ∧
      StreamAccounting z zNext used produced ∧
      BufferFrame h finished (fun b => StreamRoot r b ∨ b = zs)
        [⟨slow.put, produced⟩] := by
  obtain ⟨finished, zNext, sNext, made, run, nextJ,
    nextOut, madeBound, frame⟩ :=
    inflate_fast_default_view_exact_frame invariant buffers mode
      inputCursor inputCount outputCursor outputCount
      stateHold stateBits fast
  obtain ⟨other, otherZ, otherS, used, produced,
    otherRun, otherPost⟩ :=
    inflate_fast_local_view_post invariant buffers mode
      inputCursor inputCount outputCursor outputCount
      stateHold stateBits fast
  have accounting := otherPost.accounting
  have sameHeap : finished = other :=
    congrArg Prod.snd (Except.ok.inj (run.symm.trans otherRun))
  subst other
  have sameZ : zNext = otherZ := Option.some.inj
    (nextJ.good.live.hz.symm.trans otherPost.invariant.good.live.hz)
  subst otherZ
  have outAccounting : zNext.next_out = advance z.next_out produced :=
    accounting.2.2.2.2.2.1
  rw [outputCursor] at outAccounting
  have nonnull := buffers.output.nonnull
  cases ptr : slow.put with
  | null => exact False.elim (nonnull ptr)
  | ref dest off =>
    have madeEq : made = produced := by
      rw [ptr] at nextOut outAccounting
      simp only [advance] at nextOut outAccounting
      have offset :=
        (Ptr.ref.inj (nextOut.symm.trans outAccounting)).2
      omega
    subst produced
    exact ⟨finished, zNext, sNext, used, made, run, nextJ,
      accounting, by simpa only [ptr] using frame⟩

#print axioms inflate_fast_default_view_public_exact_frame

end Zlib.Inflate.Local
