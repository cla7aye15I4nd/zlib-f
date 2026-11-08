import ZlibF.Proof.«inflate.c.fast-view-whole-normalized»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The actual fast call retains all caller fields and the source-bit
budget for the same public byte-consumption count. -/
theorem inflate_fast_default_view_caller_budget
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
      C.run (Zlib.Inffast.inflate_fast (some r) slow.out_) h = .ok ((), finished) ∧
      DefaultStateJ finished r zs zNext sNext ∧
      StreamAccounting z zNext used made ∧
      ByteViewSizes h finished ∧ sNext.window = s.window ∧
      (sNext.mode = s.mode ∨ sNext.mode = TYPE ∨ sNext.mode = BAD) ∧
      sNext.bits.toNat < 8 ∧
      (∀ ref : BRef, Space.ro finished ref = Space.ro h ref) ∧
      LiveChange h finished (fun _ => False) (fun _ => False) ∧
      finished.nalloc = h.nalloc ∧
      sNext.bits.toNat ≤ slow.bits.toNat + 8 * used := by
  obtain ⟨finished, zNext, sNext, used, made, run, current,
    accounting, sizes, window, modes, small, readonly, live, nalloc⟩ :=
    inflate_fast_default_view_caller_fields invariant buffers mode inputCursor
      inputCount outputCursor outputCount stateHold stateBits fast
  obtain ⟨budgetHeap, budgetZ, budgetS, budgetUsed, budgetMade,
    budgetRun, budgetGood, budgetAccounting, budget⟩ :=
    inflate_fast_default_view_accounting_budget invariant buffers mode inputCursor
      inputCount outputCursor outputCount stateHold stateBits fast
  have sameHeap : finished = budgetHeap := congrArg Prod.snd
    (Except.ok.inj (run.symm.trans budgetRun))
  subst budgetHeap
  have sameZ : budgetZ = zNext := Option.some.inj
    (budgetGood.live.hz.symm.trans current.good.live.hz)
  have sameS : budgetS = sNext := Option.some.inj
    (budgetGood.live.hs.symm.trans current.good.live.hs)
  subst budgetZ
  subst budgetS
  have sameUsed : budgetUsed = used := by
    have first := accounting.2.2.1
    have second := budgetAccounting.2.2.1
    omega
  subst budgetUsed
  exact ⟨finished, zNext, sNext, used, made, run, current,
    accounting, sizes, window, modes, small, readonly, live, nalloc, budget⟩

#print axioms inflate_fast_default_view_caller_budget
end Zlib.Inflate.Proofs
