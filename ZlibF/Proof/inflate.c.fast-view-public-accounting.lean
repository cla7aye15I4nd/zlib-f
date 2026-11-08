import ZlibF.Proof.«inflate.c.fast-view-public-accounting-budget»
import ZlibF.Proof.«inflate.c.fast-view-entire-safe»
import ZlibF.Proof.«inflate.c.fast-view-loop-stream-fields-frame»
import ZlibF.Proof.«inflate.c.fast-writeback-public»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec Zlib.Inffast.Proofs
set_option autoImplicit false

/-- The complete translated fast call accounts for byte movements against
the original public stream, including every broken decoder exit. -/
theorem inflate_fast_default_view_accounting
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
    ∃ finished zNext sNext used produced,
      C.run (Zlib.Inffast.inflate_fast (some r) slow.out_) h =
        .ok ((), finished) ∧
      Good finished r zs zNext sNext ∧
      StreamAccounting z zNext used produced := by
  obtain ⟨finished, zNext, sNext, used, produced, run, good, accounting, budget⟩ :=
    inflate_fast_default_view_accounting_budget invariant buffers mode
      inputCursor inputCount outputCursor outputCount stateHold stateBits fast
  exact ⟨finished, zNext, sNext, used, produced, run, good, accounting⟩

/-- The actual fast call simultaneously retains the initialized decoder
relation and accounts for bytes against its entry stream. -/
theorem inflate_fast_default_view_public_core
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
    ∃ finished zNext sNext used produced,
      C.run (Zlib.Inffast.inflate_fast (some r) slow.out_) h =
        .ok ((), finished) ∧
      DefaultStateJ finished r zs zNext sNext ∧
      StreamAccounting z zNext used produced := by
  obtain ⟨finished, zNext, sNext, run, invariantNext⟩ :=
    inflate_fast_default_view_J invariant buffers mode
      inputCursor inputCount outputCursor outputCount
      stateHold stateBits fast
  obtain ⟨other, otherZ, otherS, used, produced,
    otherRun, good, accounting⟩ :=
    inflate_fast_default_view_accounting invariant buffers mode
      inputCursor inputCount outputCursor outputCount
      stateHold stateBits fast
  have same : finished = other := congrArg Prod.snd
    (Except.ok.inj (run.symm.trans otherRun))
  subst other
  have sameZ : zNext = otherZ := Option.some.inj
    (invariantNext.good.live.hz.symm.trans good.live.hz)
  have sameS : sNext = otherS := Option.some.inj
    (invariantNext.good.live.hs.symm.trans good.live.hs)
  subst otherZ
  subst otherS
  exact ⟨finished, zNext, sNext, used, produced,
    run, invariantNext, accounting⟩

#print axioms inflate_fast_default_view_accounting
#print axioms inflate_fast_default_view_public_core
end Zlib.Inflate.Proofs
