import ZlibF.Proof.«inflate.c.fast-view-loop-entry-core»
import ZlibF.Proof.«inflate.c.fast-view-loop-actual-invariant»
import ZlibF.Proof.«inflate.c.leave-default-state»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false


/-- The real fast loop is safe from a synchronized initial call packet,
without requiring distinct input and output allocations. -/
theorem FastLoopReady.run_initial
    {ctx : FastLoopContext} {h : Heap} {q : Zlib.Inffast.L}
    {slow : IL} {bs : List UInt8} {off : Nat}
    (packet : FastInputPacket h slow bs q)
    (invariant : DefaultStateJ h ctx.r ctx.zs ctx.z ctx.s)
    (buffers : DispatchBuffers h ctx.r slow bs)
    (codesGet : Space.get h ctx.codeRef = some ctx.codes)
    (distGet : Space.get h ctx.distRef = some ctx.distCodes)
    (leftEq : slow.left = ctx.leftTotal)
    (outEq : slow.out_ = ctx.outTotal)
    (putPtr : slow.put = .ref ctx.dest ctx.oo)
    (nextPtr : slow.next = .ref ctx.inputRef off)
    (lastPtr : ctx.c.last = .ref ctx.inputRef
      (off + slow.have_.toNat - 5))
    (inputMargin : 6 ≤ slow.have_.toNat)
    (bitsBound : slow.bits.toNat ≤ 30)
    (outInit : q.out = slow.put) :
    ∃ result after,
      C.run (cdoWhile (Zlib.Inffast.inflate_fast_body ctx.c)
        (fun q => do
          if q.broke then pure (false, q)
          else if ← Ptr.lt q.in_ ctx.c.last then
            pure (← Ptr.lt q.out ctx.c.end_, q)
          else pure (false, q)) q) h =
          .ok (result, after) ∧
      FastLoopExit ctx after result :=
  (FastLoopReady.initial packet invariant buffers codesGet
    distGet leftEq outEq putPtr nextPtr lastPtr inputMargin
    bitsBound outInit).run


/-- Actual RESTORE reaches a heap on which the general fast-loop entry
packet can be constructed. No separation by allocation identity is used. -/
theorem default_fast_loop_after_restore
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState}
    {slow : IL} {bs : List UInt8}
    (E : Env c h r zs z s)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    (mode : DataTableMode s.mode)
    (fast : (slow.have_ >= 6 && slow.left >= 258 &&
      slow.bits < 8) = true) :
    let restored :=
      setI (r.put h (leaveStream z slow)) zs (leaveState s slow)
    ∃ (ctx : FastLoopContext) (q : Zlib.Inffast.L),
      C.run (leaveRestore c slow) h = .ok ((), restored) ∧
      ctx.c.strm = c.strm ∧ ctx.c.state = c.st ∧
      q.in_ = slow.next ∧ q.out = slow.put ∧
      FastLoopReady ctx restored q := by
  dsimp only
  have bitCount : slow.bits.toNat ≤ 39 := by
    have margins : (6 ≤ slow.have_ ∧ 258 ≤ slow.left) ∧
        slow.bits < 8 := by
      simpa only [Bool.and_eq_true, decide_eq_true_eq]
        using fast
    have small : slow.bits.toNat < 8 := by
      simpa [UInt32.lt_iff_toNat_lt] using margins.2
    omega
  have current := invariant.restore E buffers bitCount
  have views : ∀ ref : BRef,
      (Space.get
        (setI (r.put h (leaveStream z slow)) zs
          (leaveState s slow)) ref : Option (Array UInt8)) =
        Space.get h ref := by
    intro ref
    rw [byte_view_get_setI, byte_view_get_stream_put]
  have readonly : ∀ ref : BRef,
      Space.ro
        (setI (r.put h (leaveStream z slow)) zs
          (leaveState s slow)) ref = Space.ro h ref := by
    intro ref
    rw [byte_view_ro_setI, byte_view_ro_stream_put]
  have packet := buffers.byte_views invariant.good
    current.good rfl views readonly
  have dataMode : DataTableMode (leaveState s slow).mode := mode
  obtain ⟨ctx, q, cursor, output, hold, bits,
    strm, state, _, _, _, _, _, _, _, _, ready⟩ :=
    default_fast_loop_entry current packet dataMode fast
  refine ⟨ctx, q, leaveRestore_run E, ?_, ?_,
    cursor, output, ready⟩
  · rw [strm]
    exact E.strm.symm
  · rw [state]
    exact E.st.symm

/-- The restored default data-mode caller reaches a terminating actual
fast-body loop on general represented buffer views. -/
theorem default_fast_loop_after_restore_run
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState}
    {slow : IL} {bs : List UInt8}
    (E : Env c h r zs z s)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    (mode : DataTableMode s.mode)
    (fast : (slow.have_ >= 6 && slow.left >= 258 &&
      slow.bits < 8) = true) :
    let restored :=
      setI (r.put h (leaveStream z slow)) zs (leaveState s slow)
    ∃ (ctx : FastLoopContext) (q result : Zlib.Inffast.L)
        (after : Heap),
      C.run (leaveRestore c slow) h = .ok ((), restored) ∧
      ctx.c.strm = c.strm ∧ ctx.c.state = c.st ∧
      C.run (cdoWhile (Zlib.Inffast.inflate_fast_body ctx.c)
        (fun q => do
          if q.broke then pure (false, q)
          else if ← Ptr.lt q.in_ ctx.c.last then
            pure (← Ptr.lt q.out ctx.c.end_, q)
          else pure (false, q)) q) restored =
          .ok (result, after) ∧
      FastLoopExit ctx after result := by
  dsimp only
  obtain ⟨ctx, q, restore, strm, state, _, _, ready⟩ :=
    default_fast_loop_after_restore E invariant buffers
      mode fast
  obtain ⟨result, after, run, final⟩ := ready.run
  exact ⟨ctx, q, result, after, restore, strm, state,
    run, final⟩

end Zlib.Inflate.Proofs
