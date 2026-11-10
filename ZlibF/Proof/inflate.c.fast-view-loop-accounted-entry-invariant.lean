import ZlibF.Proof.«inflate.c.fast-view-loop-accounted-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- The actual fast prelude and loop retain a call-entry input account on
every nonbreaking exit, for general represented caller buffers. -/
theorem fastEntryLoop_account_run
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
    ∃ (ctx : FastLoopContext) (q result : Zlib.Inffast.L)
        (after : Heap) (startOff : Nat),
      C.run (fastEntryPrefix (some r) slow.out_) h =
        .ok ((ctx.c, q), h) ∧
      q.in_ = .ref ctx.inputRef startOff ∧
      C.run (fastEntryLoop (some r) slow.out_) h =
        .ok ((ctx.c, result), after) ∧
      FastLoopExit ctx after result ∧
      (result.broke = false →
        FastInputAccount ctx startOff q.bits.toNat result) := by
  obtain ⟨ctx, q, prefixRun, ready⟩ :=
    fastEntryPrefix_ready invariant buffers mode
      inputCursor inputCount outputCursor outputCount
      stateHold stateBits fast
  obtain ⟨startOff, result, after, cursor, loopRun,
    final, account⟩ := ready.run_account_from_entry
  refine ⟨ctx, q, result, after, startOff,
    prefixRun, cursor, ?_, final, account⟩
  change (fastEntryPrefix (some r) slow.out_) h =
      .ok ((ctx.c, q), h) at prefixRun
  change (cdoWhile (Zlib.Inffast.inflate_fast_body ctx.c)
      (fun q => do
        if q.broke then pure (false, q)
        else if ← Ptr.lt q.in_ ctx.c.last then
          pure (← Ptr.lt q.out ctx.c.end_, q)
        else pure (false, q)) q) h =
      .ok (result, after) at loopRun
  change (fastEntryLoop (some r) slow.out_) h =
    .ok ((ctx.c, result), after)
  unfold fastEntryLoop
  simp only [bind_app, prefixRun, loopRun, pure_app]

/-- Actual RESTORE followed by the translated fast prelude and loop retains
the call-entry bit budget on every nonbreaking fast exit. -/
theorem default_fast_loop_account_after_restore
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
        (after : Heap) (startOff : Nat),
      C.run (leaveRestore c slow) h = .ok ((), restored) ∧
      C.run (fastEntryPrefix (some r) slow.out_) restored =
        .ok ((ctx.c, q), restored) ∧
      C.run (fastEntryLoop (some r) slow.out_) restored =
        .ok ((ctx.c, result), after) ∧
      FastLoopExit ctx after result ∧
      (result.broke = false →
        FastInputAccount ctx startOff q.bits.toNat result) := by
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
  have dataMode : DataTableMode (leaveState s slow).mode :=
    mode
  obtain ⟨ctx, q, result, after, startOff,
    prefixRun, cursor, combinedRun, final, account⟩ :=
    fastEntryLoop_account_run current packet dataMode
      rfl rfl rfl rfl rfl rfl fast
  exact ⟨ctx, q, result, after, startOff,
    leaveRestore_run E, prefixRun, combinedRun,
    final, account⟩

end Zlib.Inflate.Proofs
