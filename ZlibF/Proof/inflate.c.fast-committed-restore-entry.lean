import ZlibF.Proof.«inflate.c.fast-committed-entry»

namespace Zlib.Inflate.Proofs.FunctionalEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inftrees
set_option autoImplicit false

/-- Actual RESTORE preserves installed tables, compatible table queries,
retained window and the already-observed output prefix, then the actual
fast prelude establishes a causal WordReady without future input. -/
theorem PayloadRepresentation.restore_committed_fast_entry
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState}
    {slow : IL} {bs : List UInt8}
    {L D : List Nat} {dict past current : List UInt8}
    (E : Env c h r zs z s)
    (representation : PayloadRepresentation h r zs z s slow bs
      L D (dict ++ past))
    (mode : DataTableMode s.mode)
    (flags : InstalledQueryFlags h s)
    (historyView : ∀ dest oo output,
      slow.put = .ref dest oo → Space.get h dest = some output →
      ZlibF.Math.LZ77Copy.writtenBytes output oo
        (slow.out_.toNat - slow.left.toNat) = current)
    (fast : (slow.have_ >= 6 && slow.left >= 258 &&
      slow.bits < 8) = true) :
    let restored := setI (r.put h (leaveStream z slow)) zs
      (leaveState s slow)
    ∃ (ctx : FastLoopContext) (q : Zlib.Inffast.L)
      (p : FastCommittedLoop.Parameters ctx),
      runX (RESTORE c.strm c.st) slow h =
        .ok ((.ok (), slow), restored) ∧
      C.run (fastEntryPrefix (some r) slow.out_) restored =
        .ok ((ctx.c, q), restored) ∧
      Nonempty (FastCommittedLoop.WordReady p restored q) ∧
      p.start = past ++ current ∧ p.initialWords = [] ∧
      p.input = bs ∧ p.entry = q ∧
      ctx.r = r ∧ ctx.zs = zs ∧
      ctx.z = leaveStream z slow ∧
      ctx.s = leaveState s slow ∧
      slow.put = .ref ctx.dest ctx.oo ∧
      ctx.leftTotal = slow.left ∧ ctx.outTotal = slow.out_ ∧
      q.in_ = slow.next ∧ q.bits = slow.bits ∧
      q.hold = slow.hold := by
  dsimp only
  obtain ⟨restoreRun, after⟩ := representation.restore E
  obtain ⟨origin, buffers, bits, tables, dictionary⟩ := after
  have dataMode : DataTableMode (leaveState s slow).mode := by
    change DataTableMode s.mode
    exact mode
  have capacity : 2 ^ (leaveState s slow).wbits.toNat = 32768 := by
    rw [origin.toDefaultStateJ.window]
    decide
  have restoredDictionary : InflateDictionary
      (setI (r.put h (leaveStream z slow)) zs (leaveState s slow))
      (leaveState s slow)
      ((dict ++ past).drop ((dict ++ past).length - 32768)) := by
    simpa only [capacity] using dictionary
  have restoredFlags : InstalledQueryFlags
      (setI (r.put h (leaveStream z slow)) zs (leaveState s slow))
      (leaveState s slow) :=
    flags.restore representation.1.good.live.hs slow
  have restoredHistory : ∀ dest oo output,
      slow.put = .ref dest oo →
      Space.get (setI (r.put h (leaveStream z slow)) zs
        (leaveState s slow)) dest = some output →
      ZlibF.Math.LZ77Copy.writtenBytes output oo
        (slow.out_.toNat - slow.left.toNat) = current := by
    intro dest oo output ptr get
    have oldGet : Space.get h dest = some output := by
      rw [byte_view_get_setI, byte_view_get_stream_put] at get
      exact get
    exact historyView dest oo output ptr oldGet
  obtain ⟨ctx, q, p, prefixRun, wordReady,
    start, words, raw, entry, sameR, sameZs,
    sameZ, sameS, put, left, out, input,
    heldBits, heldHold⟩ :=
    fastEntryPrefix_committed_general
      origin.toDefaultStateJ buffers dataMode
      rfl rfl rfl rfl rfl rfl tables restoredFlags
      restoredDictionary restoredHistory fast
  exact ⟨ctx, q, p, restoreRun, prefixRun, wordReady,
    start, words, raw, entry, sameR, sameZs,
    sameZ, sameS, put, left, out, input, heldBits, heldHold⟩

#print axioms PayloadRepresentation.restore_committed_fast_entry
end Zlib.Inflate.Proofs.FunctionalEpoch
