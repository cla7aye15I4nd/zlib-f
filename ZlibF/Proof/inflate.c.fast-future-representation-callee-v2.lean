import ZlibF.Proof.«inflate.c.fast-future-restore-entry»
import ZlibF.Proof.«inflate.c.fast-future-callee-prefix-cursor»

namespace Zlib.Inflate.Proofs.FunctionalEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inftrees
set_option autoImplicit false

/-- At any actual payload cut carrying the transported representation,
RESTORE and the complete fast callee execute on arbitrary retained history
and arbitrary current-call output. No public protocol predicate is assumed
at an intermediate heap. -/
theorem PayloadRepresentation.restore_fast_callee_future_v2
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState}
    {slow : IL} {bs : List UInt8} {L D : List Nat}
    {oldDict past current : List UInt8}
    {future tail : List Bool} {decoded : List UInt8}
    (E : Env c h r zs z s)
    (representation : PayloadRepresentation h r zs z s slow bs
      L D (oldDict ++ past))
    (mode : DataTableMode s.mode)
    (distanceFlags : ∀ (ref : CodeRef) (offset : Nat)
      (codes : Array Code), s.distcode = .ref ref offset →
      Space.get h ref = some codes →
      Zlib.Inftrees.Spec.FastTableFlags.QueryCompatible
        DISTS codes offset s.distbits.toNat)
    (historyView : ∀ dest oo output,
      slow.put = .ref dest oo → Space.get h dest = some output →
      ZlibF.Math.LZ77Copy.writtenBytes output oo
        (slow.out_.toNat - slow.left.toNat) = current)
    (parsed : Symbols L D oldDict (past ++ current)
      (stream slow bs ++ future) tail decoded)
    (fast : (slow.have_ >= 6 && slow.left >= 258 &&
      slow.bits < 8) = true) :
    let restored := setI (r.put h (leaveStream z slow)) zs
      (leaveState s slow)
    ∃ (ctx : FastLoopContext) (q : Zlib.Inffast.L)
      (finished : Heap) (zNext : ZStream) (sNext : InflateState)
      (used made : Nat) (regs : IL) (result : Zlib.Inffast.L)
      (after : Heap) (array : Array UInt8) (off : Nat)
      (next : List UInt8),
      runX (RESTORE c.strm c.st) slow h =
        .ok ((.ok (), slow), restored) ∧
      C.run (fastEntryPrefix (some r) slow.out_) restored =
        .ok ((ctx.c, q), restored) ∧
      C.run (Zlib.Inffast.inflate_fast (some r) slow.out_)
        restored = .ok ((), finished) ∧
      DefaultStateJ finished r zs zNext sNext ∧
      BufferFrame restored finished
        (fun b => StreamRoot r b ∨ b = zs)
        [⟨slow.put, made⟩] ∧
      FastFutureExitCursor ctx L D
        ((oldDict ++ past).drop
          ((oldDict ++ past).length - 32768))
        future tail (decoded.drop past.length) after result ∧
      zNext.next_out = result.out ∧
      result.out = .ref ctx.dest off ∧
      Space.get finished ctx.dest = some array ∧
      ZlibF.Math.LZ77Copy.writtenBytes array off
        (off - ctx.bg) = next ∧
      next <+: decoded.drop past.length ∧
      regs.next = inputAdvance slow.next used ∧
      regs.have_.toNat + used = slow.have_.toNat ∧
      regs.put = inputAdvance slow.put made ∧
      regs.left.toNat + made = slow.left.toNat := by
  dsimp only
  obtain ⟨outputPrefix, ctx, q, restoreRun, prefixRun,
    semantic, sameR, sameIndex, notBroken⟩ :=
    representation.restore_fast_entry_future E mode
      distanceFlags historyView parsed fast
  obtain ⟨_sameRestore, restoredRep⟩ :=
    representation.restore E
  obtain ⟨restoredOrigin, restoredBuffers, _restoredBits,
    _restoredTables, _restoredDictionary⟩ := restoredRep
  have restoredMode : DataTableMode (leaveState s slow).mode := by
    change DataTableMode s.mode
    exact mode
  obtain ⟨finished, zNext, sNext, used, made, regs,
    result, after, array, off, next, callRun, current,
    _finalBuffers, storedPut, _usedBound, nextPtr,
    haveCount, putPtr, leftCount, _small, _budget,
    _loopRun, semanticExit, _suffixRun, resultPut,
    physical, _getAfter, finalGet, written, prefixBytes⟩ :=
    semantic.callee_output_prefix_cursor
      restoredOrigin.toDefaultStateJ restoredBuffers
      restoredMode rfl rfl rfl rfl rfl rfl fast prefixRun
  obtain ⟨frameHeap, frameZ, frameS, frameUsed,
    frameMade, frameRun, frameJ, accounting, frame⟩ :=
    inflate_fast_default_view_public_exact_frame
      restoredOrigin.toDefaultStateJ restoredBuffers restoredMode
      rfl rfl rfl rfl rfl rfl fast
  have sameHeap : finished = frameHeap := congrArg Prod.snd
    (Except.ok.inj (callRun.symm.trans frameRun))
  subst frameHeap
  have sameStream : frameZ = zNext := Option.some.inj
    (frameJ.good.live.hz.symm.trans current.good.live.hz)
  subst frameZ
  have pointer : zNext.next_out = inputAdvance slow.put made :=
    storedPut.symm.trans putPtr
  have framePointer : zNext.next_out = advance slow.put frameMade :=
    accounting.2.2.2.2.2.1
  have sameMade : frameMade = made := by
    cases sourcePtr : slow.put with
    | null =>
        exact False.elim (restoredBuffers.output.nonnull sourcePtr)
    | ref dest off =>
        rw [sourcePtr] at pointer framePointer
        simp only [inputAdvance, advance] at pointer framePointer
        have equals := pointer.symm.trans framePointer
        have offsets := (Ptr.ref.inj equals).2
        omega
  subst frameMade
  exact ⟨ctx, q, finished, zNext, sNext, used, made,
    regs, result, after, array, off, next, restoreRun,
    prefixRun, callRun, current, frame, semanticExit, resultPut,
    physical, finalGet, written, prefixBytes,
    nextPtr, haveCount, putPtr, leftCount⟩

#print axioms PayloadRepresentation.restore_fast_callee_future_v2
end Zlib.Inflate.Proofs.FunctionalEpoch
