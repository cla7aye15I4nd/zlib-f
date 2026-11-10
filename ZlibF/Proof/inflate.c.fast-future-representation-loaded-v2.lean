import ZlibF.Proof.«inflate.c.fast-future-representation-callee-v6»
import ZlibF.Proof.«inflate.c.fast-load-frame»

namespace Zlib.Inflate.Proofs.FunctionalEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inftrees
set_option autoImplicit false

/-- The actual RESTORE, complete fast callee and LOAD sequence preserves
its exact new output interval through TYPE bookkeeping. The preexisting
current-call bytes are retained as the prefix of the independently decoded
physical output. -/
theorem PayloadRepresentation.restore_fast_callee_loaded_v2
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
    ∃ (finished loadedHeap : Heap) (zNext : ZStream)
      (loadedState : InflateState) (loaded : IL)
      (ctx : FastLoopContext) (array : Array UInt8)
      (off made : Nat) (next more : List UInt8),
      runX (RESTORE c.strm c.st) slow h =
        .ok ((.ok (), slow), restored) ∧
      C.run (Zlib.Inffast.inflate_fast (some r) slow.out_)
        restored = .ok ((), finished) ∧
      runX (inflateAfterFast c) slow finished =
        .ok ((.ok (), loaded), loadedHeap) ∧
      DefaultStateJ loadedHeap r zs zNext loadedState ∧
      BufferFrame restored loadedHeap
        (fun b => StreamRoot r b ∨ b = zs)
        [⟨slow.put, made⟩] ∧
      loaded.put = .ref ctx.dest off ∧
      loaded.put = inputAdvance slow.put made ∧
      off ≤ array.size ∧
      loaded.left.toNat + made = slow.left.toNat ∧
      loaded.out_ = slow.out_ ∧
      Space.get loadedHeap ctx.dest = some array ∧
      ZlibF.Math.LZ77Copy.writtenBytes array off made = more ∧
      more.length = made ∧ next = current ++ more ∧
      next <+: decoded.drop past.length ∧
      loadedState.check = (leaveState s slow).check ∧
      zNext.adler = (leaveStream z slow).adler ∧
      loadedState.wrap = (leaveState s slow).wrap ∧
      loadedState.flags = (leaveState s slow).flags := by
  dsimp only
  let restored := setI (r.put h (leaveStream z slow)) zs (leaveState s slow)
  obtain ⟨ctx, q, finished, zNext, sNext, used, made,
    regs, result, after, array, off, next, restoreRun,
    prefixRun, callRun, currentJ, frame, semanticExit,
    resultPut, physical, finalGet, written, prefixBytes,
    nextPtr, haveCount, putPtr, leftCount,
    more, moreLength, nextAppend, moreBytes,
    check, adler, wrap, flags, count, slowOrder,
    fastPut, outputBound⟩ :=
    representation.restore_fast_callee_future_v6 E mode
      distanceFlags historyView parsed fast
  have environment : Env c finished r zs zNext sNext :=
    ⟨E.strm, E.st, currentJ.good.live.hz,
      currentJ.good.live.hs⟩
  obtain ⟨loaded, loadedHeap, loadedState, loadRun,
    loadedJ, finalFrame, loadedPut, loadedLeft,
    loadedOut, loadedCount, loadedCheck,
    loadedWrap, loadedFlags, views⟩ :=
    inflateAfterFast_frame_credit_fields (l := slow)
      environment currentJ count frame
  have finalGet : Space.get loadedHeap ctx.dest = some array :=
    views ctx.dest array finalGet
  refine ⟨finished, loadedHeap, zNext, loadedState,
    loaded, ctx, array, off, made, next, more,
    restoreRun, callRun, loadRun, loadedJ, finalFrame,
    ?_, ?_, outputBound, loadedCount, loadedOut, finalGet,
    moreBytes, moreLength, nextAppend, prefixBytes,
    ?_, adler, ?_, ?_⟩
  · exact loadedPut.trans (resultPut.trans physical)
  · exact loadedPut.trans fastPut
  · exact loadedCheck.trans check
  · exact loadedWrap.trans wrap
  · exact loadedFlags.trans flags

#print axioms PayloadRepresentation.restore_fast_callee_loaded_v2
end Zlib.Inflate.Proofs.FunctionalEpoch
