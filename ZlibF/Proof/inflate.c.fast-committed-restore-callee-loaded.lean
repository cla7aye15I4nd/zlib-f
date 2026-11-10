import ZlibF.Proof.«inflate.c.fast-committed-callee-loaded-source»
import ZlibF.Proof.«inflate.c.fast-committed-restore-entry»

namespace Zlib.Inflate.Proofs.FunctionalEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.FastCommittedLoop
set_option autoImplicit false

/-- Actual RESTORE, the complete translated fast callee, and LOAD preserve
a causal accepted-word certificate on arbitrary available input. Normal
and EOB include exact post-LOAD source bits; BAD is an actual state result.
This does not assume a future source or desired decoded output. -/
theorem PayloadRepresentation.restore_committed_fast_loaded
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
    ∃ (ctx : FastLoopContext) (p : Parameters ctx)
      (finished loadedHeap loopHeap : Heap)
      (zNext : ZStream) (loadedState : InflateState)
      (loaded : IL) (result : Zlib.Inffast.L)
      (used made : Nat),
      runX (RESTORE c.strm c.st) slow h =
        .ok ((.ok (), slow), restored) ∧
      C.run (Zlib.Inffast.inflate_fast (some r) slow.out_)
        restored = .ok ((), finished) ∧
      runX (inflateAfterFast c) slow finished =
        .ok ((.ok (), loaded), loadedHeap) ∧
      DefaultStateJ loadedHeap r zs zNext loadedState ∧
      WordExit p loopHeap result ∧
      LoadedSourceOutcome p loopHeap result loaded used ∧
      p.start = past ++ current ∧ p.initialWords = [] ∧
      p.input = bs ∧
      loaded.have_.toNat + used = bs.length ∧
      loaded.left.toNat + made = slow.left.toNat := by
  dsimp only
  obtain ⟨ctx, q, p, restoreRun, prefixRun, wordReady,
    start, words, raw, entry, sameR, sameZs,
    sameZ, sameS, put, left, out, input, heldBits,
    heldHold⟩ :=
    representation.restore_committed_fast_entry E mode
      flags historyView fast
  obtain ⟨ready⟩ := wordReady
  obtain ⟨restoredRun, afterRep⟩ := representation.restore E
  obtain ⟨origin, buffers, bits, tables, dictionary⟩ := afterRep
  have dataMode : DataTableMode (leaveState s slow).mode := by
    change DataTableMode s.mode
    exact mode
  obtain ⟨finished, loadedHeap, zNext, loadedState,
    loaded, used, made, result, loopHeap, callRun, loadRun,
    currentJ, exit, outcome, haveCount, leftCount⟩ :=
    ready.callee_loaded_source
      ⟨E.strm, E.st, origin.good.live.hz,
        origin.good.live.hs⟩
      origin.toDefaultStateJ buffers dataMode
      rfl rfl rfl rfl rfl rfl fast prefixRun
      entry raw heldBits sameR sameZs
  exact ⟨ctx, p, finished, loadedHeap, loopHeap,
    zNext, loadedState, loaded, result, used, made,
    restoreRun, callRun, loadRun, currentJ,
    exit, outcome, start, words, raw, haveCount, leftCount⟩

#print axioms PayloadRepresentation.restore_committed_fast_loaded
end Zlib.Inflate.Proofs.FunctionalEpoch
