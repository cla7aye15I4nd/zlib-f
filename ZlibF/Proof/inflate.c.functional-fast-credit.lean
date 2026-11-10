import ZlibF.Proof.«inflate.c.functional-trailer»
import ZlibF.Proof.«inflate.c.global-dynamic-fast-callee-output-v2»

namespace Zlib.Inflate.Proofs.FunctionalEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.WrapperGlue Zlib.Inflate.Proofs.FunctionalTrailer
set_option autoImplicit false

/-- The actual dynamic LEN_ fast branch establishes the physical
uncredited-output relation needed by generic CHECK/leave. The incoming
cumulative seed is internal epoch state, not a checksum result supplied
by a caller or an assumption about the fast callee. -/
theorem DynamicPayloadReady.fast_output_credit
    {h : Heap} {r : ZStreamRef} {zs : Nat} {log : DataLog}
    {input : List UInt8} {flush : Int32} {future rest : List Bool} {decoded : List UInt8}
    (ready : DynamicPayloadReady h r zs log input flush future rest decoded)
    (fast : (ready.packet.boundary.regs.have_ >= 6 &&
      ready.packet.boundary.regs.left >= 258 && ready.packet.boundary.regs.bits < 8) = true)
    (seed : AdlerCredit ready.calleeStream ready.calleeState log.output) :
    ∃ loadedHeap zNext loadedState loaded next,
      runX (inflate_LEN_ ⟨some r, some (.tab zs), syncBuf h, flush⟩) ready.fastRegs
        (setI ready.packet.codeHeap zs ready.packet.boundary.state) =
          .ok ((.ok (), loaded), loadedHeap) ∧
      DefaultStateJ loadedHeap r zs zNext loadedState ∧ next <+: decoded ∧
      OutputCredit loadedHeap zNext loadedState loaded log.output next 0 := by
  obtain ⟨ctx, initial, finished, zNext, sNext, used, made, regs, result, after,
    array, off, next, loaded, loadedHeap, loadedState,
    actual, _callee, _prefixRun, _loopRun, _semantic, _suffix, _calleeJ, currentJ,
    loadedPut, streamPut, resultPut, offEq, bgEq, bound, length, get, written, prefixBytes,
    check, adler, wrap, flags, loadedCheck, loadedWrap, loadedFlags, _loadedMode,
    _loadedLeft, loadedOut, loadedCount, _regsPut, _next, _have, _put, _left⟩ :=
    ready.fast_callee_output_v2 fast
  have noOutput : ready.fastRegs.out_ = ready.fastRegs.left := by
    obtain ⟨_usedBound, _origin, _buffers, _small, _next, _have,
      _put, _left, fresh, _window, _mode, _symbols, _dispatch⟩ := ready.packet.endpoint
    simpa only [DynamicPayloadReady.fastRegs] using fresh
  have count : (loaded.out_ - loaded.left).toNat = next.length := by
    rw [UInt32.toNat_sub_of_le _ _ (by
      apply UInt32.le_iff_toNat_le.mpr
      rw [loadedOut, noOutput]
      omega), loadedOut, noOutput, length]
    omega
  have physical : ZlibF.Math.LZ77Copy.writtenBytes array off next.length = next := by
    have amount : off - ctx.bg = next.length := by rw [offEq, bgEq, length]; omega
    rwa [amount] at written
  refine ⟨loadedHeap, zNext, loadedState, loaded, next, actual, currentJ, prefixBytes, ?_⟩
  exact OutputCredit.from_observed_frame seed (loadedCheck.trans check) adler
    (loadedWrap.trans wrap) (loadedFlags.trans flags) count
    (loadedPut.trans (streamPut.trans resultPut)) get (by rw [length, offEq]; omega) bound physical

#print axioms DynamicPayloadReady.fast_output_credit
end Zlib.Inflate.Proofs.FunctionalEpoch
