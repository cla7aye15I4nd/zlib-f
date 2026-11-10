import ZlibF.Proof.«inflate.c.fast-bad-consumed-word-classifier»
namespace Zlib.Inflate.Proofs.FastArbitraryBody
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inffast.Spec Zlib.Inftrees
open Zlib.Inftrees.Spec.DecodeTableInvariant Zlib.Inftrees.Spec.DecodeTableStability
set_option autoImplicit false
/-- Actual loop-ready source resources either avoid BAD or consume a
universally rejected word. No valid-source or callee-result oracle is an
input; table truncation properties come from actual data producers. -/
theorem ready_body_nonbad_or_rejected_word
    {ctx : FastLoopContext} {h : Heap} {q : Zlib.Inffast.L} {L D : List Nat} {dict : List UInt8}
    (ready : FastLoopReady ctx h q)
    (lmeaning : ∃ used, Inv LENS ctx.codes ctx.baseOff ctx.rootWidth used L)
    (lstable : StableQuery LENS ctx.codes ctx.baseOff ctx.rootWidth)
    (ltake : Zlib.Inftrees.Proofs.QueryTakeSource.QueryTake LENS ctx.codes ctx.baseOff ctx.rootWidth)
    (lflags : Zlib.Inftrees.Spec.FastTableFlags.QueryCompatible LENS ctx.codes ctx.baseOff ctx.rootWidth)
    (dmeaning : ∃ used, Inv DISTS ctx.distCodes ctx.distOff ctx.distWidth used D)
    (dflags : Zlib.Inftrees.Spec.FastTableFlags.QueryCompatible DISTS ctx.distCodes ctx.distOff ctx.distWidth)
    (dstable : StableQuery DISTS ctx.distCodes ctx.distOff ctx.distWidth)
    (dtake : Zlib.Inftrees.Proofs.QueryTakeSource.QueryTake DISTS ctx.distCodes ctx.distOff ctx.distWidth)
    (saved : Array UInt8) (woff : Nat)
    (windowData : ctx.c.whave ≠ 0 → ∃ window, window ≠ ctx.dest ∧ ctx.c.window = .ref window woff ∧
      Space.get h window = some saved ∧ woff + ctx.c.wsize.toNat ≤ saved.size)
    (dictionary : MatchHistory.saved saved ctx.c.wsize.toNat ctx.c.wnext.toNat ctx.c.whave.toNat woff = dict)
    (dictCount : dict.length = ctx.c.whave.toNat) :
    ∃ slow bs output off j,
      FastInputPacket h slow bs q ∧ DispatchBuffers h ctx.r slow bs ∧
      slow.next = .ref ctx.inputRef off ∧ slow.put = .ref ctx.dest ctx.oo ∧ q.out = .ref ctx.dest j ∧
      Space.get h ctx.dest = some output ∧
      (BodyNonBad h ctx.r ctx.zs ctx.c q ∨
       BadWordResult h ctx.r ctx.zs ctx.z ctx.s ctx.c slow q bs dict
         (ZlibF.Math.LZ77Copy.writtenBytes output j (j - ctx.bg)) L D) := by
  rcases ready with ⟨slow, bs, output, off, j, packet, invariant, buffers, codesGet, distGet, bits,
    leftEq, _outEq, put, next, _last, margin, out, get, write, size, current, beginLe, span, guard⟩
  obtain ⟨lextent, linv⟩ := lmeaning
  obtain ⟨dextent, dinv⟩ := dmeaning
  have left : slow.left ≠ 0 := by rw [leftEq]; exact ctx.leftNonzero
  have avail : 258 ≤ slow.left.toNat := by rw [leftEq]; exact ctx.avail
  have endPtr : ctx.c.end_ = .ref ctx.dest (ctx.oo + slow.left.toNat - 257) := by rw [leftEq]; exact ctx.endPtr
  have whave : ctx.c.whave.toNat ≤ ctx.c.wsize.toNat := by rw [ctx.whaveEq, ctx.wsizeEq]; exact invariant.good.inv.win.hv
  have wnext : ctx.c.wnext.toNat ≤ ctx.c.wsize.toNat := by
    rw [ctx.wnextEq, ctx.wsizeEq]
    rcases invariant.good.inv.win.wn with valid | ⟨zero, nextZero⟩ <;> omega
  have wsize : ctx.c.wsize.toNat ≤ 32768 := by
    rw [ctx.wsizeEq]
    rcases invariant.good.inv.win.ws with zero | full
    · omega
    · rw [invariant.window] at full
      change ctx.s.wsize.toNat = 32768 at full
      omega
  have event := fast_body_nonbad_or_rejected_word packet buffers margin bits ctx.lcodePtr ctx.lenSafe ctx.lenMask
    invariant codesGet linv lflags lstable ltake ctx.dcodePtr distGet ctx.distSafe ctx.distMask dinv dflags
    dstable dtake ctx.mode ctx.streamPtr ctx.statePtr left avail whave wnext wsize out put ctx.begPtr endPtr get write size
    current beginLe span guard windowData dictionary dictCount
  exact ⟨slow, bs, output, off, j, packet, buffers, next, put, out, get, event⟩

/-- Physical retained-window rejection reconstructs the complete logical
history while keeping the same actual consumed word, heap and cursors. -/
theorem BadWordResult.logical_context
    {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {c : Zlib.Inffast.Ctx} {slow : IL} {fast : Zlib.Inffast.L} {bs dict past current : List UInt8}
    {L D : List Nat}
    (bad : BadWordResult h r zs z s c slow fast bs
      ((dict ++ past).drop ((dict ++ past).length - 32768)) current L D) :
    BadWordResult h r zs z s c slow fast bs dict (past ++ current) L D := by
  obtain ⟨used, word, result, after, finalSlow, i, bound, raw, cursor, actual, heap, broke, out,
    packet, buffers, invariant, views, source, rejected⟩ := bad
  exact ⟨used, word, result, after, finalSlow, i, bound, raw, cursor, actual, heap, broke, out,
    packet, buffers, invariant, views, source, fun future => rejected_retained_context (rejected future)⟩

#print axioms ready_body_nonbad_or_rejected_word
#print axioms BadWordResult.logical_context
end Zlib.Inflate.Proofs.FastArbitraryBody
