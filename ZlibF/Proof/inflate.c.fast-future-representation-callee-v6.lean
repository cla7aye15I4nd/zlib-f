import ZlibF.Proof.«inflate.c.fast-future-representation-callee-v5»
import ZlibF.Proof.«inflate.c.fast-future-checksum-frame»
import ZlibF.Proof.«inflate.c.fast-segment-output»
import ZlibF.Proof.«inflate.c.fast-future-callee-prefix-cursor»

namespace Zlib.Inflate.Proofs.FunctionalEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inftrees
set_option autoImplicit false

private theorem caller_range_ref_view_fast
    {h : Heap} {r : ZStreamRef} {ref : BRef}
    {off n : Nat} {write : Bool}
    (range : CallerRange h r (.ref ref off) n write) :
    ∃ array, Space.get h ref = some array ∧
      off + n ≤ array.size := by
  rcases range with null | ⟨⟨xs, bytes⟩, _, _⟩
  · cases null
  rcases bytes with empty | ⟨foundRef, foundOff, array,
      pointer, get, bound, _⟩
  · cases empty.1
  cases pointer
  exact ⟨array, get, bound⟩

/-- At any actual payload cut carrying the transported representation,
RESTORE and the complete fast callee execute on arbitrary retained history
and arbitrary current-call output. No public protocol predicate is assumed
at an intermediate heap. -/
theorem PayloadRepresentation.restore_fast_callee_future_v6
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
      regs.left.toNat + made = slow.left.toNat ∧
      ∃ more : List UInt8, more.length = made ∧
        next = current ++ more ∧
        ZlibF.Math.LZ77Copy.writtenBytes array off made = more ∧
      sNext.check = (leaveState s slow).check ∧
      zNext.adler = (leaveStream z slow).adler ∧
      sNext.wrap = (leaveState s slow).wrap ∧
      sNext.flags = (leaveState s slow).flags ∧
      zNext.avail_out.toNat + made = slow.left.toNat ∧
      slow.left.toNat ≤ slow.out_.toNat ∧
      zNext.next_out = inputAdvance slow.put made ∧
      off ≤ array.size := by
  dsimp only
  let restored := setI (r.put h (leaveStream z slow)) zs (leaveState s slow)
  obtain ⟨outputPrefix, ctx, q, restoreRun, prefixRun,
    semantic, sameR, sameIndex, notBroken, putGeometry,
    leftGeometry, outGeometry, sameZ, sameS, bitsGeometry⟩ :=
    representation.restore_fast_entry_future_geometry_v2 E mode
      distanceFlags historyView parsed fast
  obtain ⟨_sameRestore, restoredRep⟩ :=
    representation.restore E
  obtain ⟨restoredOrigin, restoredBuffers, _restoredBits,
    _restoredTables, _restoredDictionary⟩ := restoredRep
  have restoredMode : DataTableMode (leaveState s slow).mode := by
    change DataTableMode s.mode
    exact mode
  obtain ⟨finished, zNext, sNext, used, made, regs,
    result, after, array, off, next, callRun, currentJ,
    finalBuffers, storedPut, _usedBound, nextPtr,
    haveCount, putPtr, leftCount, _small, _budget,
    loopRun, semanticExit, suffixRun, resultPut,
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
    (frameJ.good.live.hz.symm.trans currentJ.good.live.hz)
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
  have oldRange : CallerRange restored r (.ref ctx.dest ctx.oo)
      slow.left.toNat true := by
    rw [← putGeometry]
    exact restoredBuffers.output.range
  obtain ⟨oldArray, oldGet, oldBoundAdd⟩ :=
    caller_range_ref_view_fast oldRange
  have oldBound : ctx.oo ≤ oldArray.size := by omega
  have oldOriginalGet : Space.get h ctx.dest = some oldArray := by
    rw [byte_view_get_setI, byte_view_get_stream_put] at oldGet
    exact oldGet
  let oldCount := slow.out_.toNat - slow.left.toNat
  have oldCountLe : oldCount ≤ ctx.oo := by
    dsimp only [oldCount]
    rw [← outGeometry, ← leftGeometry]
    exact ctx.made
  have beginGeometry : ctx.bg = ctx.oo - oldCount := by
    rw [ctx.beginEq, outGeometry, leftGeometry]
  have oldBytes : ZlibF.Math.LZ77Copy.writtenBytes
      oldArray ctx.oo oldCount = current :=
    historyView ctx.dest ctx.oo oldArray putGeometry oldOriginalGet
  have oldLength : current.length = oldCount := by
    rw [← oldBytes]
    simp only [ZlibF.Math.LZ77Copy.writtenBytes,
      List.length_take, List.length_drop, Array.length_toList]
    omega
  have offGeometry : off = ctx.oo + made := by
    have join : inputAdvance slow.put made = .ref ctx.dest off :=
      putPtr.symm.trans (storedPut.trans (resultPut.trans physical))
    rw [putGeometry, inputAdvance] at join
    exact (Ptr.ref.inj join).2.symm
  have finalPtr : regs.put = .ref ctx.dest off :=
    storedPut.trans (resultPut.trans physical)
  have finalRange : CallerRange finished r (.ref ctx.dest off)
      regs.left.toNat true := by
    rw [← finalPtr]
    exact finalBuffers.output.range
  obtain ⟨rangeArray, getRange, finalBoundAdd⟩ :=
    caller_range_ref_view_fast finalRange
  have sameArray : rangeArray = array :=
    Option.some.inj (getRange.symm.trans finalGet)
  subst rangeArray
  have finalBound : ctx.oo + made ≤ array.size := by
    rw [← offGeometry]
    omega
  have wholeCount : off - ctx.bg = oldCount + made := by
    rw [offGeometry, beginGeometry]
    omega
  have frameAt : BufferFrame restored finished
      (fun b => StreamRoot r b ∨ b = zs)
      [⟨.ref ctx.dest ctx.oo, made⟩] := by
    simpa only [putGeometry] using frame
  have wholeBytes : ZlibF.Math.LZ77Copy.writtenBytes array
      (ctx.oo + made) (oldCount + made) = next := by
    rw [← offGeometry, ← wholeCount]
    exact written
  obtain ⟨more, moreLength, moreBytes, outputConcat⟩ :=
    fast_segment_of_whole frameAt oldGet finalGet
      oldCountLe oldBound finalBound oldLength oldBytes wholeBytes
  have initialBits : q.bits.toNat < 8 := by
    rw [bitsGeometry]
    have margins : slow.bits < 8 := by
      have facts : (6 ≤ slow.have_ ∧ 258 ≤ slow.left) ∧
          slow.bits < 8 := by
        simpa only [Bool.and_eq_true, decide_eq_true_eq] using fast
      exact facts.2
    exact UInt32.lt_iff_toNat_lt.mp margins
  have currentCtx : DefaultStateJ finished ctx.r ctx.zs zNext sNext := by
    simpa only [sameR, sameIndex] using currentJ
  obtain ⟨checkFrame, adlerFrame, wrapFrame, flagsFrame⟩ :=
    semantic.callee_checksum_frame initialBits loopRun suffixRun currentCtx
  refine ⟨ctx, q, finished, zNext, sNext, used, made,
    regs, result, after, array, off, next, restoreRun,
    prefixRun, callRun, currentJ, frame, semanticExit, resultPut,
    physical, finalGet, written, prefixBytes,
    nextPtr, haveCount, putPtr, leftCount,
    more, moreLength, outputConcat, ?_,
    by simpa only [sameS] using checkFrame,
    by simpa only [sameZ] using adlerFrame,
    by simpa only [sameS] using wrapFrame,
    by simpa only [sameS] using flagsFrame,
    by simpa only [show (leaveStream z slow).avail_out = slow.left from rfl] using accounting.2.2.2.1,
    by rw [← leftGeometry, ← outGeometry]; exact ctx.count,
    storedPut.symm.trans putPtr,
    by rw [offGeometry]; exact finalBound⟩
  rwa [offGeometry]

#print axioms PayloadRepresentation.restore_fast_callee_future_v6
end Zlib.Inflate.Proofs.FunctionalEpoch
