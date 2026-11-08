import ZlibF.Proof.«inflate.c.fast-view-loop-output-span-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- Fixed data and checked table geometry for one default fast call. -/
structure FastLoopContext where
  c : Zlib.Inffast.Ctx
  r : ZStreamRef
  zs : Nat
  z : ZStream
  s : InflateState
  codeRef : CodeRef
  codes : Array Code
  baseOff : Nat
  rootWidth : Nat
  distRef : CodeRef
  distCodes : Array Code
  distOff : Nat
  distWidth : Nat
  dest : BRef
  inputRef : BRef
  oo : Nat
  bg : Nat
  leftTotal : UInt32
  outTotal : UInt32
  streamPtr : c.strm = some r
  statePtr : c.state = some (.tab zs)
  mode : DataTableMode s.mode
  whaveEq : c.whave = s.whave
  wsizeEq : c.wsize = s.wsize
  wnextEq : c.wnext = s.wnext
  windowEq : c.window = s.window
  lcodePtr : c.lcode = .ref codeRef baseOff
  lenSafe : LenTableSafe codes baseOff rootWidth
  lenMask : c.lmask.toUInt64.toNat = 2 ^ rootWidth - 1
  dcodePtr : c.dcode = .ref distRef distOff
  distSafe : DistTableSafe distCodes distOff distWidth
  distMask : c.dmask.toUInt64.toNat = 2 ^ distWidth - 1
  leftNonzero : leftTotal ≠ 0
  avail : 258 ≤ leftTotal.toNat
  begPtr : c.beg = .ref dest bg
  endPtr : c.end_ = .ref dest (oo + leftTotal.toNat - 257)
  count : leftTotal.toNat ≤ outTotal.toNat
  made : outTotal.toNat - leftTotal.toNat ≤ oo
  beginEq : bg = oo - (outTotal.toNat - leftTotal.toNat)

/-- State at the beginning of a continuing fast-loop body. -/
inductive FastLoopReady (ctx : FastLoopContext)
    (h : Heap) (q : Zlib.Inffast.L) : Prop where
  | intro (slow : IL) (bs : List UInt8)
      (output : Array UInt8) (off k : Nat)
      (packet : FastInputPacket h slow bs q)
      (invariant : DefaultStateJ h ctx.r ctx.zs ctx.z ctx.s)
      (buffers : DispatchBuffers h ctx.r slow bs)
      (codesGet : Space.get h ctx.codeRef = some ctx.codes)
      (distGet : Space.get h ctx.distRef = some ctx.distCodes)
      (bitsBound : slow.bits.toNat ≤ 30)
      (leftEq : slow.left = ctx.leftTotal)
      (outEq : slow.out_ = ctx.outTotal)
      (putPtr : slow.put = .ref ctx.dest ctx.oo)
      (nextPtr : slow.next = .ref ctx.inputRef off)
      (lastPtr : ctx.c.last = .ref ctx.inputRef
        (off + slow.have_.toNat - 5))
      (inputMargin : 6 ≤ slow.have_.toNat)
      (outPtr : q.out = .ref ctx.dest k)
      (outputGet : Space.get h ctx.dest = some output)
      (outputWrite : Space.ro h ctx.dest = false)
      (outputSize : ctx.oo + slow.left.toNat ≤ output.size)
      (current : ctx.oo ≤ k)
      (beginLe : ctx.bg ≤ k)
      (span : k - ctx.bg < 2 ^ 32)
      (guard : C.run (Ptr.lt q.out ctx.c.end_) h = .ok (true, h)) :
      FastLoopReady ctx h q

/-- Exit information retained by the actual fast loop. -/
def FastLoopExit (ctx : FastLoopContext)
    (h : Heap) (q : Zlib.Inffast.L) : Prop :=
  ∃ finalSlow finalBs finalZ finalS,
    FastInputPacket h finalSlow finalBs q ∧
    DefaultStateJ h ctx.r ctx.zs finalZ finalS ∧
    DispatchBuffers h ctx.r finalSlow finalBs

def fastLoopCond (ctx : FastLoopContext)
    (q : Zlib.Inffast.L) : M (Bool × Zlib.Inffast.L) := do
  if q.broke then pure (false, q)
  else if ← Ptr.lt q.in_ ctx.c.last then
    pure (← Ptr.lt q.out ctx.c.end_, q)
  else pure (false, q)

def fastLoopMeasure (ctx : FastLoopContext)
    (q : Zlib.Inffast.L) : Nat :=
  match q.out with
  | .null => 0
  | .ref _ k => ctx.oo + ctx.leftTotal.toNat - k

/-- One actual body and condition either exits with a retained packet or
re-establishes every premise needed by the next body. -/
theorem FastLoopReady.step
    {ctx : FastLoopContext} {h : Heap} {q : Zlib.Inffast.L}
    (ready : FastLoopReady ctx h q) :
    ∃ result after,
      C.run (Zlib.Inffast.inflate_fast_body ctx.c q) h =
        .ok (result, after) ∧
      ((fastLoopCond ctx result after = .ok ((false, result), after) ∧
          FastLoopExit ctx after result) ∨
       (fastLoopCond ctx result after = .ok ((true, result), after) ∧
          FastLoopReady ctx after result ∧
          fastLoopMeasure ctx result < fastLoopMeasure ctx q)) := by
  rcases ready with ⟨slow, bs, output, off, k, packet,
    invariant, buffers, codesGet, distGet, bitsBound,
    leftEq, outEq, putPtr, nextPtr, lastPtr, inputMargin,
    outPtr, outputGet, outputWrite, outputSize, current,
    beginLe, span, guard⟩
  obtain ⟨first, second, third, fourth, fifth, sixth,
    rest, rfl⟩ := packet.six_unread inputMargin
  have left : slow.left ≠ 0 := by
    rw [leftEq]
    exact ctx.leftNonzero
  have avail : 258 ≤ slow.left.toNat := by
    rw [leftEq]
    exact ctx.avail
  have endPtr : ctx.c.end_ = .ref ctx.dest
      (ctx.oo + slow.left.toNat - 257) := by
    rw [leftEq]
    exact ctx.endPtr
  have count : slow.left.toNat ≤ slow.out_.toNat := by
    rw [leftEq, outEq]
    exact ctx.count
  have made : slow.out_.toNat - slow.left.toNat ≤ ctx.oo := by
    rw [leftEq, outEq]
    exact ctx.made
  have beginEq : ctx.bg = ctx.oo -
      (slow.out_.toNat - slow.left.toNat) := by
    rw [leftEq, outEq]
    exact ctx.beginEq
  obtain ⟨used, consumed, finalSlow, result, after,
    zNext, sNext, usedBound, consumedBound, bodyRun,
    finalPacket, finalJ, finalBuffers, sizes, source,
    rank, finalFrame, heapFrame, keepGoing, condRun,
    continuing, finalBits⟩ :=
    packet.fast_body_condition_heap_bits_default_state
      invariant buffers ctx.streamPtr ctx.statePtr ctx.mode
      ctx.whaveEq ctx.wsizeEq ctx.wnextEq ctx.windowEq
      ctx.lcodePtr codesGet ctx.lenSafe ctx.lenMask
      ctx.dcodePtr distGet ctx.distSafe ctx.distMask
      bitsBound left avail outPtr putPtr ctx.begPtr endPtr
      outputGet outputWrite outputSize current beginLe
      span guard nextPtr lastPtr
  refine ⟨result, after, bodyRun, ?_⟩
  cases flag : keepGoing
  · have stopped : fastLoopCond ctx result after =
        .ok ((false, result), after) := by
      change C.run (do
        if result.broke then pure (false, result)
        else if ← Ptr.lt result.in_ ctx.c.last then
          pure (← Ptr.lt result.out ctx.c.end_, result)
        else pure (false, result)) after =
          .ok ((false, result), after)
      rwa [flag] at condRun
    exact Or.inl ⟨stopped, finalSlow,
      List.drop used
        (first :: second :: third :: fourth :: fifth :: sixth :: rest),
      zNext, sNext, finalPacket, finalJ, finalBuffers⟩
  · obtain ⟨notBroken, inputReady, next, nextOut,
      margin⟩ := continuing flag
    obtain ⟨putFrame, leftFrame, outFrame, nextFrame,
      _, lastFrame⟩ := finalFrame notBroken
    obtain ⟨array, heapEq, streamEq, stateEq⟩ :=
      heapFrame notBroken
    rcases rank with broken | ⟨nextRank, rankOut,
      within, decrease⟩
    · rw [notBroken] at broken
      cases broken
    have sameNext : nextRank = next := by
      rw [rankOut] at nextOut
      cases nextOut
      rfl
    subst nextRank
    obtain ⟨outputNext, outputNextGet, sizeEq,
      outputNextWrite, nextCurrent, nextBegin, nextSpan,
      nextGuard⟩ :=
      fast_continuing_output_view sizes heapEq outputGet
        outputWrite outputSize nextOut endPtr current
        decrease margin count made beginEq
    obtain ⟨nextCodes, nextDist⟩ :=
      fast_continuing_table_views heapEq codesGet distGet
    have nextJ : DefaultStateJ after ctx.r ctx.zs
        ctx.z ctx.s := by
      rw [streamEq, stateEq] at finalJ
      exact finalJ
    have nextLeft : finalSlow.left = ctx.leftTotal :=
      leftFrame.trans leftEq
    have nextOutCount : finalSlow.out_ = ctx.outTotal :=
      outFrame.trans outEq
    have nextPut : finalSlow.put = .ref ctx.dest ctx.oo :=
      putFrame.trans putPtr
    have nextCursor : finalSlow.next =
        .ref ctx.inputRef (off + used) := by
      rw [nextFrame, nextPtr]
      rfl
    have nextSize : ctx.oo + finalSlow.left.toNat ≤
        outputNext.size := by
      calc
        ctx.oo + finalSlow.left.toNat =
            ctx.oo + slow.left.toNat := by rw [leftFrame]
        _ ≤ output.size := outputSize
        _ = outputNext.size := sizeEq.symm
    have measure : fastLoopMeasure ctx result <
        fastLoopMeasure ctx q := by
      simp only [fastLoopMeasure, nextOut, outPtr]
      rw [← leftEq]
      omega
    have repeated : fastLoopCond ctx result after =
        .ok ((true, result), after) := by
      change C.run (do
        if result.broke then pure (false, result)
        else if ← Ptr.lt result.in_ ctx.c.last then
          pure (← Ptr.lt result.out ctx.c.end_, result)
        else pure (false, result)) after =
          .ok ((true, result), after)
      rwa [flag] at condRun
    refine Or.inr ⟨repeated, ?_, measure⟩
    exact ⟨finalSlow,
      List.drop used
        (first :: second :: third :: fourth :: fifth :: sixth :: rest),
      outputNext, off + used, next,
      finalPacket, nextJ, finalBuffers, nextCodes,
      nextDist, finalBits flag, nextLeft, nextOutCount,
      nextPut, nextCursor, lastFrame, inputReady,
      nextOut, outputNextGet, outputNextWrite, nextSize,
      nextCurrent, nextBegin, nextSpan, nextGuard⟩

end Zlib.Inflate.Proofs
