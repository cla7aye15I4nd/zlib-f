import ZlibF.Proof.«inflate.c.fast-view-prelude-invariant»
import ZlibF.Proof.«inflate.c.fast-view-loop-full-input-budget»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- The actual source-order fast prelude returns the context and registers
used by the checked general-view loop invariant. -/
theorem fastEntryPrefix_ready
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
    ∃ (ctx : FastLoopContext) (q : Zlib.Inffast.L),
      C.run (fastEntryPrefix (some r) slow.out_) h =
        .ok ((ctx.c, q), h) ∧
      FastLoopReady ctx h q := by
  obtain ⟨ir, dest, io, oo, nextPtr, putPtr, prefixRun⟩ :=
    fastEntryPrefix_run invariant.good invariant.platform
      buffers (invariant.tables mode) inputCursor inputCount
      outputCursor outputCount stateHold stateBits fast
  obtain ⟨lr, lo, lc, lptr, lget, lsafe⟩ :=
    (invariant.tables mode).lengthTable
  obtain ⟨dr, doff, dc, dptr, dget, dsafe⟩ :=
    (invariant.tables mode).distanceTable
  have margins : (6 ≤ slow.have_ ∧ 258 ≤ slow.left) ∧
      slow.bits < 8 := by
    simpa only [Bool.and_eq_true, decide_eq_true_eq]
      using fast
  have inputMargin : 6 ≤ slow.have_.toNat := by
    simpa [UInt32.le_iff_toNat_le] using margins.1.1
  have outputMargin : 258 ≤ slow.left.toNat := by
    simpa [UInt32.le_iff_toNat_le] using margins.1.2
  have bitsBound : slow.bits.toNat ≤ 30 := by
    have small : slow.bits.toNat < 8 := by
      simpa [UInt32.lt_iff_toNat_lt] using margins.2
    omega
  let bg := oo - (slow.out_.toNat - slow.left.toNat)
  let c0 : Zlib.Inffast.Ctx := {
    strm := some r, state := some (.tab zs),
    last := .ref ir (io + slow.have_.toNat - 5),
    beg := .ref dest bg,
    end_ := .ref dest (oo + slow.left.toNat - 257),
    wsize := s.wsize, whave := s.whave,
    wnext := s.wnext, window := s.window,
    lcode := s.lencode, dcode := s.distcode,
    lmask := ((1 : UInt32) <<< s.lenbits) - 1,
    dmask := ((1 : UInt32) <<< s.distbits) - 1 }
  let q0 : Zlib.Inffast.L := {
    in_ := slow.next, out := slow.put,
    hold := slow.hold, bits := slow.bits,
    here := default, op := 0, len := 0, dist := 0,
    from_ := default, broke := false,
    againL := false, againD := false }
  let ctx : FastLoopContext := {
    c := c0, r, zs, z, s,
    codeRef := lr, codes := lc, baseOff := lo,
    rootWidth := s.lenbits.toNat,
    distRef := dr, distCodes := dc, distOff := doff,
    distWidth := s.distbits.toNat,
    dest, inputRef := ir, oo, bg,
    leftTotal := slow.left, outTotal := slow.out_,
    streamPtr := rfl, statePtr := rfl, mode,
    whaveEq := rfl, wsizeEq := rfl, wnextEq := rfl,
    windowEq := rfl,
    lcodePtr := lptr, lenSafe := lsafe,
    lenMask := by
      change ((((1 : UInt32) <<< s.lenbits) - 1).toUInt64.toNat) =
        2 ^ s.lenbits.toNat - 1
      rw [UInt32.toNat_toUInt64]
      exact Zlib.Inffast.Proofs.u32_shl1_sub1 (by
        have width := lsafe.1
        omega),
    dcodePtr := dptr, distSafe := dsafe,
    distMask := by
      change ((((1 : UInt32) <<< s.distbits) - 1).toUInt64.toNat) =
        2 ^ s.distbits.toNat - 1
      rw [UInt32.toNat_toUInt64]
      exact Zlib.Inffast.Proofs.u32_shl1_sub1 (by
        have width := dsafe.1
        omega),
    leftNonzero := by
      intro zero
      rw [zero] at outputMargin
      simp at outputMargin,
    avail := outputMargin,
    begPtr := rfl, endPtr := rfl,
    count := buffers.output.count,
    made := buffers.output.produced dest oo putPtr,
    beginEq := rfl }
  have packet : FastInputPacket h slow bs q0 :=
    ⟨buffers.bits, rfl, rfl, rfl⟩
  have ready : FastLoopReady ctx h q0 :=
    FastLoopReady.initial packet invariant buffers lget
      dget rfl rfl putPtr nextPtr rfl inputMargin
      bitsBound rfl
  exact ⟨ctx, q0, prefixRun, ready⟩

/-- The actual prelude and actual fast loop compose before normalization
and writeback. -/
theorem fastEntryPrefix_loop_run
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
        (after : Heap),
      C.run (fastEntryPrefix (some r) slow.out_) h =
        .ok ((ctx.c, q), h) ∧
      C.run (cdoWhile (Zlib.Inffast.inflate_fast_body ctx.c)
        (fun q => do
          if q.broke then pure (false, q)
          else if ← Ptr.lt q.in_ ctx.c.last then
            pure (← Ptr.lt q.out ctx.c.end_, q)
          else pure (false, q)) q) h =
          .ok (result, after) ∧
      FastLoopExit ctx after result := by
  obtain ⟨ctx, q, prefixRun, ready⟩ :=
    fastEntryPrefix_ready invariant buffers mode inputCursor
      inputCount outputCursor outputCount stateHold stateBits
      fast
  have inputCursor : ∃ off, q.in_ = .ref ctx.inputRef off := by
    rcases ready with ⟨_, _, _, off, _, packet, _, _, _, _, _,
      _, _, _, nextPtr, _, _, _, _, _, _, _, _, _, _⟩
    exact ⟨off, packet.cursor.trans nextPtr⟩
  obtain ⟨off, cursor⟩ := inputCursor
  obtain ⟨result, after, loopRun, final, _, _, _⟩ :=
    ready.run_full_input_budget (FastLoopInputBudget.initial cursor)
  exact ⟨ctx, q, result, after, prefixRun, loopRun, final⟩

/-- Proof-only cut immediately after the translated fast loop. -/
def fastEntryLoop (strm : ZStreamPtr) (start : UInt32) :
    M (Zlib.Inffast.Ctx × Zlib.Inffast.L) := do
  let pair ← fastEntryPrefix strm start
  let result ← cdoWhile
    (Zlib.Inffast.inflate_fast_body pair.1)
    (fun q => do
      if q.broke then pure (false, q)
      else if ← Ptr.lt q.in_ pair.1.last then
        pure (← Ptr.lt q.out pair.1.end_, q)
      else pure (false, q)) pair.2
  return (pair.1, result)

/-- The real fast call is the checked prelude and loop followed by its
unchanged normalization and writeback fragment. -/
theorem inflate_fast_loop_split
    (strm : ZStreamPtr) (start : UInt32) :
    Zlib.Inffast.inflate_fast strm start =
      (do
        let pair ← fastEntryLoop strm start
        fastAfterLoop pair.1 pair.2) := by
  rw [inflate_fast_prefix_split]
  funext h
  unfold fastEntryLoop fastAfterPrefix
  simp only [bind_app]
  repeat' (split <;> try rfl)

/-- Prelude and loop execute as one fault-free computation on the general
caller view, retaining the basic default decoder and buffer packet. -/
theorem fastEntryLoop_run
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
    ∃ (ctx : FastLoopContext) (result : Zlib.Inffast.L)
        (after : Heap),
      C.run (fastEntryLoop (some r) slow.out_) h =
        .ok ((ctx.c, result), after) ∧
      FastLoopExit ctx after result := by
  obtain ⟨ctx, q, result, after, prefixRun,
    loopRun, final⟩ :=
    fastEntryPrefix_loop_run invariant buffers mode
      inputCursor inputCount outputCursor outputCount
      stateHold stateBits fast
  refine ⟨ctx, result, after, ?_, final⟩
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

end Zlib.Inflate.Proofs
