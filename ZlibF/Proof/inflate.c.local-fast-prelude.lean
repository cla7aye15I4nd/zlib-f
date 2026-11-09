import ZlibF.Proof.«inflate.c.local-fast-loop-boundary»
import ZlibF.Proof.«inflate.c.fast-view-prelude-ready-invariant»

/-! The actual source-order fast prelude constructs a local loop entry
on arbitrary caller byte views, including disjoint intervals of one object. -/
namespace Zlib.Inflate.Local
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- A fast-path dispatch packet yields bounded input and writable output
views for every public byte-object representation. Their occupied ranges
may be disjoint slices of one object. This is the caller-side premise for
generalizing the translated fast callee beyond raw blocks. -/
theorem fast_views {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (good : LocalGood h cutoff r zs z s)
    (fit : ZlibF.PlatformMemory.ByteObjectsFit h)
    (buffers : DispatchBuffers h r l bs)
    (fast : (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    ∃ (ir or : BRef) (ia oa : Array UInt8) (io oo : Nat),
      l.next = .ref ir io ∧ Space.get h ir = some ia ∧
      io + l.have_.toNat ≤ ia.size ∧ ia.size < 2 ^ 63 ∧
      bs = (ia.toList.drop io).take bs.length ∧
      l.put = .ref or oo ∧ Space.get h or = some oa ∧
      Space.ro h or = false ∧ oo + l.left.toNat ≤ oa.size ∧
      oa.size < 2 ^ 63 ∧
      (ir ≠ or ∨ io + l.have_.toNat ≤ oo ∨
        oo + l.left.toNat ≤ io) := by
  have margins : (6 ≤ l.have_ ∧ 258 ≤ l.left) ∧ l.bits < 8 := by
    simpa only [Bool.and_eq_true, decide_eq_true_eq] using fast
  have inputRoom : 6 ≤ l.have_.toNat := by
    simpa [UInt32.le_iff_toNat_le] using margins.1.1
  have outputRoom : 258 ≤ l.left.toNat := by
    simpa [UInt32.le_iff_toNat_le] using margins.1.2
  have nonempty : bs ≠ [] := by
    intro empty
    have count := buffers.bits.have_eq
    rw [empty] at count
    simp at count
    omega
  obtain ⟨ir, ia, io, inputPtr, inputGet, inputSize, inputBytes⟩ :=
    buffers.bits.next.resolve_left nonempty
  obtain ⟨or, oa, oo, outputPtr, outputGet, outputWrite,
      outputSize, _, _, _⟩ :=
    callerRange_slow_output good l buffers.output.range
      buffers.output.nonnull buffers.output.count
      buffers.output.produced
  have separated : ir ≠ or ∨ io + l.have_.toNat ≤ oo ∨
      oo + l.left.toNat ≤ io := by
    have packet := buffers.separate
    rw [inputPtr, outputPtr] at packet
    dsimp [Separate] at packet
    rcases packet with zeroIn | zeroOut | disjoint
    · omega
    · omega
    · exact disjoint
  exact ⟨ir, or, ia, oa, io, oo, inputPtr, inputGet,
    by rw [buffers.bits.have_eq]; exact inputSize,
    fit.size_lt inputGet, inputBytes, outputPtr, outputGet,
    outputWrite, outputSize, fit.size_lt outputGet, separated⟩

/-- The three actual fast-callee entry pointer expressions are safe for
general represented byte views, including disjoint slices of one object.
The initial `last`, `beg` and `end` positions do not require raw blocks. -/
theorem fast_pointer_setup {h : Heap} {cutoff : Nat} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8}
    (good : LocalGood h cutoff r zs z s)
    (fit : ZlibF.PlatformMemory.ByteObjectsFit h)
    (buffers : DispatchBuffers h r l bs)
    (fast : (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    ∃ (ir or : BRef) (io oo : Nat),
      l.next = .ref ir io ∧ l.put = .ref or oo ∧
      OkOn h (Ptr.add l.next (l.have_ - 5).toNat)
        (.ref ir (io + l.have_.toNat - 5)) ∧
      OkOn h (Zlib.Inffast.subn l.put (l.out_ - l.left))
        (.ref or (oo - (l.out_.toNat - l.left.toNat))) ∧
      OkOn h (Ptr.add l.put (l.left - 257).toNat)
        (.ref or (oo + l.left.toNat - 257)) := by
  obtain ⟨ir, or, ia, oa, io, oo, inputPtr, inputGet,
    inputSize, _, _, outputPtr, outputGet, _, outputSize, _, _⟩ :=
    fast_views good fit buffers fast
  have margins : (6 ≤ l.have_ ∧ 258 ≤ l.left) ∧ l.bits < 8 := by
    simpa only [Bool.and_eq_true, decide_eq_true_eq] using fast
  have inputRoom : 5 ≤ l.have_.toNat := by
    have : 6 ≤ l.have_.toNat := by
      simpa [UInt32.le_iff_toNat_le] using margins.1.1
    omega
  have outputRoom : 257 ≤ l.left.toNat := by
    have : 258 ≤ l.left.toNat := by
      simpa [UInt32.le_iff_toNat_le] using margins.1.2
    omega
  have inputSub : (l.have_ - 5).toNat = l.have_.toNat - 5 :=
    Zlib.Inffast.Proofs.u32_toNat_sub inputRoom
  have outputSub : (l.left - 257).toNat = l.left.toNat - 257 :=
    Zlib.Inffast.Proofs.u32_toNat_sub outputRoom
  have startSub : (l.out_ - l.left).toNat =
      l.out_.toNat - l.left.toNat :=
    Zlib.Inffast.Proofs.u32_toNat_sub buffers.output.count
  have begBound : l.out_.toNat - l.left.toNat ≤ oo :=
    buffers.output.produced or oo outputPtr
  refine ⟨ir, or, io, oo, inputPtr, outputPtr, ?_, ?_, ?_⟩
  · rw [inputPtr, inputSub]
    have step := Ptr.add_nat_ok (h := h) (r := ir) (a := ia)
      (off := io) (n := l.have_.toNat - 5) inputGet (by omega)
    simpa only [show io + (l.have_.toNat - 5) = io + l.have_.toNat - 5 by omega] using step
  · rw [outputPtr]
    have step := Zlib.Inffast.Proofs.subn_ok (h := h) (r := or)
      (a := oa) (off := oo) (n := l.out_ - l.left)
      outputGet (by rw [startSub]; exact begBound) (by omega)
    simpa only [startSub] using step
  · rw [outputPtr, outputSub]
    have step := Ptr.add_nat_ok (h := h) (r := or) (a := oa)
      (off := oo) (n := l.left.toNat - 257) outputGet (by omega)
    simpa only [show oo + (l.left.toNat - 257) = oo + l.left.toNat - 257 by omega] using step

theorem fastEntryPrefix_run
    {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState}
    {slow : IL} {bs : List UInt8}
    (good : LocalGood h cutoff r zs z s)
    (fit : ZlibF.PlatformMemory.ByteObjectsFit h)
    (buffers : DispatchBuffers h r slow bs)
    (tables : DataTablesSafe h s)
    (inputCursor : z.next_in = slow.next)
    (inputCount : z.avail_in = slow.have_)
    (outputCursor : z.next_out = slow.put)
    (outputCount : z.avail_out = slow.left)
    (stateHold : s.hold = slow.hold)
    (stateBits : s.bits = slow.bits)
    (fast : (slow.have_ >= 6 && slow.left >= 258 &&
      slow.bits < 8) = true) :
    ∃ (ir dest : BRef) (io oo : Nat),
      slow.next = .ref ir io ∧
      slow.put = .ref dest oo ∧
      C.run (fastEntryPrefix (some r) slow.out_) h =
        .ok (({
          strm := some r, state := some (.tab zs),
          last := .ref ir (io + slow.have_.toNat - 5),
          beg := .ref dest
            (oo - (slow.out_.toNat - slow.left.toNat)),
          end_ := .ref dest
            (oo + slow.left.toNat - 257),
          wsize := s.wsize, whave := s.whave,
          wnext := s.wnext, window := s.window,
          lcode := s.lencode, dcode := s.distcode,
          lmask := ((1 : UInt32) <<< s.lenbits) - 1,
          dmask := ((1 : UInt32) <<< s.distbits) - 1 },
          {
          in_ := slow.next, out := slow.put,
          hold := slow.hold, bits := slow.bits,
          here := default, op := 0, len := 0, dist := 0,
          from_ := default, broke := false,
          againL := false, againD := false }), h) := by
  obtain ⟨ir, dest, io, oo, nextPtr, putPtr,
    lastRun, begRun, endRun⟩ :=
    fast_pointer_setup good fit buffers fast
  obtain ⟨_, _, _, _, _, lenSafe⟩ :=
    tables.lengthTable
  obtain ⟨_, _, _, _, _, distSafe⟩ :=
    tables.distanceTable
  have lenWidth : s.lenbits.toNat < 32 := by
    have width := lenSafe.1
    omega
  have distWidth : s.distbits.toNat < 32 := by
    have width := distSafe.1
    omega
  change (Ptr.add slow.next (slow.have_ - 5).toNat) h =
      .ok (.ref ir (io + slow.have_.toNat - 5), h)
    at lastRun
  change (Zlib.Inffast.subn slow.put
      (slow.out_ - slow.left)) h =
      .ok (.ref dest
        (oo - (slow.out_.toNat - slow.left.toNat)), h)
    at begRun
  change (Ptr.add slow.put (slow.left - 257).toNat) h =
      .ok (.ref dest (oo + slow.left.toNat - 257), h)
    at endRun
  refine ⟨ir, dest, io, oo, nextPtr, putPtr, ?_⟩
  change (fastEntryPrefix (some r) slow.out_) h =
    .ok (({
      strm := some r, state := some (.tab zs),
      last := .ref ir (io + slow.have_.toNat - 5),
      beg := .ref dest
        (oo - (slow.out_.toNat - slow.left.toNat)),
      end_ := .ref dest
        (oo + slow.left.toNat - 257),
      wsize := s.wsize, whave := s.whave,
      wnext := s.wnext, window := s.window,
      lcode := s.lencode, dcode := s.distcode,
      lmask := ((1 : UInt32) <<< s.lenbits) - 1,
      dmask := ((1 : UInt32) <<< s.distbits) - 1 },
      {
      in_ := slow.next, out := slow.put,
      hold := slow.hold, bits := slow.bits,
      here := default, op := 0, len := 0, dist := 0,
      from_ := default, broke := false,
      againL := false, againD := false }), h)
  unfold fastEntryPrefix
  simp only [bind_app, ldZStream_ok good.live.hz,
    good.live.zst, castInflateState_ok,
    inputCursor, inputCount, outputCursor, outputCount]
  simp only [lastRun, begRun, endRun,
    ldInflateState_tab good.live.hs,
    Zlib.Inffast.Proofs.shl32_eq lenWidth,
    Zlib.Inffast.Proofs.shl32_eq distWidth,
    pure_app, stateHold, stateBits]

/-- The initial fast registers satisfy the actual loop invariant on any
represented caller byte view. The input and output may occupy disjoint
intervals of the same object. -/
theorem FastLoopReady.initial
    {ctx : FastLoopContext} {h : Heap} {cutoff : Nat} {q : Zlib.Inffast.L}
    {slow : IL} {bs : List UInt8} {off : Nat}
    (packet : FastInputPacket h slow bs q)
    (invariant : LocalStateJ h cutoff ctx.r ctx.zs ctx.z ctx.s)
    (buffers : DispatchBuffers h ctx.r slow bs)
    (codesGet : Space.get h ctx.codeRef = some ctx.codes)
    (distGet : Space.get h ctx.distRef = some ctx.distCodes)
    (leftEq : slow.left = ctx.leftTotal)
    (outEq : slow.out_ = ctx.outTotal)
    (putPtr : slow.put = .ref ctx.dest ctx.oo)
    (nextPtr : slow.next = .ref ctx.inputRef off)
    (lastPtr : ctx.c.last = .ref ctx.inputRef
      (off + slow.have_.toNat - 5))
    (inputMargin : 6 ≤ slow.have_.toNat)
    (bitsBound : slow.bits.toNat ≤ 30)
    (outInit : q.out = slow.put) :
    FastLoopReady cutoff ctx h q := by
  obtain ⟨output, outputGet, outputWrite, outputSize⟩ :=
    fast_packet_output_view buffers putPtr rfl
  have endPtr : ctx.c.end_ = .ref ctx.dest
      (ctx.oo + slow.left.toNat - 257) := by
    rw [leftEq]
    exact ctx.endPtr
  have outPtr : q.out = .ref ctx.dest ctx.oo :=
    outInit.trans putPtr
  have firstBound : ctx.oo ≤ output.size := by
    omega
  have endBound : ctx.oo + slow.left.toNat - 257 ≤
      output.size := by
    omega
  have compare := Ptr.lt_ok (r := ctx.dest) (a := output)
    outputGet firstBound endBound
  change C.run (Ptr.lt (.ref ctx.dest ctx.oo)
    (.ref ctx.dest (ctx.oo + slow.left.toNat - 257))) h =
    .ok (decide (ctx.oo < ctx.oo + slow.left.toNat - 257), h)
    at compare
  have guard : C.run (Ptr.lt q.out ctx.c.end_) h =
      .ok (true, h) := by
    rw [outPtr, endPtr]
    rw [compare]
    have avail : 258 ≤ slow.left.toNat := by
      rw [leftEq]
      exact ctx.avail
    simp [show ctx.oo < ctx.oo + slow.left.toNat - 257 by omega]
  have beginLe : ctx.bg ≤ ctx.oo := by
    rw [ctx.beginEq]
    omega
  have span : ctx.oo - ctx.bg < 2 ^ 32 := by
    have width := UInt32.toNat_lt ctx.outTotal
    rw [ctx.beginEq]
    omega
  exact .intro slow bs output off ctx.oo packet invariant
    buffers codesGet distGet bitsBound leftEq outEq putPtr
    nextPtr lastPtr inputMargin outPtr outputGet outputWrite
    outputSize (Nat.le_refl _) beginLe span guard

/-- The actual source prefix exposes its input and output geometry
alongside the checked loop entry. -/
theorem fastEntryPrefix_ready_geometry
    {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState}
    {slow : IL} {bs : List UInt8}
    (invariant : LocalStateJ h cutoff r zs z s)
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
    ∃ (ir dest : BRef) (io oo : Nat)
        (ctx : FastLoopContext) (q : Zlib.Inffast.L),
      slow.next = .ref ir io ∧ slow.put = .ref dest oo ∧
      ctx.inputRef = ir ∧ ctx.dest = dest ∧ ctx.oo = oo ∧
      ctx.leftTotal = slow.left ∧ ctx.r = r ∧ ctx.zs = zs ∧
      ctx.c.last = .ref ir (io + slow.have_.toNat - 5) ∧
      ctx.c.end_ = .ref dest (oo + slow.left.toNat - 257) ∧
      q.in_ = slow.next ∧ q.out = slow.put ∧ q.bits = slow.bits ∧
      C.run (fastEntryPrefix (some r) slow.out_) h =
        .ok ((ctx.c, q), h) ∧ FastLoopReady cutoff ctx h q := by
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
  have ready : FastLoopReady cutoff ctx h q0 :=
    FastLoopReady.initial packet invariant buffers lget
      dget rfl rfl putPtr nextPtr rfl inputMargin
      bitsBound rfl
  exact ⟨ir, dest, io, oo, ctx, q0, nextPtr, putPtr,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, prefixRun, ready⟩


end Zlib.Inflate.Local
