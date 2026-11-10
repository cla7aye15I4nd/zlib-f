import ZlibF.Proof.«inflate.c.fast-view-loop-actual-invariant»
import ZlibF.Proof.«inflate.c.leave-default-state»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- The initial fast registers satisfy the actual loop invariant on any
represented caller byte view. The input and output may occupy disjoint
intervals of the same object. -/
theorem FastLoopReady.initial
    {ctx : FastLoopContext} {h : Heap} {q : Zlib.Inffast.L}
    {slow : IL} {bs : List UInt8} {off : Nat}
    (packet : FastInputPacket h slow bs q)
    (invariant : DefaultStateJ h ctx.r ctx.zs ctx.z ctx.s)
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
    FastLoopReady ctx h q := by
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

/-- The real fast loop is safe from a synchronized initial call packet,
without requiring distinct input and output allocations. -/
theorem FastLoopReady.run_initial
    {ctx : FastLoopContext} {h : Heap} {q : Zlib.Inffast.L}
    {slow : IL} {bs : List UInt8} {off : Nat}
    (packet : FastInputPacket h slow bs q)
    (invariant : DefaultStateJ h ctx.r ctx.zs ctx.z ctx.s)
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
    ∃ result after,
      C.run (cdoWhile (Zlib.Inffast.inflate_fast_body ctx.c)
        (fun q => do
          if q.broke then pure (false, q)
          else if ← Ptr.lt q.in_ ctx.c.last then
            pure (← Ptr.lt q.out ctx.c.end_, q)
          else pure (false, q)) q) h =
          .ok (result, after) ∧
      FastLoopExit ctx after result :=
  (FastLoopReady.initial packet invariant buffers codesGet
    distGet leftEq outEq putPtr nextPtr lastPtr inputMargin
    bitsBound outInit).run

/-- A default data-mode caller supplies the concrete tables and byte views
needed to instantiate the general fast loop. The registers and context use
the caller cursors and decoder fields. -/
theorem default_fast_loop_entry
    {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState}
    {slow : IL} {bs : List UInt8}
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    (mode : DataTableMode s.mode)
    (fast : (slow.have_ >= 6 && slow.left >= 258 &&
      slow.bits < 8) = true) :
    ∃ (ctx : FastLoopContext) (q : Zlib.Inffast.L),
      q.in_ = slow.next ∧ q.out = slow.put ∧
      q.hold = slow.hold ∧ q.bits = slow.bits ∧
      ctx.c.strm = some r ∧
      ctx.c.state = some (.tab zs) ∧
      ctx.c.wsize = s.wsize ∧
      ctx.c.whave = s.whave ∧
      ctx.c.wnext = s.wnext ∧
      ctx.c.window = s.window ∧
      ctx.c.lcode = s.lencode ∧
      ctx.c.dcode = s.distcode ∧
      ctx.c.lmask = ((1 : UInt32) <<< s.lenbits) - 1 ∧
      ctx.c.dmask = ((1 : UInt32) <<< s.distbits) - 1 ∧
      FastLoopReady ctx h q := by
  obtain ⟨ir, dest, ia, oa, io, oo, inputPtr,
    inputGet, inputSize, _, _, outputPtr, outputGet,
    outputWrite, outputSize, _, _⟩ :=
    buffers.fast_views invariant.good invariant.platform fast
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
    made := buffers.output.produced dest oo outputPtr,
    beginEq := rfl }
  have packet : FastInputPacket h slow bs q0 :=
    ⟨buffers.bits, rfl, rfl, rfl⟩
  have ready : FastLoopReady ctx h q0 :=
    FastLoopReady.initial packet invariant buffers lget
      dget rfl rfl outputPtr inputPtr rfl inputMargin
      bitsBound rfl
  exact ⟨ctx, q0, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ready⟩

/-- Actual RESTORE reaches a heap on which the general fast-loop entry
packet can be constructed. No separation by allocation identity is used. -/
theorem default_fast_loop_after_restore
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState}
    {slow : IL} {bs : List UInt8}
    (E : Env c h r zs z s)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    (mode : DataTableMode s.mode)
    (fast : (slow.have_ >= 6 && slow.left >= 258 &&
      slow.bits < 8) = true) :
    let restored :=
      setI (r.put h (leaveStream z slow)) zs (leaveState s slow)
    ∃ (ctx : FastLoopContext) (q : Zlib.Inffast.L),
      C.run (leaveRestore c slow) h = .ok ((), restored) ∧
      ctx.c.strm = c.strm ∧ ctx.c.state = c.st ∧
      q.in_ = slow.next ∧ q.out = slow.put ∧
      FastLoopReady ctx restored q := by
  dsimp only
  have bitCount : slow.bits.toNat ≤ 39 := by
    have margins : (6 ≤ slow.have_ ∧ 258 ≤ slow.left) ∧
        slow.bits < 8 := by
      simpa only [Bool.and_eq_true, decide_eq_true_eq]
        using fast
    have small : slow.bits.toNat < 8 := by
      simpa [UInt32.lt_iff_toNat_lt] using margins.2
    omega
  have current := invariant.restore E buffers bitCount
  have views : ∀ ref : BRef,
      (Space.get
        (setI (r.put h (leaveStream z slow)) zs
          (leaveState s slow)) ref : Option (Array UInt8)) =
        Space.get h ref := by
    intro ref
    rw [byte_view_get_setI, byte_view_get_stream_put]
  have readonly : ∀ ref : BRef,
      Space.ro
        (setI (r.put h (leaveStream z slow)) zs
          (leaveState s slow)) ref = Space.ro h ref := by
    intro ref
    rw [byte_view_ro_setI, byte_view_ro_stream_put]
  have packet := buffers.byte_views invariant.good
    current.good rfl views readonly
  have dataMode : DataTableMode (leaveState s slow).mode := mode
  obtain ⟨ctx, q, cursor, output, hold, bits,
    strm, state, _, _, _, _, _, _, _, _, ready⟩ :=
    default_fast_loop_entry current packet dataMode fast
  refine ⟨ctx, q, leaveRestore_run E, ?_, ?_,
    cursor, output, ready⟩
  · rw [strm]
    exact E.strm.symm
  · rw [state]
    exact E.st.symm

/-- The restored default data-mode caller reaches a terminating actual
fast-body loop on general represented buffer views. -/
theorem default_fast_loop_after_restore_run
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState}
    {slow : IL} {bs : List UInt8}
    (E : Env c h r zs z s)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    (mode : DataTableMode s.mode)
    (fast : (slow.have_ >= 6 && slow.left >= 258 &&
      slow.bits < 8) = true) :
    let restored :=
      setI (r.put h (leaveStream z slow)) zs (leaveState s slow)
    ∃ (ctx : FastLoopContext) (q result : Zlib.Inffast.L)
        (after : Heap),
      C.run (leaveRestore c slow) h = .ok ((), restored) ∧
      ctx.c.strm = c.strm ∧ ctx.c.state = c.st ∧
      C.run (cdoWhile (Zlib.Inffast.inflate_fast_body ctx.c)
        (fun q => do
          if q.broke then pure (false, q)
          else if ← Ptr.lt q.in_ ctx.c.last then
            pure (← Ptr.lt q.out ctx.c.end_, q)
          else pure (false, q)) q) restored =
          .ok (result, after) ∧
      FastLoopExit ctx after result := by
  dsimp only
  obtain ⟨ctx, q, restore, strm, state, _, _, ready⟩ :=
    default_fast_loop_after_restore E invariant buffers
      mode fast
  obtain ⟨result, after, run, final⟩ := ready.run
  exact ⟨ctx, q, result, after, restore, strm, state,
    run, final⟩

end Zlib.Inflate.Proofs
