import ZlibF.Proof.«inflate.c.wrapper-output-credit»
import ZlibF.Proof.«inflate.c.default-origin-state»
import ZlibF.Proof.«inflate.c.origin-fields-dispatch»
import ZlibF.Proof.«inflate.c.origin-fields-leave»
namespace Zlib.Inflate.Proofs.FunctionalTrailer
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.WrapperGlue
set_option autoImplicit false
theorem CHECK_mismatch_nonempty
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l current : IL}
    {ref : BRef} {off : Nat} {array : Array UInt8} {before incoming : List UInt8}
    (E : Env c h r zs z s) (wrap : s.wrap = 5) (flags : s.flags = 0)
    (seed : s.check = (adler32 before).toUInt64)
    (nonempty : l.out_ - l.left ≠ 0)
    (pointer : l.put = .ref ref off) (get : Space.get h ref = some array)
    (start : (l.out_ - l.left).toNat ≤ off) (finish : off ≤ array.size)
    (slice : (array.toList.drop (off - (l.out_ - l.left).toNat)).take
      (l.out_ - l.left).toNat = incoming)
    (pull : runX (NEEDBITS 32) l h = .ok ((.ok (), current), h))
    (outField : current.out_ = l.out_) (leftField : current.left = l.left)
    (putField : current.put = l.put)
    (trailer : ZSWAP32 current.hold ≠ (adler32 (before ++ incoming)).toUInt64) :
    ∃ i, strTable[i]? = some "incorrect data check" ∧
      runX (inflate_CHECK c) l h = .ok ((.ok (), { current with out_ := l.left }),
        tcBadHeap
          (setI (r.put h { z with total_out := z.total_out + (l.out_ - l.left).toUInt64, adler := (adler32 (before ++ incoming)).toUInt64 }) zs
            { s with total := s.total + (l.out_ - l.left).toUInt64, check := (adler32 (before ++ incoming)).toUInt64 })
          r zs { z with total_out := z.total_out + (l.out_ - l.left).toUInt64, adler := (adler32 (before ++ incoming)).toUInt64 }
          { s with total := s.total + (l.out_ - l.left).toUInt64, check := (adler32 (before ++ incoming)).toUInt64 } i) := by
  let out := l.out_ - l.left
  let value := (adler32 (before ++ incoming)).toUInt64
  let h1 : Heap := setI (r.put h { z with total_out := z.total_out + out.toUInt64 }) zs
    { s with total := s.total + out.toUInt64 }
  have get1 : Space.get h1 ref = some array := by
    rw [byte_view_get_setI, byte_view_get_stream_put]
    exact get
  have state1 : h1.istates zs = some { s with total := s.total + out.toUInt64 } := by
    simp [h1]
  have actualPointer : l.put.add (-(out.toNat : Int)) h1 =
      .ok (.ref ref (off - out.toNat), h1) := by
    rw [pointer]
    exact Ptr.sub_nat_ok get1 start finish
  have update0 := UPDATE_CHECK_zlib_view state1 flags get1 (by dsimp only [out]; omega :
    off - out.toNat + out.toNat ≤ array.size) s.check
  have checksum : adlerValue s.check ((array.toList.drop (off - out.toNat)).take out.toNat) = value := by
    rw [seed, slice]
    exact ZlibF.Math.DeflateChecksum.adler_value_append before incoming
  have update : UPDATE_CHECK (some (.tab zs)) s.check (.ref ref (off - out.toNat)) out h1 =
      .ok (value, h1) := by
    rw [update0, checksum]
  have actualPointer2 := actualPointer
  have update2 := update
  simp [h1, out, wrap, flags] at actualPointer2 update2
  let zs0 := { z with total_out := z.total_out + out.toUInt64, adler := value }
  let ss0 := { s with total := s.total + out.toUInt64, check := value }
  let heap0 := setI (r.put h zs0) zs ss0
  have getZ : r.get heap0 = some zs0 := by
    rw [ZStreamRef.get_setI]
    exact ZStreamRef.get_put_same E.hz _
  have getS : heap0.istates zs = some ss0 := by simp [heap0]
  obtain ⟨i, literal, bad⟩ := tcBadMode_run (c := c) "incorrect data check" lit_data_check
    E.strm E.st getZ getS
  refine ⟨i, literal, ?_⟩
  unfold inflate_CHECK
  rw [E.st]
  have bad2 := bad
  dsimp only [heap0, zs0, ss0, out, value] at bad2
  simp [wrap, flags] at bad2
  simp [runX_bind, runX_lift, ldI_eq, E.hs, wrap, pull, E.strm, runX_modify, runX_get,
    wrZ_eq, wrI_eq, E.hz, outField, leftField, putField, nonempty,
    show ((5 : Int32) &&& 4) ≠ 0 by decide, actualPointer2, update2,
    flags, trailer, runX_throw, chkCond, h1, out, value,
    ZStreamRef.put_setI, ZStreamRef.put_put, ZStreamRef.get_put_same E.hz, bad2, runX_pure]


#print axioms CHECK_mismatch_nonempty

/-- The actual call's physical output and the portion already credited
by source CHECK/leave statements. This internal ghost is populated by
payload execution producers, not required as a public caller contract. -/
structure OutputCredit (h : Heap) (z : ZStream) (s : InflateState) (l : IL)
    (prior emitted : List UInt8) (credited : Nat) : Prop where
  count : credited ≤ emitted.length
  checksum : AdlerCredit z s (prior ++ emitted.take credited)
  pending : (l.out_ - l.left).toNat = emitted.length - credited
  physical : ∃ ref off a, l.put = .ref ref off ∧ Space.get h ref = some a ∧
    emitted.length ≤ off ∧ off ≤ a.size ∧
    ZlibF.Math.LZ77Copy.writtenBytes a off emitted.length = emitted

/-- Suffixes of an independently observed physical prefix are exactly
the bytes used by the source checksum's put-minus-pending expression. -/
theorem writtenBytes_pending {a : Array UInt8} {off credited : Nat} {emitted : List UInt8}
    (made : emitted.length ≤ off) (count : credited ≤ emitted.length)
    (physical : ZlibF.Math.LZ77Copy.writtenBytes a off emitted.length = emitted) :
    ZlibF.Math.LZ77Copy.writtenBytes a off (emitted.length - credited) = emitted.drop credited := by
  calc
    ZlibF.Math.LZ77Copy.writtenBytes a off (emitted.length - credited) =
        (ZlibF.Math.LZ77Copy.writtenBytes a off emitted.length).drop credited := by
      simp only [ZlibF.Math.LZ77Copy.writtenBytes, List.drop_take, List.drop_drop]
      have index : off - (emitted.length - credited) = off - emitted.length + credited := by omega
      rw [index]
    _ = emitted.drop credited := congrArg (List.drop credited) physical

theorem OutputCredit.pending_slice
    {h : Heap} {z : ZStream} {s : InflateState} {l : IL} {prior emitted : List UInt8} {credited : Nat}
    (ledger : OutputCredit h z s l prior emitted credited) :
    ∃ ref off a, l.put = .ref ref off ∧ Space.get h ref = some a ∧
      (l.out_ - l.left).toNat ≤ off ∧ off ≤ a.size ∧
      ZlibF.Math.LZ77Copy.writtenBytes a off (l.out_ - l.left).toNat = emitted.drop credited := by
  obtain ⟨ref, off, a, pointer, get, made, bound, physical⟩ := ledger.physical
  refine ⟨ref, off, a, pointer, get, by rw [ledger.pending]; omega, bound, ?_⟩
  rw [ledger.pending]
  exact writtenBytes_pending made ledger.count physical

/-- Crediting the source's pending suffix produces the independent
checksum of all observed bytes. No final checksum value is an oracle. -/
theorem output_credit_append (prior emitted : List UInt8) (credited : Nat) :
    (prior ++ emitted.take credited) ++ emitted.drop credited = prior ++ emitted := by
  rw [List.append_assoc, List.take_append_drop]

/-- Actual complete inf_leave consumes the internal two-part ledger.
Ordinary returns credit all actual call output; genuine window allocation
failure retains exactly the previously credited prefix. Arbitrary output
capacity, zero output and same-object separated views remain admitted. -/
theorem leave_from_output_history
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs prior emitted : List UInt8} {credited : Nat}
    (E : Env c h r zs z s) (origin : DefaultOriginState h r zs z s)
    (allocator : DefAlloc z) (packet : DispatchBuffers h r l bs) (bits : l.bits.toNat ≤ 39)
    (ledger : OutputCredit h z s l prior emitted credited) :
    ∃ rc after current state,
      inflate_leave c l h = .ok (rc, after) ∧
      DefaultStateJ after r zs current state ∧ DefAlloc current ∧
      current.next_out = l.put ∧ current.avail_out = l.left ∧
      ((AdlerCredit current state (prior ++ emitted)) ∨
        (rc = Z_MEM_ERROR ∧ state.mode = MEM ∧
          AdlerCredit current state (prior ++ emitted.take credited))) := by
  obtain ⟨rc, after, current, state, ref, off, a, incoming, run, final, alloc,
    pointer, get, view, written, _length, _bytes, put, left, outcome⟩ :=
    inflate_leave_adler_observed E origin.toDefaultStateJ allocator packet bits ledger.checksum
  obtain ⟨ref0, off0, a0, pointer0, get0, _start0, _bound0, slice0⟩ := ledger.pending_slice
  have samePointer := pointer.symm.trans pointer0
  cases samePointer
  have sameArray : a0 = a := Option.some.inj (get0.symm.trans get)
  subst a0
  have sameIncoming : incoming = emitted.drop credited := written.trans slice0
  refine ⟨rc, after, current, state, run, final, alloc, put, left, ?_⟩
  rcases outcome with ordinary | memory
  · left
    rw [sameIncoming, output_credit_append] at ordinary
    exact ordinary.2
  · exact Or.inr memory

#print axioms writtenBytes_pending
#print axioms OutputCredit.pending_slice
#print axioms output_credit_append
#print axioms leave_from_output_history


/-- Zero-pending-output mismatch follows the same actual BAD source
branch without changing its old checksum or crediting any byte twice. -/
theorem CHECK_mismatch_empty
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l current : IL}
    (E : Env c h r zs z s) (wrap : s.wrap = 5) (flags : s.flags = 0)
    (empty : l.out_ = l.left)
    (pull : runX (NEEDBITS 32) l h = .ok ((.ok (), current), h))
    (outField : current.out_ = l.out_) (leftField : current.left = l.left)
    (trailer : ZSWAP32 current.hold ≠ s.check) :
    ∃ i, strTable[i]? = some "incorrect data check" ∧
      runX (inflate_CHECK c) l h =
        .ok ((.ok (), { current with out_ := l.left }), tcBadHeap h r zs z s i) := by
  obtain ⟨i, literal, bad⟩ := tcBadMode_run (c := c) "incorrect data check" lit_data_check
    E.strm E.st E.hz E.hs
  refine ⟨i, literal, ?_⟩
  have amount : current.out_ - current.left = 0 := by rw [outField, leftField, empty]; simp
  unfold inflate_CHECK
  rw [runX_bind, runX_ldS E]
  simp only [wrap, show ((5 : Int32) != 0) = true from rfl, ↓reduceIte]
  rw [runX_bind, pull]
  simp only []
  have shapeS : { s with wrap := 5, flags := 0 } = s := by rw [← wrap, ← flags]
  simp [runX_bind, runX_lift, runX_modify, runX_get, amount, E.strm, E.st,
    wrZ_eq, wrI_eq, ldI_eq, E.hz, E.hs, ZStreamRef.put_self E.hz, flags, wrap,
    trailer, bad, setI_setI, setI, upd_upd, upd_self _ _ _ E.hs,
    outField, leftField, empty, bind_app, pure_app, shapeS,
    show ((5 : Int32) &&& 4) ≠ 0 by decide, runX_pure]

#print axioms CHECK_mismatch_empty


/-- Source-level CHECK classification after the actual trailer pull.
The expected checksum is derived from physical output and its credited
history. Both matching and mismatching inputs are covered. -/
theorem CHECK_after_pull
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l current : IL} {prior emitted : List UInt8} {credited : Nat}
    (E : Env c h r zs z s) (ledger : OutputCredit h z s l prior emitted credited)
    (pull : runX (NEEDBITS 32) l h = .ok ((.ok (), current), h))
    (outField : current.out_ = l.out_) (leftField : current.left = l.left)
    (putField : current.put = l.put) :
    let zc := { z with total_out := z.total_out + (l.out_ - l.left).toUInt64, adler := (adler32 (prior ++ emitted)).toUInt64 }
    let sc := { s with total := s.total + (l.out_ - l.left).toUInt64, check := (adler32 (prior ++ emitted)).toUInt64 }
    let hc := setI (r.put h zc) zs sc
    (ZSWAP32 current.hold = (adler32 (prior ++ emitted)).toUInt64 →
      runX (inflate_CHECK c) l h = .ok
        ((.error Ex.leave, { current with out_ := l.left, hold := 0, bits := 0, ret := Z_STREAM_END }),
          setI hc zs { sc with mode := DONE })) ∧
    (ZSWAP32 current.hold ≠ (adler32 (prior ++ emitted)).toUInt64 →
      ∃ i, strTable[i]? = some "incorrect data check" ∧
        runX (inflate_CHECK c) l h = .ok
          ((.ok (), { current with out_ := l.left }), tcBadHeap hc r zs zc sc i)) := by
  dsimp only
  obtain ⟨ref, off, a, pointer, get, start, bound, physical⟩ := ledger.pending_slice
  have appended := output_credit_append prior emitted credited
  by_cases empty : l.out_ = l.left
  · have zero : (l.out_ - l.left).toNat = 0 := by rw [empty]; simp
    have fullyCredited : credited = emitted.length := by
      have pending := ledger.pending
      rw [zero] at pending
      have count := ledger.count
      omega
    have expected : (adler32 (prior ++ emitted)).toUInt64 = s.check := by
      have seed := ledger.checksum.2.2.1
      rw [fullyCredited, List.take_length] at seed
      exact seed.symm
    have streamEq : { z with total_out := z.total_out + (l.out_ - l.left).toUInt64, adler := (adler32 (prior ++ emitted)).toUInt64 } = z := by
      simp only [empty, UInt32.sub_self, show (0 : UInt32).toUInt64 = 0 from rfl, UInt64.add_zero, expected]
      rw [← ledger.checksum.2.2.2]
    have stateEq : { s with total := s.total + (l.out_ - l.left).toUInt64, check := (adler32 (prior ++ emitted)).toUInt64 } = s := by
      simp only [empty, UInt32.sub_self, show (0 : UInt32).toUInt64 = 0 from rfl, UInt64.add_zero, expected]
    rw [streamEq, stateEq, ZStreamRef.put_self E.hz]
    have heapEq : setI h zs s = h := by simp only [setI, upd_self _ _ _ E.hs]
    rw [heapEq]
    constructor
    · intro matched
      simpa only [empty, UInt32.sub_self, show (0 : UInt32).toUInt64 = 0 from rfl, UInt64.add_zero, expected]
        using inflate_CHECK_zlib_zero_output_cut E ledger.checksum.1 ledger.checksum.2.1 empty pull
          outField leftField (matched.trans expected)
    · intro mismatched
      exact CHECK_mismatch_empty E ledger.checksum.1 ledger.checksum.2.1 empty pull outField leftField
        (by rwa [expected] at mismatched)
  · have nonempty : l.out_ - l.left ≠ 0 := by
      intro zero
      apply empty
      simpa using UInt32.sub_eq_iff_eq_add.mp zero
    constructor
    · intro matched
      have actual := inflate_CHECK_zlib_output_append_cut E ledger.checksum.1 ledger.checksum.2.1
        ledger.checksum.2.2.1 nonempty pointer get start bound physical pull outField leftField putField
        (by rw [appended]; exact matched)
      rw [appended] at actual
      simpa only [setI_setI] using actual
    · intro mismatched
      have actual := CHECK_mismatch_nonempty E ledger.checksum.1 ledger.checksum.2.1
        ledger.checksum.2.2.1 nonempty pointer get start bound physical pull outField leftField putField
        (by rw [appended]; exact mismatched)
      simpa only [appended] using actual

#print axioms CHECK_after_pull

/-- Real last-block TYPE/TYPEDO aligns the arbitrary residual held bits,
retains the physical/credited output ledger, and enters CHECK in the same
mainwhile. This does not turn a TYPE cut into a public return. -/
theorem last_type_to_check_history
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs prior emitted : List UInt8} {credited : Nat}
    (E : Env c h r zs z s) (origin : DefaultOriginState h r zs z s)
    (packet : DispatchBuffers h r l bs) (bits : l.bits.toNat ≤ 39)
    (ledger : OutputCredit h z s l prior emitted credited)
    (mode : s.mode = TYPE ∨ s.mode = TYPEDO) (last : s.last ≠ 0)
    (flush : c.flush ≠ Z_BLOCK ∧ c.flush ≠ Z_TREES) :
    let state := { s with mode := CHECK }
    let after := setI h zs state
    runX (inflate_dispatch c) l h = .ok ((.ok (), bytebits l), after) ∧
    DefaultOriginState after r zs z state ∧ DispatchBuffers after r (bytebits l) bs ∧
    (bytebits l).bits.toNat ≤ 39 ∧ (bytebits l).bits.toNat % 8 = 0 ∧
    OutputCredit after z state (bytebits l) prior emitted credited ∧
    stream (bytebits l) bs = (stream l bs).drop (l.bits.toNat % 8) := by
  dsimp only
  have actual : runX (inflate_dispatch c) l h =
      .ok ((.ok (), bytebits l), setI h zs { s with mode := CHECK }) := by
    rw [inflate_dispatch_block_type E l mode]
    rcases mode with selected | selected
    · rw [ite_eq_left selected, inflate_TYPE_go c l h flush]
      exact inflate_TYPEDO_last E l last
    · have different : s.mode ≠ TYPE := by rw [selected]; decide
      rw [ite_eq_right different]
      exact inflate_TYPEDO_last E l last
  obtain ⟨_outcome, _regs, _after, currentZ, currentS, used, _made, _bound, source,
    current, currentPacket, _sizes, _next, count, _put, _left, _bits, _progress⟩ :=
    inflate_dispatch_default_origin_state_rank E origin packet bits
  have same := Except.ok.inj (source.symm.trans actual)
  cases same
  have getZ : r.get (setI h zs { s with mode := CHECK }) = some z := by
    rw [ZStreamRef.get_setI]; exact E.hz
  have sameZ : currentZ = z := Option.some.inj (current.good.live.hz.symm.trans getZ)
  have sameS : currentS = { s with mode := CHECK } := by
    apply Option.some.inj
    rw [← current.good.live.hs, setI_istates_same]
  subst currentZ currentS
  have usedZero : used = 0 := by change l.have_.toNat + used = l.have_.toNat at count; omega
  subst used
  simp only [List.drop_zero] at currentPacket
  obtain ⟨inv, bitSource, bitCount⟩ := BYTEBITS_inv packet.bits
  have alignment : (bytebits l).bits.toNat = l.bits.toNat - l.bits.toNat % 8 := by
    change (l.bits - (l.bits &&& 7)).toNat = _
    rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (and7_le l)), and7_toNat]
  have aligned : (bytebits l).bits.toNat % 8 = 0 := by rw [alignment]; omega
  refine ⟨actual, current, currentPacket, by rw [alignment]; omega, aligned, ?_, bitSource⟩
  refine ⟨ledger.count, ledger.checksum, ledger.pending, ?_⟩
  obtain ⟨ref, off, a, pointer, get, made, bound, physical⟩ := ledger.physical
  exact ⟨ref, off, a, pointer, (byte_view_get_setI h zs { s with mode := CHECK } ref).trans get,
    made, bound, physical⟩

#print axioms last_type_to_check_history

/-- An independently valid trailer closes the real CHECK mainwhile suffix
and the real complete inf_leave. The checksum is computed from the
observed old output plus this call's physical output, irrespective of
output capacity or how much CHECK has already credited. -/
theorem CHECK_valid_trailer_suffix
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs prior emitted : List UInt8} {credited : Nat}
    (E : Env c h r zs z s) (origin : DefaultOriginState h r zs z s)
    (allocator : DefAlloc z) (packet : DispatchBuffers h r l bs) (bits : l.bits.toNat ≤ 39)
    (aligned : l.bits.toNat % 8 = 0) (mode : s.mode = CHECK)
    (ledger : OutputCredit h z s l prior emitted credited) (future : List Bool)
    (valid : stream l bs = bytesBits (be32 (adler32 (prior ++ emitted)).toNat) ++ future) :
    ∃ regs used checked current state after finalZ finalS,
      used ≤ bs.length ∧
      runX (xwhile (pure true) (inflate_dispatch c)) l h = .ok ((.error Ex.leave, regs), checked) ∧
      DefaultOriginState checked r zs current state ∧
      DispatchBuffers checked r regs (bs.drop used) ∧
      state.mode = DONE ∧ regs.ret = Z_STREAM_END ∧ regs.out_ = regs.left ∧
      stream regs (bs.drop used) = future ∧
      inflate_leave c regs checked = .ok (Z_STREAM_END, after) ∧
      DefaultOriginState after r zs finalZ finalS ∧ DefAlloc finalZ ∧
      AdlerCredit finalZ finalS (prior ++ emitted) := by
  obtain ⟨ref, off, a, pointer, get, start, bound, physical⟩ := ledger.pending_slice
  have appended := output_credit_append prior emitted credited
  obtain ⟨regs, used, checked, current, state, usedBound, checkRun, getZ, getS,
    currentCredit, currentMode, next, put, left, out, hold, bitField, ret, futureEq⟩ :=
    CHECK_adler_commit E ledger.checksum packet.bits bits aligned pointer get start bound physical future
      (by rw [appended]; exact valid)
  rw [appended] at currentCredit
  have step := (inflate_dispatch_CHECK E l mode).trans checkRun
  obtain ⟨_outcome, _regs, _heap, observedZ, observedS, observedUsed, _made, _bound,
    observedRun, observedOrigin, observedPacket, _sizes, observedNext, count, _put, _left, observedBits, _progress⟩ :=
    inflate_dispatch_default_origin_state_rank E origin packet bits
  have same := Except.ok.inj (observedRun.symm.trans step)
  cases same
  have sameZ : observedZ = current := Option.some.inj (observedOrigin.good.live.hz.symm.trans getZ)
  have sameS : observedS = state := Option.some.inj (observedOrigin.good.live.hs.symm.trans getS)
  subst observedZ observedS
  have consumed : observedUsed = used := by
    rcases packet.bits.next with empty | inputPointer
    · rw [empty] at usedBound _bound
      simp only [List.length_nil] at usedBound _bound
      omega
    · obtain ⟨inputRef, inputArray, inputOff, inputPtr, _inputGet, _inputRoom, _inputBytes⟩ := inputPointer
      have samePtr := observedNext.symm.trans next
      simp only [inputPtr, inputAdvance] at samePtr
      have indices : inputOff + observedUsed = inputOff + used := by injection samePtr
      omega
  subst observedUsed
  have currentAlloc : DefAlloc current := by
    obtain ⟨regs0, used0, _used0Bound, explicit, _rest⟩ :=
      inflate_CHECK_zlib_valid_trailer E ledger.checksum.1 ledger.checksum.2.1 ledger.checksum.2.2.1
        ledger.checksum.2.2.2 packet.bits bits aligned pointer get start bound physical future
        (by rw [appended]; exact valid)
    have same := Except.ok.inj (checkRun.symm.trans explicit)
    cases same
    have exactGet : r.get
        (setI (r.put h { z with total_out := z.total_out + (l.out_ - l.left).toUInt64, adler := (adler32 ((prior ++ emitted.take credited) ++ emitted.drop credited)).toUInt64 }) zs
          { s with total := s.total + (l.out_ - l.left).toUInt64, check := (adler32 ((prior ++ emitted.take credited) ++ emitted.drop credited)).toUInt64, mode := DONE }) =
        some { z with total_out := z.total_out + (l.out_ - l.left).toUInt64, adler := (adler32 ((prior ++ emitted.take credited) ++ emitted.drop credited)).toUInt64 } := by
      rw [ZStreamRef.get_setI]
      exact ZStreamRef.get_put_same E.hz _
    have streamEq := Option.some.inj (getZ.symm.trans exactGet)
    rw [streamEq]
    exact allocator
  have env : Env c checked r zs current state := ⟨E.strm, E.st, getZ, getS⟩
  obtain ⟨after, finalZ, finalS, leave, finalGetZ, finalGetS, finalCredit⟩ :=
    inflate_leave_after_CHECK_adler env observedOrigin.good currentAlloc.1 observedOrigin.pending
      observedPacket observedBits currentCredit out ret
  obtain ⟨rc, _after, otherZ, otherS, otherLeave, finalOrigin, finalAlloc⟩ :=
    inflate_leave_default_origin env observedOrigin currentAlloc observedPacket observedBits
  have same := Except.ok.inj (otherLeave.symm.trans leave)
  cases same
  have sameZ : otherZ = finalZ := Option.some.inj (finalOrigin.good.live.hz.symm.trans finalGetZ)
  have sameS : otherS = finalS := Option.some.inj (finalOrigin.good.live.hs.symm.trans finalGetS)
  subst otherZ otherS
  have loop := xwhile_run_chain (inflate_dispatch c) (fun _ => l) (fun _ => h)
    0 (by unfold fuel; decide) Ex.leave regs checked (by intro j impossible; omega) step
  exact ⟨regs, used, checked, current, state, after, finalZ, finalS, usedBound,
    loop, observedOrigin, observedPacket, currentMode, ret, out, futureEq,
    leave, finalOrigin, finalAlloc, finalCredit⟩

#print axioms CHECK_valid_trailer_suffix

/-- LOAD starts a fresh physical call-output segment. The cumulative
checksum seed is a proven internal record relation. -/
theorem OutputCredit.start
    {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs prior : List UInt8}
    (good : Good h r zs z s) (packet : DispatchBuffers h r l bs)
    (fresh : l.out_ = l.left) (credit : AdlerCredit z s prior) :
    OutputCredit h z s l prior [] 0 := by
  obtain ⟨ref, a, off, pointer, get, _ro, room, _count, _produced, _unowned⟩ :=
    callerRange_slow_output good l packet.output.range packet.output.nonnull
      packet.output.count packet.output.produced
  refine ⟨by simp, by simpa using credit, by rw [fresh]; simp, ?_⟩
  exact ⟨ref, off, a, pointer, get, by simp, by omega, by
    simp [ZlibF.Math.LZ77Copy.writtenBytes]⟩

/-- An actual decoder's scalar frame and independently observed physical
prefix establish the uncredited call-output ledger at its source exit.
This is a representation lemma; the fields are supplied by execution
proofs rather than a caller or callee contract. -/
theorem OutputCredit.from_observed_frame
    {h : Heap} {z z0 : ZStream} {s s0 : InflateState} {l : IL}
    {prior emitted : List UInt8} {ref : BRef} {off : Nat} {a : Array UInt8}
    (credit : AdlerCredit z0 s0 prior)
    (check : s.check = s0.check) (adler : z.adler = z0.adler)
    (wrap : s.wrap = s0.wrap) (flags : s.flags = s0.flags)
    (count : (l.out_ - l.left).toNat = emitted.length)
    (pointer : l.put = .ref ref off) (get : Space.get h ref = some a)
    (start : emitted.length ≤ off) (bound : off ≤ a.size)
    (physical : ZlibF.Math.LZ77Copy.writtenBytes a off emitted.length = emitted) :
    OutputCredit h z s l prior emitted 0 := by
  refine ⟨by omega, ?_, by simpa using count, ref, off, a, pointer, get, start, bound, physical⟩
  simp only [List.take_zero, List.append_nil]
  exact ⟨wrap.trans credit.1, flags.trans credit.2.1,
    check.trans credit.2.2.1, adler.trans (credit.2.2.2.trans check.symm)⟩

#print axioms OutputCredit.start
#print axioms OutputCredit.from_observed_frame
theorem leaveFinalize_trailer_fields {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z current : ZStream} {s : InflateState} (E : Env c h r zs current s)
    (invariant : DefaultOriginState h r zs current s) (allocator : DefAlloc current)
    (output : LeaveOutputView h l) (cursor : z.next_out = l.put) (count : z.avail_out = l.left) :
    ∃ rc after stream state, leaveFinalize c l z h = .ok (rc, after) ∧
      DefaultOriginState after r zs stream state ∧ DefAlloc stream ∧
      state.hold = s.hold ∧ state.bits = s.bits ∧
      (state.mode = s.mode ∨ (rc = Z_MEM_ERROR ∧ state.mode = MEM)) := by
  have statics : Zlib.Crc32.Proofs.StaticsOK h := by
    unfold Zlib.Crc32.Proofs.StaticsOK
    rw [invariant.globals]
    exact ⟨rfl, rfl⟩
  obtain ⟨rc, after, stream, state, run, good, frame, views, ret, codes, static⟩ :=
    leaveFinalize_all_wrappers_safe E invariant.good output statics cursor count
  have sizes : ByteViewSizes h after := by
    intro ref
    rw [views ref]
  have finalJ := invariant.toDefaultStateJ.leave_metadata good frame codes (sizes.platform invariant.platform) static
  have final := invariant.of_fields finalJ (by rw [frame]) (by rw [frame]) (by rw [frame])
  have fixed := streamFrameM_leaveFinalize r c l z E.strm h rc after run
  refine ⟨rc, after, stream, state, run, final,
    fixed.allocator invariant.good.live.hz good.live.hz allocator, ?_⟩
  rw [frame]
  exact ⟨rfl, rfl, Or.inl rfl⟩

/-- Actual window success and allocation failure preserve the stored remaining length. -/
theorem leaveWithWindow_trailer_fields {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (E : Env c h r zs z s)
    (invariant : DefaultOriginState h r zs z s) (allocator : DefAlloc z)
    (output : OutputCursorInvariant h r l) (cursor : z.next_out = l.put) (count : z.avail_out = l.left) :
    ∃ rc after stream state, leaveWithWindow c l z h = .ok (rc, after) ∧
      DefaultOriginState after r zs stream state ∧ DefAlloc stream ∧
      state.hold = s.hold ∧ state.bits = s.bits ∧
      (state.mode = s.mode ∨ (rc = Z_MEM_ERROR ∧ state.mode = MEM)) := by
  obtain ⟨ref, bytes, off, put, get, _, room, leftCount, produced, unowned⟩ :=
    callerRange_slow_output invariant.good l output.range output.nonnull output.count output.produced
  have amount : (l.out_ - z.avail_out).toNat = l.out_.toNat - l.left.toNat := by
    rw [count, UInt32.toNat_sub_of_le _ _ leftCount]
  have start : (l.out_ - z.avail_out).toNat ≤ off := by rw [amount]; exact produced
  have bound : off ≤ bytes.size := by omega
  have separate : Separate (.ref ref (off - (l.out_ - z.avail_out).toNat))
      (l.out_ - z.avail_out).toNat s.window (2 ^ s.wbits.toNat) := by
    rcases invariant.good.inv.win.block with null | ⟨w, a, win, _, _, _⟩
    · simp [Separate, null]
    · simp [Separate, win, unowned w win]
  obtain ⟨wr, heap1, state1, windowRun, good1, windowFrame, sourceView, codeViews, outcome⟩ :=
    updatewindow_decoder_boundary (copy := l.out_ - z.avail_out) invariant.good allocator.1 get start bound unowned
  obtain ⟨platform, static⟩ := updatewindow_platform_public invariant.good invariant.platform
    allocator.1 get start bound separate windowRun
  have currentJ := invariant.toDefaultStateJ.window_update good1 windowFrame codeViews platform static
  have current := invariant.window_update currentJ windowFrame
  rcases outcome with success | failure
  · subst wr
    have env1 : Env c heap1 r zs z state1 := ⟨E.strm, E.st, good1.live.hz, good1.live.hs⟩
    have view : LeaveOutputView heap1 l :=
      ⟨ref, off, bytes, put, sourceView, by rw [count] at start; exact start, bound⟩
    obtain ⟨rc, after, stream, state, finish, final, finalAllocator, finalProgress⟩ :=
      leaveFinalize_trailer_fields (z := z) env1 current allocator view cursor count
    refine ⟨rc, after, stream, state, ?_, final, finalAllocator, by rw [windowFrame] at finalProgress; exact finalProgress⟩
    unfold leaveWithWindow
    rw [bind_app, E.strm, cursor, put, windowRun]
    simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    exact finish
  · obtain ⟨eqrc, _, stateEq, heapEq⟩ := failure
    subst wr
    subst state1
    let state := { s with mode := MEM }
    have good : Good (setI heap1 zs state) r zs z state :=
      good1.decode_update (by rfl) (by change HEAD ≤ MEM ∧ MEM ≤ SYNC; decide)
    have finalJ := current.toDefaultStateJ.mem_update good (platform.with_istates _) rfl
    have final := current.of_fields finalJ rfl rfl rfl
    refine ⟨Z_MEM_ERROR, setI heap1 zs state, z, state, ?_, final, allocator, ⟨rfl, rfl, Or.inr ⟨rfl, rfl⟩⟩⟩
    unfold leaveWithWindow
    rw [bind_app, E.strm, cursor, put, windowRun]
    simp only [show ((1 : Int32) != 0) = true from rfl, ↓reduceIte, bind_app, E.st,
      setMode_tab good1.live.hs, pure_app]
    rfl

/-- The complete actual leave preserves the stored remaining length. -/
theorem inflate_leave_trailer_fields {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs : List UInt8} (E : Env c h r zs z s)
    (invariant : DefaultOriginState h r zs z s) (allocator : DefAlloc z)
    (buffers : DispatchBuffers h r l bs) (bits : l.bits.toNat ≤ 39) :
    ∃ rc after stream state, inflate_leave c l h = .ok (rc, after) ∧
      DefaultOriginState after r zs stream state ∧ DefAlloc stream ∧
      state.hold = l.hold ∧ state.bits = l.bits ∧
      (state.mode = s.mode ∨ (rc = Z_MEM_ERROR ∧ state.mode = MEM)) := by
  let stream0 := leaveStream z l
  let state0 := leaveState s l
  let heap0 := setI (r.put h stream0) zs state0
  have currentJ := invariant.toDefaultStateJ.restore E buffers bits
  have current := invariant.of_fields currentJ rfl rfl rfl
  have env0 : Env c heap0 r zs stream0 state0 :=
    ⟨E.strm, E.st, current.good.live.hz, current.good.live.hs⟩
  have views0 : ∀ ref : BRef, (Space.get heap0 ref : Option (Array UInt8)) = Space.get h ref := by
    intro ref
    rw [byte_view_get_setI, byte_view_get_stream_put]
  have output0 : OutputCursorInvariant heap0 r l :=
    ⟨callerRange_transport invariant.good current.good rfl views0 (by
      intro ref
      rw [byte_view_ro_setI, byte_view_ro_stream_put]) buffers.output.range,
      buffers.output.nonnull, buffers.output.count, buffers.output.produced⟩
  by_cases update : (s.wsize != 0 || (l.out_ != l.left && s.mode < BAD &&
      (s.mode < CHECK || c.flush != Z_FINISH))) = true
  · obtain ⟨rc, after, stream, state, run, final, finalAllocator, finalProgress⟩ :=
      leaveWithWindow_trailer_fields env0 current allocator output0 rfl rfl
    refine ⟨rc, after, stream, state, ?_, final, finalAllocator, finalProgress⟩
    rw [inflate_leave_restore_cut E, leaveAfterRestore_window env0 update]
    exact run
  · have skip : (s.wsize != 0 || (l.out_ != l.left && s.mode < BAD &&
      (s.mode < CHECK || c.flush != Z_FINISH))) = false := by
      cases eq : (s.wsize != 0 || (l.out_ != l.left && s.mode < BAD &&
        (s.mode < CHECK || c.flush != Z_FINISH))) <;> simp_all
    obtain ⟨rc, after, stream, state, run, final, finalAllocator, finalProgress⟩ :=
      leaveFinalize_trailer_fields (z := stream0) env0 current allocator
        (leaveOutputView_of_cursor current.good output0) rfl rfl
    refine ⟨rc, after, stream, state, ?_, final, finalAllocator, finalProgress⟩
    rw [inflate_leave_restore_cut E, leaveAfterRestore_no_window env0 skip]
    exact run

#print axioms leaveFinalize_trailer_fields
#print axioms leaveWithWindow_trailer_fields
#print axioms inflate_leave_trailer_fields

/-- Actual NEEDBITS waiting exits CHECK before its checksum statements. -/
theorem CHECK_wait_cut
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (E : Env c h r zs z s) (l regs : IL) (wrap : s.wrap ≠ 0)
    (pull : runX (NEEDBITS 32) l h = .ok ((.error Ex.leave, regs), h)) :
    runX (inflate_CHECK c) l h = .ok ((.error Ex.leave, regs), h) := by
  unfold inflate_CHECK
  rw [runX_bind, runX_ldS E]
  simp only [show (s.wrap != 0) = true by simp [wrap], ite_true]
  rw [runX_bind, pull]

/-- Any short actual trailer prefix exits the same real mainwhile and
executes complete leave. Actual pending output is credited once on
ordinary return; true MEM retains the previous credited prefix. No output
capacity or absent-window premise is imposed. -/
theorem CHECK_wait_suffix
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs prior emitted : List UInt8} {credited : Nat}
    (E : Env c h r zs z s) (origin : DefaultOriginState h r zs z s)
    (allocator : DefAlloc z) (packet : DispatchBuffers h r l bs) (bits : l.bits.toNat ≤ 39)
    (mode : s.mode = CHECK) (ledger : OutputCredit h z s l prior emitted credited)
    (short : l.bits.toNat + 8 * bs.length < 32) :
    ∃ regs rc after current state,
      runX (xwhile (pure true) (inflate_dispatch c)) l h = .ok ((.error Ex.leave, regs), h) ∧
      regs.have_ = 0 ∧ regs.next = inputAdvance l.next bs.length ∧
      regs.put = l.put ∧ regs.left = l.left ∧ regs.out_ = l.out_ ∧
      regs.bits.toNat = l.bits.toNat + 8 * bs.length ∧
      natBits regs.bits.toNat regs.hold.toNat = natBits l.bits.toNat l.hold.toNat ++ bytesBits bs ∧
      inflate_leave c regs h = .ok (rc, after) ∧
      DefaultOriginState after r zs current state ∧ DefAlloc current ∧
      state.hold = regs.hold ∧ state.bits = regs.bits ∧
      (state.mode = CHECK ∨ (rc = Z_MEM_ERROR ∧ state.mode = MEM)) ∧
      ((AdlerCredit current state (prior ++ emitted)) ∨
        (rc = Z_MEM_ERROR ∧ state.mode = MEM ∧
          AdlerCredit current state (prior ++ emitted.take credited))) := by
  obtain ⟨outcome, regs, used, pull, usedBound, inv, source, count, shape,
    bitBound, _identity, full, waiting, kinds, cursor⟩ := NEEDBITS_run_cursor packet.bits 32 (by decide)
  have error : outcome = .error Ex.leave := by
    rcases kinds with normal | error
    · have enough := full normal
      change 32 ≤ regs.bits.toNat at enough
      omega
    · exact error
  obtain ⟨all, zero, below⟩ := waiting error
  subst used
  rw [List.drop_length] at inv source
  have sourceWord : natBits regs.bits.toNat regs.hold.toNat =
      natBits l.bits.toNat l.hold.toNat ++ bytesBits bs := by
    simpa only [stream, bytesBits_nil, List.append_nil] using source
  have symbol : SymbolRegShape l regs := by rw [shape]; rfl
  have packet0 := packet.consume origin.good origin.good rfl (fun _ => rfl) (fun _ => rfl)
    symbol cursor usedBound (by simpa only [List.drop_length] using inv)
  rw [List.drop_length] at packet0
  have step := (inflate_dispatch_CHECK E _ mode).trans
    (CHECK_wait_cut E _ regs (by rw [ledger.checksum.1]; decide) (by rwa [error] at pull))
  have small : regs.bits.toNat ≤ 39 := by omega
  have regsLedger : OutputCredit h z s regs prior emitted credited := by
    refine ⟨ledger.count, ledger.checksum, ?_, ?_⟩
    · rw [shape]
      exact ledger.pending
    · rw [shape]
      exact ledger.physical
  obtain ⟨rc, after, current, state, leave, final, finalAlloc, held, bitfield, modefield⟩ :=
    inflate_leave_trailer_fields E origin allocator packet0 small
  obtain ⟨rc0, after0, current0, state0, observed, currentJ, alloc0, put0, left0, finalCredit⟩ :=
    leave_from_output_history E origin allocator packet0 small regsLedger
  have same := Except.ok.inj (leave.symm.trans observed)
  cases same
  have sameZ : current0 = current := Option.some.inj (currentJ.good.live.hz.symm.trans final.good.live.hz)
  have sameS : state0 = state := Option.some.inj (currentJ.good.live.hs.symm.trans final.good.live.hs)
  subst current0 state0
  have loop := xwhile_run_chain (inflate_dispatch c) (fun _ => l) (fun _ => h)
    0 (by unfold fuel; decide) Ex.leave regs h (by intro j impossible; omega) step
  refine ⟨regs, rc, after, current, state, loop, zero, cursor, by rw [shape], by rw [shape],
    by rw [shape], count, sourceWord, leave, final, finalAlloc, held, bitfield, ?_⟩
  constructor
  · rcases modefield with normal | failure
    · exact Or.inl (normal.trans mode)
    · exact Or.inr failure
  · exact finalCredit

#print axioms CHECK_wait_cut
#print axioms CHECK_wait_suffix

end Zlib.Inflate.Proofs.FunctionalTrailer
