import ZlibF.Proof.«inflate.c.functional-trailer»
import ZlibF.Proof.«inflate.c.header-progress-observed»
import ZlibF.Spec.Public.Sequences

namespace Zlib.Inflate.Proofs.FunctionalTrailerSplits
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.WrapperGlue Zlib.Inflate.Proofs.FunctionalTrailer
set_option autoImplicit false
/- Generic CHECK-only roots reused verbatim from the previous checked
trailer package. No STORED or COPY execution hypothesis is imported. -/
theorem origin_packet_of_actual
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat} {z stream0 : ZStream}
    {s state : InflateState} {l regs : IL} {bs : List UInt8} {outcome : Except Ex Unit}
    (E : Env c h r zs z s) (initial : DefaultOriginState h r zs z s)
    (packet : DispatchBuffers h r l bs) (bits : l.bits.toNat ≤ 39)
    (actual : runX (inflate_dispatch c) l h = .ok ((outcome, regs), after))
    (getZ : r.get after = some stream0) (getS : after.istates zs = some state) :
    DefaultOriginState after r zs stream0 state ∧
      DispatchBuffers after r regs (bs.drop (l.have_.toNat - regs.have_.toNat)) := by
  obtain ⟨exit, locals, heap0, stream1, state1, used, made, _bound, run, current,
    nextPacket, _sizes, _next, count, _put, _left, _bits, _rank⟩ :=
    inflate_dispatch_default_origin_state_rank E initial packet bits
  have same := Except.ok.inj (run.symm.trans actual)
  cases same
  have sameZ : stream1 = stream0 := Option.some.inj (current.good.live.hz.symm.trans getZ)
  have sameS : state1 = state := Option.some.inj (current.good.live.hs.symm.trans getS)
  subst stream1 state1
  have actualUse : used = l.have_.toNat - regs.have_.toNat := by omega
  rw [actualUse] at nextPacket
  exact ⟨current, nextPacket⟩

#print axioms origin_packet_of_actual

theorem check_wait_body
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {bs credited : List UInt8}
    (E : Env c h r zs z s) (initial : DefaultOriginState h r zs z s)
    (allocator : DefAlloc z) (buffers : StreamBuffers h r) (nonnull : z.next_out ≠ .null)
    (input : BitInv h (dispatchRegs z s) bs) (mode : s.mode = CHECK)
    (short : s.bits.toNat + 8 * bs.length < 32) (credit : AdlerCredit z s credited) :
    ∃ rc after stream0 state,
      (do let (result, regs) ← runX (inflate_run c) IL.init
          match result with
          | .error (.ret value) => pure value
          | _ => inflate_leave c regs) h = .ok (rc, after) ∧
      DefaultOriginState after r zs stream0 state ∧ DefAlloc stream0 ∧ state.mode = CHECK ∧
      state.bits.toNat < 32 ∧ state.bits.toNat = s.bits.toNat + 8 * bs.length ∧
      natBits state.bits.toNat state.hold.toNat = natBits s.bits.toNat s.hold.toNat ++ bytesBits bs ∧
      stream0.next_in = inputAdvance z.next_in bs.length ∧ stream0.avail_in = 0 ∧
      stream0.next_out = z.next_out ∧ stream0.avail_out = z.avail_out ∧
      AdlerCredit stream0 state credited ∧ rc ≠ Z_MEM_ERROR := by
  have output := dispatchRegs_output E.hz buffers nonnull s
  obtain ⟨z0, get0, inputRange, outputRange, separate⟩ := buffers
  have sameZ : z0 = z := Option.some.inj (get0.symm.trans E.hz)
  subst z0
  have packet : DispatchBuffers h r (dispatchRegs z s) bs := ⟨inputRange, output, separate, input⟩
  obtain ⟨outcome, regs, used, pull, usedBound, inv, source, bitCount, shape,
    bitBound, identity, full, waiting, kinds, cursor⟩ := NEEDBITS_run_cursor input 32 (by decide)
  change regs.bits.toNat = s.bits.toNat + 8 * used at bitCount
  have error : outcome = .error Ex.leave := by
    rcases kinds with normal | waiting
    · have full := full normal
      change 32 ≤ regs.bits.toNat at full
      omega
    · exact waiting
  obtain ⟨all, zero, below⟩ := waiting error
  subst used
  rw [List.drop_length] at inv source
  have sourceWord : natBits regs.bits.toNat regs.hold.toNat =
      natBits s.bits.toNat s.hold.toNat ++ bytesBits bs := by
    simpa only [stream, dispatchRegs, bytesBits_nil, List.append_nil] using source
  have symbol : SymbolRegShape (dispatchRegs z s) regs := by rw [shape]; rfl
  have packet0 := packet.consume initial.good initial.good rfl (fun _ => rfl) (fun _ => rfl)
    symbol cursor usedBound (by simpa only [List.drop_length] using inv)
  rw [List.drop_length] at packet0
  have step := (inflate_dispatch_CHECK E _ mode).trans
    (CHECK_wait_cut E _ regs (by rw [credit.1]; decide) (by rwa [error] at pull))
  have loop := xwhile_run_chain (inflate_dispatch c) (fun _ => dispatchRegs z s) (fun _ => h)
    0 (by unfold fuel; decide) Ex.leave regs h (by intro j impossible; omega) step
  have noOutput : regs.out_ = regs.left := by rw [shape]; rfl
  have ret : PublicLeaveRet regs := by left; rw [shape]; rfl
  have bits : regs.bits.toNat ≤ 39 := by change regs.bits.toNat < 32 at below; omega
  obtain ⟨rc, after, stream0, state, leave, final, finalAlloc, held, bitfield, modefield⟩ :=
    inflate_leave_trailer_fields E initial allocator packet0 bits
  have notMemory : rc ≠ Z_MEM_ERROR := by
    intro same
    subst rc
    exact inflate_leave_zero_output_not_memory E initial.good allocator.1 initial.pending packet0 bits ret noOutput leave
  have finalMode : state.mode = CHECK := by
    rcases modefield with same | failure
    · exact same.trans mode
    · exact False.elim (notMemory failure.1)
  obtain ⟨rc1, after1, stream1, state1, ref, off, a, incoming, leave1, final1, alloc1,
    pointer, get, view, written, incomingLength, observed, put, leftCount, outcome1⟩ :=
    inflate_leave_adler_observed E initial.toDefaultStateJ allocator packet0 bits credit
  have same := Except.ok.inj (leave.symm.trans leave1)
  cases same
  have sameZ : stream1 = stream0 := Option.some.inj (final1.good.live.hz.symm.trans final.good.live.hz)
  have sameS : state1 = state := Option.some.inj (final1.good.live.hs.symm.trans final.good.live.hs)
  subst stream1 state1
  have incomingEmpty : incoming = [] := by
    apply List.length_eq_zero_iff.mp
    rw [incomingLength, noOutput, UInt32.sub_self]
    rfl
  have finalCredit : AdlerCredit stream0 state credited := by
    rcases outcome1 with ordinary | failure
    · simpa only [incomingEmpty, List.append_nil] using ordinary.2
    · exact False.elim (notMemory failure.1)
  obtain ⟨rc2, after2, stream2, state2, leave2, final2, alloc2, next, haveCount, put2, left2, account⟩ :=
    inflate_leave_default_public_accounting E initial.toDefaultStateJ allocator packet0 bits
  have same := Except.ok.inj (leave.symm.trans leave2)
  cases same
  have sameZ : stream2 = stream0 := Option.some.inj (final2.good.live.hz.symm.trans final.good.live.hz)
  subst stream2
  have entry : runX (inflate_run c) IL.init h =
      runX (xwhile (pure true) (inflate_dispatch c)) (dispatchRegs z s) h := by
    unfold inflate_run
    rw [runX_bind, runX_rdS E]
    have noType : s.mode ≠ TYPE := by rw [mode]; decide
    simp only [noType, beq_iff_eq, ite_false, runX_bind]
    rw [LOAD_run E]
    simp only []
    rw [runX_modify]
    rfl
  refine ⟨rc, after, stream0, state, ?_, final, finalAlloc, finalMode, ?_, ?_, ?_,
    next.trans cursor, haveCount.trans zero, ?_, ?_, finalCredit, notMemory⟩
  · rw [bind_app, entry, loop]
    exact leave
  · rw [bitfield]
    exact below
  · rw [bitfield]
    exact bitCount
  · rw [bitfield, held]
    exact sourceWord
  · rw [put2, shape]
    rfl
  · rw [left2, shape]
    rfl

#print axioms check_wait_body

theorem check_wait_public
    {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {bs credited : List UInt8} {flush : Int32}
    (initial : DefaultOriginState h r zs z s) (allocator : DefAlloc z)
    (buffers : StreamBuffers h r) (nonnull : z.next_out ≠ .null)
    (inputValid : z.next_in = .null → z.avail_in = 0)
    (inputBytes : Bytes h z.next_in z.avail_in.toNat bs) (mode : s.mode = CHECK)
    (short : s.bits.toNat + 8 * bs.length < 32) (credit : AdlerCredit z s credited) :
    ∃ rc after stream0 state,
      C.run (inflate (some r) flush) h = .ok (rc, after) ∧
      DefaultOriginState after r zs stream0 state ∧ DefAlloc stream0 ∧ state.mode = CHECK ∧
      state.bits.toNat < 32 ∧ state.bits.toNat = s.bits.toNat + 8 * bs.length ∧
      natBits state.bits.toNat state.hold.toNat = natBits s.bits.toNat s.hold.toNat ++ bytesBits bs ∧
      stream0.next_in = inputAdvance z.next_in bs.length ∧ stream0.avail_in = 0 ∧
      stream0.next_out = z.next_out ∧ stream0.avail_out = z.avail_out ∧
      AdlerCredit stream0 state credited ∧ rc ≠ Z_MEM_ERROR := by
  let c : Ctx := ⟨some r, some (.tab zs), syncBuf h, flush⟩
  have allocated := default_origin_syncAlloc initial
  have env : Env c (syncAlloc h) r zs z s :=
    ⟨rfl, rfl, allocated.good.live.hz, allocated.good.live.hs⟩
  have input := header_input_view_of_bytes (s := s) inputBytes initial.held
  have input0 : BitInv (syncAlloc h) (dispatchRegs z s) bs := by
    refine ⟨input.have_eq, ?_, input.hold_lt⟩
    rcases input.next with empty | ⟨ref, array, off, pointer, get, bound, values⟩
    · exact Or.inl empty
    · exact Or.inr ⟨ref, array, off, pointer,
        (byte_view_syncAlloc initial.good.fresh get).1, bound, values⟩
  obtain ⟨rc, bodyHeap, stream0, state, body, current, bodyAlloc, finalMode,
    below, bits, word, next, zero, put, left, finalCredit, notMemory⟩ :=
    check_wait_body env allocated allocator (streamBuffers_syncAlloc initial.good.fresh buffers)
      nonnull input0 mode short credit
  obtain ⟨otherStream, otherState, run, final, finalAllocator, freed, getZ, getS⟩ :=
    inflate_public_close_body initial.toDefaultStateJ allocator buffers nonnull inputValid body
  have sameZ : otherStream = stream0 := Option.some.inj (getZ.symm.trans current.good.live.hz)
  have sameS : otherState = state := Option.some.inj (getS.symm.trans current.good.live.hs)
  subst otherStream otherState
  exact ⟨rc, freeWin bodyHeap (syncBuf h), stream0, state, run, current.of_fields final rfl rfl rfl,
    finalAllocator, finalMode, below, bits, word, next, zero, put, left, finalCredit, notMemory⟩

#print axioms check_wait_public

theorem check_complete_body
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {bs credited : List UInt8} {future : List Bool}
    (E : Env c h r zs z s) (initial : DefaultOriginState h r zs z s)
    (allocator : DefAlloc z) (buffers : StreamBuffers h r) (nonnull : z.next_out ≠ .null)
    (input : BitInv h (dispatchRegs z s) bs) (mode : s.mode = CHECK)
    (aligned : s.bits.toNat % 8 = 0) (credit : AdlerCredit z s credited)
    (source : stream (dispatchRegs z s) bs = bytesBits (be32 (adler32 credited).toNat) ++ future) :
    ∃ after stream0 state,
      (do let (result, regs) ← runX (inflate_run c) IL.init
          match result with
          | .error (.ret value) => pure value
          | _ => inflate_leave c regs) h = .ok (Z_STREAM_END, after) ∧
      r.get after = some stream0 ∧ after.istates zs = some state ∧
      AdlerCredit stream0 state credited ∧ stream0.next_out = z.next_out ∧
      stream0.avail_out = z.avail_out := by
  have output := dispatchRegs_output E.hz buffers nonnull s
  obtain ⟨z0, get0, inputRange, outputRange, separate⟩ := buffers
  have sameZ : z0 = z := Option.some.inj (get0.symm.trans E.hz)
  subst z0
  have packet : DispatchBuffers h r (dispatchRegs z s) bs := ⟨inputRange, output, separate, input⟩
  obtain ⟨pulled, used, pull, usedBound, inv, bits32, next, outField, leftField, putField,
    trailer, remainder⟩ := wrapper_NEEDBITS_valid_be32 input initial.good.inv.bits aligned
      (adler32 credited) future source
  let regs := { pulled with out_ := (dispatchRegs z s).left, hold := 0, bits := 0, ret := Z_STREAM_END }
  let doneState := { s with mode := DONE }
  let doneHeap := setI h zs doneState
  have actual : runX (inflate_dispatch c) (dispatchRegs z s) h =
      .ok ((.error Ex.leave, regs), doneHeap) := by
    rw [inflate_dispatch_CHECK E _ mode]
    exact inflate_CHECK_zlib_zero_output_cut E credit.1 credit.2.1 rfl pull outField leftField
      (trailer.trans credit.2.2.1.symm)
  have getZ : r.get doneHeap = some z := by rw [ZStreamRef.get_setI]; exact E.hz
  have getS : doneHeap.istates zs = some doneState := by dsimp only [doneHeap]; rw [setI_istates_same]
  obtain ⟨current, packet0⟩ := origin_packet_of_actual E initial packet initial.good.inv.bits actual getZ getS
  have env0 : Env c doneHeap r zs z doneState := ⟨E.strm, E.st, getZ, getS⟩
  have doneCredit : AdlerCredit z doneState credited := adlerCredit_decode credit rfl
  have zeroOut : regs.out_ = regs.left := leftField.symm
  obtain ⟨after, stream0, state, leave, finalGetZ, finalGetS, finalCredit⟩ :=
    inflate_leave_after_CHECK_adler env0 current.good allocator.1 current.pending packet0
      (by change (0 : UInt32).toNat ≤ 39; decide) doneCredit zeroOut rfl
  obtain ⟨rc1, after1, stream1, state1, leave1, final1, alloc1,
    next1, have1, put1, left1, account⟩ :=
    inflate_leave_default_public_accounting env0 current.toDefaultStateJ allocator packet0
      (by change (0 : UInt32).toNat ≤ 39; decide)
  have same := Except.ok.inj (leave.symm.trans leave1)
  cases same
  have sameZ : stream1 = stream0 := Option.some.inj (final1.good.live.hz.symm.trans finalGetZ)
  subst stream1
  have loop := xwhile_run_chain (inflate_dispatch c) (fun _ => dispatchRegs z s) (fun _ => h)
    0 (by unfold fuel; decide) Ex.leave regs doneHeap (by intro j impossible; omega) actual
  have entry : runX (inflate_run c) IL.init h =
      runX (xwhile (pure true) (inflate_dispatch c)) (dispatchRegs z s) h := by
    unfold inflate_run
    rw [runX_bind, runX_rdS E]
    have noType : s.mode ≠ TYPE := by rw [mode]; decide
    simp only [noType, beq_iff_eq, ite_false, runX_bind]
    rw [LOAD_run E]
    simp only []
    rw [runX_modify]
    rfl
  refine ⟨after, stream0, state, ?_, finalGetZ, finalGetS, finalCredit, ?_, ?_⟩
  · rw [bind_app, entry, loop]
    exact leave
  · rw [put1, putField]
    rfl
  · rw [left1, leftField]
    rfl

#print axioms check_complete_body

theorem check_wait_dataStep
    {h after : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {flush rc : Int32} {input output credited : List UInt8} {used : Nat}
    (initial : DefaultOriginState h r zs z s) (allocator : DefAlloc z)
    (observed : DataStep .inflate h after r flush rc input output used)
    (mode : s.mode = CHECK) (short : s.bits.toNat + 8 * input.length < 32)
    (credit : AdlerCredit z s credited) :
    ∃ stream0 state, DefaultOriginState after r zs stream0 state ∧ DefAlloc stream0 ∧
      state.mode = CHECK ∧ used ≤ input.length ∧ output = [] ∧
      state.bits.toNat < 32 ∧ state.bits.toNat = s.bits.toNat + 8 * used ∧
      natBits state.bits.toNat state.hold.toNat =
        natBits s.bits.toNat s.hold.toNat ++ bytesBits (input.take used) ∧
      AdlerCredit stream0 state credited ∧ rc ≠ Z_MEM_ERROR := by
  obtain ⟨z0, z1, get0, get1, buffers, header, inputBytes, usedEq, outputBytes, actual⟩ := observed
  have sameZ : z0 = z := Option.some.inj (get0.symm.trans initial.good.live.hz)
  subst z0
  by_cases null : z.next_out = .null
  · have expected := inflate_default_null_output_run initial.toDefaultStateJ flush null
    have sameRun := Except.ok.inj (actual.symm.trans expected)
    cases sameRun
    have get : r.get (tmpFreed h) = some z := by
      simpa only [tmpFreed, ZStreamRef.get_freeWin, ZStreamRef.get_syncAlloc] using initial.good.live.hz
    have streamEq : z1 = z := Option.some.inj (get1.symm.trans get)
    subst z1
    have zero : used = 0 := by rw [usedEq]; omega
    clear usedEq
    subst used
    have length := header_observed_bytes_length outputBytes
    have empty : output = [] := by apply List.length_eq_zero_iff.mp; omega
    have allocated := default_origin_syncAlloc initial
    have final := allocated.free_local (syncAlloc_bytes_buf h) (by simp only [syncJunk, Array.size_ofFn])
    exact ⟨z, s, final, allocator, mode, by omega, empty, by omega,
      by simp only [Nat.mul_zero, Nat.add_zero], by simp only [List.take_zero, bytesBits_nil, List.append_nil],
      credit, by decide⟩
  · have inputValid : z.next_in = .null → z.avail_in = 0 := by
      intro nullIn
      rcases inputBytes with ⟨_, zero, _⟩ | ⟨ref, off, array, pointer, get, room, values⟩
      · exact UInt32.toNat_inj.mp zero
      · rw [nullIn] at pointer
        cases pointer
    obtain ⟨rc0, heap0, stream0, state, run, final, finalAllocator, finalMode,
      below, bits, word, next, zero, put, left, finalCredit, notMemory⟩ :=
      check_wait_public (flush := flush) initial allocator buffers null inputValid inputBytes mode short credit
    have sameRun : (rc0, heap0) = (rc, after) := Except.ok.inj (run.symm.trans actual)
    cases sameRun
    have streamEq : z1 = stream0 := Option.some.inj (get1.symm.trans final.good.live.hz)
    subst z1
    have inputLength := header_observed_bytes_length inputBytes
    have usedAll : used = input.length := by rw [zero] at usedEq; simp only [UInt32.toNat_zero, Nat.sub_zero] at usedEq; omega
    have outputLength := header_observed_bytes_length outputBytes
    have empty : output = [] := by rw [left] at outputLength; apply List.length_eq_zero_iff.mp; omega
    refine ⟨stream0, state, final, finalAllocator, finalMode, by omega, empty, below, ?_, ?_, finalCredit, notMemory⟩
    · rw [usedAll]
      exact bits
    · rw [usedAll, List.take_length]
      exact word

#print axioms check_wait_dataStep

theorem check_complete_public
    {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {bs credited : List UInt8} {future : List Bool} {flush : Int32}
    (initial : DefaultOriginState h r zs z s) (allocator : DefAlloc z)
    (buffers : StreamBuffers h r) (nonnull : z.next_out ≠ .null)
    (inputValid : z.next_in = .null → z.avail_in = 0)
    (inputBytes : Bytes h z.next_in z.avail_in.toNat bs) (mode : s.mode = CHECK)
    (aligned : s.bits.toNat % 8 = 0) (credit : AdlerCredit z s credited)
    (source : stream (dispatchRegs z s) bs = bytesBits (be32 (adler32 credited).toNat) ++ future) :
    ∃ after stream0 state,
      C.run (inflate (some r) flush) h = .ok (Z_STREAM_END, after) ∧
      DefaultStateJ after r zs stream0 state ∧ DefAlloc stream0 ∧ AdlerCredit stream0 state credited ∧
      stream0.next_out = z.next_out ∧ stream0.avail_out = z.avail_out ∧ after.bytes h.nextBlk = none := by
  let c : Ctx := ⟨some r, some (.tab zs), syncBuf h, flush⟩
  have allocated := default_origin_syncAlloc initial
  have env : Env c (syncAlloc h) r zs z s :=
    ⟨rfl, rfl, allocated.good.live.hz, allocated.good.live.hs⟩
  have input := header_input_view_of_bytes (s := s) inputBytes initial.held
  have input0 : BitInv (syncAlloc h) (dispatchRegs z s) bs := by
    refine ⟨input.have_eq, ?_, input.hold_lt⟩
    rcases input.next with empty | ⟨ref, array, off, pointer, get, bound, values⟩
    · exact Or.inl empty
    · exact Or.inr ⟨ref, array, off, pointer,
        (byte_view_syncAlloc initial.good.fresh get).1, bound, values⟩
  obtain ⟨bodyHeap, stream0, state, body, getZ, getS, finalCredit, put, left⟩ :=
    check_complete_body env allocated allocator (streamBuffers_syncAlloc initial.good.fresh buffers)
      nonnull input0 mode aligned credit source
  obtain ⟨run, final, finalAllocator, freed, finalCredit0⟩ :=
    inflate_public_close_body_adler initial.toDefaultStateJ allocator buffers nonnull inputValid
      body getZ getS finalCredit
  exact ⟨freeWin bodyHeap (syncBuf h), stream0, state, run, final, finalAllocator,
    finalCredit0, put, left, freed⟩

#print axioms check_complete_public

inductive CheckWaitingTrace (start : Heap) (r : ZStreamRef) (zs : Nat) :
    Heap → List UInt8 → List UInt8 → Prop where
  | begin : CheckWaitingTrace start r zs start [] []
  | caller {h after input output} : CheckWaitingTrace start r zs h input output →
      Rebuffer h after r → ZlibF.PlatformMemory.ByteObjectsFit after →
      CheckWaitingTrace start r zs after input output
  | step {h after priorInput priorOutput z s flush rc input output used} :
      CheckWaitingTrace start r zs h priorInput priorOutput →
      r.get h = some z → h.istates zs = some s → s.mode = CHECK →
      s.bits.toNat + 8 * input.length < 32 →
      DataStep .inflate h after r flush rc input output used →
      CheckWaitingTrace start r zs after (priorInput ++ input.take used) (priorOutput ++ output)


theorem CheckWaitingTrace.sound
    {start after : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {input output credited : List UInt8}
    (initial : DefaultOriginState start r zs z s) (allocator : DefAlloc z)
    (mode : s.mode = CHECK) (bits : s.bits = 0) (hold : s.hold = 0)
    (credit : AdlerCredit z s credited)
    (history : CheckWaitingTrace start r zs after input output) :
    ∃ stream0 state, DefaultOriginState after r zs stream0 state ∧ DefAlloc stream0 ∧
      state.mode = CHECK ∧ state.bits.toNat < 32 ∧ state.bits.toNat = 8 * input.length ∧
      natBits state.bits.toNat state.hold.toNat = bytesBits input ∧
      input.length ≤ 3 ∧ output = [] ∧ AdlerCredit stream0 state credited := by
  induction history with
  | begin =>
    refine ⟨z, s, initial, allocator, mode, ?_, ?_, ?_, by simp, rfl, credit⟩
    · rw [bits]; decide
    · rw [bits]; rfl
    · rw [bits, hold]; rfl
  | @caller before after inputs outputs prior edit platform ih =>
    obtain ⟨stream0, state, current, currentAllocator, currentMode, below, count, word,
      inputBound, empty, currentCredit⟩ := ih
    obtain ⟨stream1, next⟩ := rebuffer_default_origin current edit platform
    obtain ⟨otherStream, fields, good⟩ := rebuffer_inflate_good current.good edit
    have same : otherStream = stream1 := Option.some.inj (good.live.hz.symm.trans next.good.live.hz)
    subst otherStream
    have finalAllocator : DefAlloc stream1 := by rw [fields]; exact currentAllocator
    have nextCredit : AdlerCredit stream1 state credited := by
      refine ⟨currentCredit.1, currentCredit.2.1, currentCredit.2.2.1, ?_⟩
      rw [fields]
      exact currentCredit.2.2.2
    exact ⟨stream1, state, next, finalAllocator, currentMode, below, count, word,
      inputBound, empty, nextCredit⟩
  | @step before after inputs outputs callerStream callerState flush rc freshInput freshOutput used
      prior streamGet stateGet callerMode short actual ih =>
    obtain ⟨stream0, state, current, currentAllocator, currentMode, below, count, word,
      inputBound, empty, currentCredit⟩ := ih
    have sameZ : callerStream = stream0 := Option.some.inj (streamGet.symm.trans current.good.live.hz)
    have sameS : callerState = state := Option.some.inj (stateGet.symm.trans current.good.live.hs)
    subst callerStream callerState
    obtain ⟨stream1, state1, next, nextAllocator, nextMode, usedBound, outputEmpty,
      nextBelow, nextCount, nextWord, nextCredit, notMemory⟩ :=
      check_wait_dataStep current currentAllocator actual callerMode short currentCredit
    refine ⟨stream1, state1, next, nextAllocator, nextMode, nextBelow, ?_, ?_, ?_, ?_, nextCredit⟩
    · simp only [List.length_append, List.length_take, Nat.min_eq_left usedBound]
      omega
    · rw [nextWord, word, bytesBits_append]
    · simp only [List.length_append, List.length_take, Nat.min_eq_left usedBound]
      omega
    · rw [empty, outputEmpty]
      rfl

#print axioms CheckWaitingTrace.sound

theorem CheckWaitingTrace.complete_public
    {start h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {input output credited : List UInt8}
    (initial : DefaultOriginState start r zs z s) (allocator : DefAlloc z)
    (mode : s.mode = CHECK) (bits : s.bits = 0) (hold : s.hold = 0)
    (credit : AdlerCredit z s credited)
    (history : CheckWaitingTrace start r zs h input output) :
    ∃ stream0 state, DefaultOriginState h r zs stream0 state ∧ DefAlloc stream0 ∧ output = [] ∧
      ∀ bs tail flush, StreamBuffers h r → stream0.next_out ≠ .null →
        (stream0.next_in = .null → stream0.avail_in = 0) →
        Bytes h stream0.next_in stream0.avail_in.toNat bs →
        input ++ bs = be32 (adler32 credited).toNat ++ tail →
        ∃ after stream1 state1,
          C.run (inflate (some r) flush) h = .ok (Z_STREAM_END, after) ∧
          DefaultStateJ after r zs stream1 state1 ∧ DefAlloc stream1 ∧ AdlerCredit stream1 state1 credited ∧
          stream1.next_out = stream0.next_out ∧ stream1.avail_out = stream0.avail_out ∧
          after.bytes h.nextBlk = none := by
  obtain ⟨stream0, state, current, currentAlloc, currentMode, below, count, word, inputBound,
    empty, currentCredit⟩ := history.sound initial allocator mode bits hold credit
  refine ⟨stream0, state, current, currentAlloc, empty, ?_⟩
  intro bs tail flush buffers nonnull inputValid inputBytes packet
  have source : stream (dispatchRegs stream0 state) bs =
      bytesBits (be32 (adler32 credited).toNat) ++ bytesBits tail := by
    change natBits state.bits.toNat state.hold.toNat ++ bytesBits bs = _
    rw [word, ← bytesBits_append, packet, bytesBits_append]
  exact check_complete_public (flush := flush) current currentAlloc buffers nonnull inputValid
    inputBytes currentMode (by rw [count]; omega) currentCredit source

#print axioms CheckWaitingTrace.complete_public

theorem CheckWaitingTrace.original_trace
    {start after : Heap} {r : ZStreamRef} {zs : Nat} {base : DataLog} {input output : List UInt8}
    (original : InflateDataTrace 15 r start base)
    (history : CheckWaitingTrace start r zs after input output) :
    ∃ log, InflateDataTrace 15 r after log ∧ log.input = base.input ++ input ∧
      log.output = base.output ++ output ∧ log.dictionary = base.dictionary := by
  induction history with
  | begin => exact ⟨base, original, (List.append_nil _).symm, (List.append_nil _).symm, rfl⟩
  | caller prior edit platform ih =>
    obtain ⟨log, trace, inp, out, dict⟩ := ih
    exact ⟨log, trace.caller edit, inp, out, dict⟩
  | step prior streamGet stateGet mode short actual ih =>
    obtain ⟨log, trace, inp, out, dict⟩ := ih
    refine ⟨_, trace.step actual, ?_, ?_, dict⟩
    · simp only [inp, List.append_assoc]
    · simp only [out, List.append_assoc]

#print axioms CheckWaitingTrace.original_trace

theorem CheckWaitingTrace.seeded_sound
    {start after : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {input output credited prefixBytes : List UInt8}
    (initial : DefaultOriginState start r zs z s) (allocator : DefAlloc z)
    (mode : s.mode = CHECK) (bits : s.bits.toNat = 8 * prefixBytes.length)
    (hold : natBits s.bits.toNat s.hold.toNat = bytesBits prefixBytes) (prefixBound : prefixBytes.length < 4)
    (credit : AdlerCredit z s credited)
    (history : CheckWaitingTrace start r zs after input output) :
    ∃ stream0 state, DefaultOriginState after r zs stream0 state ∧ DefAlloc stream0 ∧
      state.mode = CHECK ∧ state.bits.toNat < 32 ∧ state.bits.toNat = 8 * (prefixBytes ++ input).length ∧
      natBits state.bits.toNat state.hold.toNat = bytesBits (prefixBytes ++ input) ∧
      (prefixBytes ++ input).length ≤ 3 ∧ output = [] ∧ AdlerCredit stream0 state credited := by
  induction history with
  | begin =>
    refine ⟨z, s, initial, allocator, mode, ?_, ?_, ?_, ?_, rfl, credit⟩
    · rw [bits]
      omega
    · simpa only [List.append_nil] using bits
    · simpa only [List.append_nil] using hold
    · simp only [List.append_nil]
      omega
  | @caller before after inputs outputs prior edit platform ih =>
    obtain ⟨stream0, state, current, currentAllocator, currentMode, below, count, word,
      inputBound, empty, currentCredit⟩ := ih
    obtain ⟨stream1, next⟩ := rebuffer_default_origin current edit platform
    obtain ⟨otherStream, fields, good⟩ := rebuffer_inflate_good current.good edit
    have same : otherStream = stream1 := Option.some.inj (good.live.hz.symm.trans next.good.live.hz)
    subst otherStream
    have finalAllocator : DefAlloc stream1 := by rw [fields]; exact currentAllocator
    have nextCredit : AdlerCredit stream1 state credited := by
      refine ⟨currentCredit.1, currentCredit.2.1, currentCredit.2.2.1, ?_⟩
      rw [fields]
      exact currentCredit.2.2.2
    exact ⟨stream1, state, next, finalAllocator, currentMode, below, count, word,
      inputBound, empty, nextCredit⟩
  | @step before after inputs outputs callerStream callerState flush rc freshInput freshOutput used
      prior streamGet stateGet callerMode short actual ih =>
    obtain ⟨stream0, state, current, currentAllocator, currentMode, below, count, word,
      inputBound, empty, currentCredit⟩ := ih
    have sameZ : callerStream = stream0 := Option.some.inj (streamGet.symm.trans current.good.live.hz)
    have sameS : callerState = state := Option.some.inj (stateGet.symm.trans current.good.live.hs)
    subst callerStream callerState
    obtain ⟨stream1, state1, next, nextAllocator, nextMode, usedBound, outputEmpty,
      nextBelow, nextCount, nextWord, nextCredit, notMemory⟩ :=
      check_wait_dataStep current currentAllocator actual callerMode short currentCredit
    refine ⟨stream1, state1, next, nextAllocator, nextMode, nextBelow, ?_, ?_, ?_, ?_, nextCredit⟩
    · simp only [List.length_append, List.length_take, Nat.min_eq_left usedBound] at count ⊢
      omega
    · rw [nextWord, word]
      simp only [bytesBits_append, List.append_assoc]
    · simp only [List.length_append, List.length_take, Nat.min_eq_left usedBound] at count ⊢
      omega
    · rw [empty, outputEmpty]
      rfl

#print axioms CheckWaitingTrace.seeded_sound

theorem check_complete_dataStep
    {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {bs credited : List UInt8} {future : List Bool} {flush : Int32}
    (initial : DefaultOriginState h r zs z s) (allocator : DefAlloc z)
    (buffers : StreamBuffers h r) (nonnull : z.next_out ≠ .null)
    (inputValid : z.next_in = .null → z.avail_in = 0)
    (inputBytes : Bytes h z.next_in z.avail_in.toNat bs) (mode : s.mode = CHECK)
    (aligned : s.bits.toNat % 8 = 0) (credit : AdlerCredit z s credited)
    (source : stream (dispatchRegs z s) bs = bytesBits (be32 (adler32 credited).toNat) ++ future) :
    ∃ after stream0 state used,
      DataStep .inflate h after r flush Z_STREAM_END bs [] used ∧
      DefaultStateJ after r zs stream0 state ∧ DefAlloc stream0 ∧ AdlerCredit stream0 state credited := by
  obtain ⟨after, stream0, state, actual, current, alloc, finalCredit, put, left, freed⟩ :=
    check_complete_public (flush := flush) initial allocator buffers nonnull inputValid inputBytes mode aligned credit source
  obtain ⟨stream1, state1, used, output, current1, alloc1, freed1, account, observed, frame⟩ :=
    public_actual_END_output initial.toDefaultStateJ allocator buffers actual
  have sameZ : stream1 = stream0 := Option.some.inj (current1.good.live.hz.symm.trans current.good.live.hz)
  have sameS : state1 = state := Option.some.inj (current1.good.live.hs.symm.trans current.good.live.hs)
  subst stream1 state1
  have empty : output = [] := by
    apply List.length_eq_zero_iff.mp
    have count := account.2.2.2.1
    rw [left] at count
    omega
  refine ⟨after, stream0, state, used, ?_, current, alloc, finalCredit⟩
  refine ⟨z, stream0, initial.good.live.hz, current.good.live.hz, buffers,
    initial.toDefaultStateJ.active_header, inputBytes, ?_, ?_, actual⟩
  · have count := account.2.2.1
    omega
  · rw [left]
    simpa only [empty, Nat.sub_self, List.length_nil] using observed

#print axioms check_complete_dataStep

/-- A generic payload-complete epoch with its source-derived Adler ledger
can wait through arbitrary actual trailer calls/rebuffers, then append the
real END DataStep to the original byte log. The independent valid trailer
is about log.output, rather than a caller-supplied final checksum value. -/
theorem CheckWaitingTrace.finish_original
    {start h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {base : DataLog} {received produced heldPrefix : List UInt8}
    (initial : DefaultOriginState start r zs z s) (allocator : DefAlloc z)
    (mode : s.mode = CHECK) (bits : s.bits.toNat = 8 * heldPrefix.length)
    (hold : natBits s.bits.toNat s.hold.toNat = bytesBits heldPrefix) (heldPrefixBound : heldPrefix.length < 4)
    (credit : AdlerCredit z s base.output)
    (original : InflateDataTrace 15 r start base)
    (history : CheckWaitingTrace start r zs h received produced) :
    ∃ stream0 state, DefaultOriginState h r zs stream0 state ∧ DefAlloc stream0 ∧ produced = [] ∧
      ∀ bs tail flush, StreamBuffers h r → stream0.next_out ≠ .null →
        (stream0.next_in = .null → stream0.avail_in = 0) →
        Bytes h stream0.next_in stream0.avail_in.toNat bs →
        heldPrefix ++ received ++ bs = be32 (adler32 base.output).toNat ++ tail →
        ∃ after finalZ finalS used log,
          DataStep .inflate h after r flush Z_STREAM_END bs [] used ∧
          InflateDataTrace 15 r after log ∧ DefaultStateJ after r zs finalZ finalS ∧ DefAlloc finalZ ∧
          AdlerCredit finalZ finalS base.output ∧ log.output = base.output ∧
          log.dictionary = base.dictionary ∧ log.result = Z_STREAM_END ∧ log.finished = true ∧
          log.input = base.input ++ received ++ bs.take used := by
  obtain ⟨currentZ, currentS, current, currentAlloc, currentMode, below, count, word,
    inputBound, empty, currentCredit⟩ :=
    history.seeded_sound initial allocator mode bits hold heldPrefixBound credit
  refine ⟨currentZ, currentS, current, currentAlloc, empty, ?_⟩
  intro bs tail flush buffers nonnull inputValid inputBytes wire
  have source : stream (dispatchRegs currentZ currentS) bs =
      bytesBits (be32 (adler32 base.output).toNat) ++ bytesBits tail := by
    change natBits currentS.bits.toNat currentS.hold.toNat ++ bytesBits bs = _
    rw [word, ← bytesBits_append, wire, bytesBits_append]
  obtain ⟨after, finalZ, finalS, used, step, final, finalAlloc, finalCredit⟩ :=
    check_complete_dataStep (flush := flush) current currentAlloc buffers nonnull inputValid inputBytes
      currentMode (by rw [count]; omega) currentCredit source
  obtain ⟨waitingLog, waitingTrace, inputEq, outputEq, dictionaryEq⟩ :=
    history.original_trace original
  refine ⟨after, finalZ, finalS, used, _, step, waitingTrace.step step,
    final, finalAlloc, finalCredit, ?_, dictionaryEq, rfl, ?_, ?_⟩
  · simpa only [outputEq, empty, List.append_nil]
  · simp only [beq_self_eq_true, Bool.or_true]
  · simp only [inputEq, List.append_assoc]

#print axioms CheckWaitingTrace.finish_original

end Zlib.Inflate.Proofs.FunctionalTrailerSplits
