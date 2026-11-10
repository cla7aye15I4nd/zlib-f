import ZlibF.Proof.«inflate.c.cumulative-parser-history»
import ZlibF.Proof.«inflate.c.default-public-output-bytes»

namespace Zlib.Inflate.Proofs.ParserRefusal
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.CumulativeParser
set_option autoImplicit false

/-- Actual entry refusal allocates and frees the local declaration, while
retaining the complete decoder and stream records, for every flush value. -/
theorem entry_refused_origin {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (initial : DefaultOriginState h r zs z s) (flush : Int32)
    (refused : (z.next_out == .null || (z.next_in == .null && z.avail_in != 0)) = true) :
    C.run (inflate (some r) flush) h = .ok (Z_STREAM_ERROR, tmpFreed h) ∧
      DefaultOriginState (tmpFreed h) r zs z s := by
  have allocated := default_origin_syncAlloc initial
  have final := allocated.free_local (syncAlloc_bytes_buf h) (by simp only [syncJunk, Array.size_ofFn])
  refine ⟨?_, final⟩
  by_cases null : z.next_out = .null
  · exact inflate_default_null_output_run initial.toDefaultStateJ flush null
  · unfold C.run inflate
    rw [bind_app, allocLocalB_run h initial.good.fresh]
    simp only []
    rw [bind_app]
    simp only [bind_app, stateCheck_live allocated.good.live, bne_self_eq_false, Bool.false_eq_true, ite_false,
      ldZStream_ok allocated.good.live.hz, refused, ite_true, pure_app]
    dsimp only [syncBuf]
    rw [freeBuf_run (syncAlloc_bytes_buf h) (syncAlloc_ro_buf h)]
    rfl

/-- Original DataStep observation of refusal is an actual zero-byte
parser stutter. Heap allocation bookkeeping may advance; private fields do not. -/
theorem dataStep_refused_stutter
    {h after : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {flush rc : Int32} {input output : List UInt8} {used : Nat}
    (initial : DefaultOriginState h r zs z s)
    (observed : DataStep .inflate h after r flush rc input output used)
    (refused : (z.next_out == .null || (z.next_in == .null && z.avail_in != 0)) = true) :
    after = tmpFreed h ∧ rc = Z_STREAM_ERROR ∧ DefaultOriginState after r zs z s ∧ used = 0 ∧ output = [] := by
  obtain ⟨expected, final⟩ := entry_refused_origin initial flush refused
  obtain ⟨z0, returned, get0, get1, _buffers, _header, _input, count, outputBytes, actual⟩ := observed
  have sameZ : z0 = z := Option.some.inj (get0.symm.trans initial.good.live.hz)
  subst z0
  have same : (rc, after) = (Z_STREAM_ERROR, tmpFreed h) := Except.ok.inj (actual.symm.trans expected)
  cases same
  have sameStream : returned = z := Option.some.inj (get1.symm.trans final.good.live.hz)
  subst returned
  have empty : output = [] := by
    have length := header_observed_bytes_length outputBytes
    rw [Nat.sub_self] at length
    exact List.length_eq_zero_iff.mp length
  exact ⟨rfl, rfl, final, by rw [count, Nat.sub_self], empty⟩

/-- Accepted actual waiting segments and refused original DataSteps may
alternate freely. Neither constructor assumes parser postconditions. -/
inductive CodeLensWaitingWithRefusals (start : Heap) (r : ZStreamRef) (zs : Nat) : Heap → List UInt8 → List UInt8 → Prop where
  | begin : CodeLensWaitingWithRefusals start r zs start [] []
  | chunk {h after input output nextInput nextOutput} :
      CodeLensWaitingWithRefusals start r zs h input output →
      CodeLensWaitingTrace h r zs after nextInput nextOutput →
      CodeLensWaitingWithRefusals start r zs after (input ++ nextInput) (output ++ nextOutput)
  | refused {h after priorInput priorOutput z flush rc input output used} :
      CodeLensWaitingWithRefusals start r zs h priorInput priorOutput → r.get h = some z →
      (z.next_out == .null || (z.next_in == .null && z.avail_in != 0)) = true →
      DataStep .inflate h after r flush rc input output used →
      CodeLensWaitingWithRefusals start r zs after (priorInput ++ input.take used) (priorOutput ++ output)

theorem CodeLensWaitingWithRefusals.sound
    {start after : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {input output : List UInt8} {alphabet before : List Nat} {received : List Bool}
    (initial : DefaultOriginState start r zs z s) (allocator : DefAlloc z)
    (mode : s.mode = CODELENS) (window : s.wsize = 0)
    (contents : Zlib.Inftrees.Proofs.CodeLengthContents s.codes 0 s.lenbits.toNat alphabet)
    (ordinary : ∀ index, index < 2 ^ s.lenbits.toNat → ∃ entry, s.codes[index]? = some entry ∧ entry.op = 0)
    (progress : Progress alphabet (s.nlen.toNat + s.ndist.toNat) before received s)
    (history : CodeLensWaitingWithRefusals start r zs after input output) :
    ∃ stream0 state, DefaultOriginState after r zs stream0 state ∧ DefAlloc stream0 ∧ output = [] ∧
      state.mode = CODELENS ∧ state.wsize = 0 ∧ state.ncode = s.ncode ∧ state.nlen = s.nlen ∧ state.ndist = s.ndist ∧
      state.codes = s.codes ∧ state.lenbits = s.lenbits ∧
      Progress alphabet (s.nlen.toNat + s.ndist.toNat) before (received ++ bytesBits input) state := by
  induction history with
  | begin =>
    exact ⟨z, s, initial, allocator, rfl, mode, window, rfl, rfl, rfl, rfl, rfl,
      by simpa only [bytesBits, List.flatMap_nil, List.append_nil] using progress⟩
  | @chunk heap next inputs outputs nextInput nextOutput prior chunk ih =>
    obtain ⟨stream0, state, current, currentAllocator, empty, currentMode, currentWindow, code, lit, dist, codes, root, trace⟩ := ih
    have currentContents : Zlib.Inftrees.Proofs.CodeLengthContents state.codes 0 state.lenbits.toNat alphabet := by rw [codes, root]; exact contents
    have currentOrdinary : ∀ index, index < 2 ^ state.lenbits.toNat → ∃ entry, state.codes[index]? = some entry ∧ entry.op = 0 := by rw [codes, root]; exact ordinary
    rw [← lit, ← dist] at trace
    obtain ⟨nextStream, nextState, nextOrigin, nextAllocator, noOutput, nextMode, nextWindow, nextCode, nextLit, nextDist, nextCodes, nextRoot, nextTrace⟩ :=
      chunk.sound current currentAllocator currentMode currentWindow currentContents currentOrdinary trace
    rw [lit, dist] at nextTrace
    refine ⟨nextStream, nextState, nextOrigin, nextAllocator, ?_, nextMode, nextWindow,
      nextCode.trans code, nextLit.trans lit, nextDist.trans dist, nextCodes.trans codes, nextRoot.trans root, ?_⟩
    · rw [empty, noOutput]; rfl
    · simpa only [bytesBits_append, List.append_assoc] using nextTrace
  | @refused heap next inputs outputs callerStream flush rc freshInput freshOutput used prior streamGet rejected actual ih =>
    obtain ⟨stream0, state, current, currentAllocator, empty, currentMode, currentWindow, code, lit, dist, codes, root, trace⟩ := ih
    have same : callerStream = stream0 := Option.some.inj (streamGet.symm.trans current.good.live.hz)
    subst callerStream
    obtain ⟨_heapEq, _rcEq, next, zero, noOutput⟩ := dataStep_refused_stutter current actual rejected
    refine ⟨stream0, state, next, currentAllocator, ?_, currentMode, currentWindow, code, lit, dist, codes, root, ?_⟩
    · rw [empty, noOutput]; rfl
    · simpa only [zero, List.take_zero, List.append_nil] using trace

#print axioms entry_refused_origin
#print axioms dataStep_refused_stutter
#print axioms CodeLensWaitingWithRefusals.sound
theorem CodeLensWaitingWithRefusals.complete_payload
    {start after : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {input output : List UInt8} {alphabet before : List Nat} {received : List Bool}
    (initial : DefaultOriginState start r zs z s) (allocator : DefAlloc z)
    (mode : s.mode = CODELENS) (window : s.wsize = 0)
    (contents : Zlib.Inftrees.Proofs.CodeLengthContents s.codes 0 s.lenbits.toNat alphabet)
    (ordinary : ∀ index, index < 2 ^ s.lenbits.toNat → ∃ entry, s.codes[index]? = some entry ∧ entry.op = 0)
    (progress : Progress alphabet (s.nlen.toNat + s.ndist.toNat) before received s)
    (history : CodeLensWaitingWithRefusals start r zs after input output) :
    ∃ stream0 state, DefaultOriginState after r zs stream0 state ∧ DefAlloc stream0 ∧ output = [] ∧
      state.ncode = s.ncode ∧ state.nlen = s.nlen ∧ state.ndist = s.ndist ∧
      ∀ (c : Ctx) (bs : List UInt8) (rest : List Bool) (decoded : List Nat),
        c.strm = some r → c.st = some (.tab zs) → Bytes after stream0.next_in stream0.avail_in.toNat bs →
        CodeLens alphabet (s.nlen.toNat + s.ndist.toNat) before ((received ++ bytesBits input) ++ bytesBits bs) rest decoded →
        HasEndOfBlock (decoded.take s.nlen.toNat) → Acceptable .litLen (decoded.take s.nlen.toNat) →
        Acceptable .dist (decoded.drop s.nlen.toNat) →
        ∃ (regs : IL) (used : Nat) (finalState : InflateState) (offset tableUsed : Nat),
          used ≤ bs.length ∧ stream regs (bs.drop used) = rest ∧
          BitInv (setI after zs finalState) { regs with ret := 0 } (bs.drop used) ∧
          finalState.mode = LEN_ ∧ offset ≤ 852 ∧ tableUsed ≤ 592 ∧
          finalState.lencode = .ref (.istate_codes zs) 0 ∧ finalState.distcode = .ref (.istate_codes zs) offset ∧
          finalState.next = .ref (.istate_codes zs) (offset + tableUsed) ∧
          Zlib.Inftrees.Spec.DecodeTableInvariant.Inv LENS finalState.codes 0 finalState.lenbits.toNat offset (decoded.take s.nlen.toNat) ∧
          Zlib.Inftrees.Spec.DecodeTableInvariant.Inv DISTS finalState.codes offset finalState.distbits.toNat tableUsed (decoded.drop s.nlen.toNat) ∧
          runX (inflate_CODELENS c) (dispatchRegs stream0 state) after =
            if c.flush = Z_TREES then .ok ((.error Ex.leave, { regs with ret := 0 }), setI after zs finalState)
            else runX (inflate_LEN_ c) { regs with ret := 0 } (setI after zs finalState) := by
  obtain ⟨stream0, state, current, currentAllocator, empty, currentMode, _window, code, lit, dist, codes, root, trace⟩ :=
    history.sound initial allocator mode window contents ordinary progress
  refine ⟨stream0, state, current, currentAllocator, empty, code, lit, dist, ?_⟩
  intro c bs rest decoded hr hc bytes valid eob validL validD
  have pending := trace.pending (z := stream0) valid
  rw [← lit, ← dist] at pending
  have currentContents : Zlib.Inftrees.Proofs.CodeLengthContents state.codes 0 state.lenbits.toNat alphabet := by rw [codes, root]; exact contents
  have view := header_input_view_of_bytes (s := state) bytes current.held
  have currentEob : HasEndOfBlock (decoded.take state.nlen.toNat) := by rw [lit]; exact eob
  have currentL : Acceptable .litLen (decoded.take state.nlen.toNat) := by rw [lit]; exact validL
  have currentD : Acceptable .dist (decoded.drop state.nlen.toNat) := by rw [lit]; exact validD
  obtain ⟨regs, used, finalState, offset, tableUsed, bound, _cursor, _budget, source, _shape,
    inv, finalMode, roomL, roomD, lenPtr, distPtr, next, lenMeaning, distMeaning, actual⟩ :=
    CodeLensPayload.inflate_CODELENS_format_complete hr hc current.good.live.hz current.good.live.hs
      current.good.inv.wf currentMode current.lengths currentContents view pending currentEob currentL currentD
  rw [lit] at lenMeaning distMeaning
  exact ⟨regs, used, finalState, offset, tableUsed, bound, source, inv, finalMode, roomL, roomD, lenPtr, distPtr, next, lenMeaning, distMeaning, actual⟩


#print axioms CodeLensWaitingWithRefusals.complete_payload
end Zlib.Inflate.Proofs.ParserRefusal
