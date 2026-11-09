import ZlibF.Proof.«deflate.c.borrow-stable-strategies»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-continuation-ready»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-body-input-ledger»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-caller-input-frame»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-buffer-frame-adjacent»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-body-composable»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-body-all-scalar-interval»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-body-physical»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-body-controls»
import ZlibF.Proof.«deflate.c.engine.loop-input-ledger»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols ZlibF.Math.DeflateEncoding
set_option autoImplicit false

/-- An actual complete slow-loop run retains the independent meaning of
all its emitted nonfinal blocks and the exact full caller byte slice on
the final heap. Refill extends accepted input consistently across slides.
Every signed flush scalar and every caller output capacity are admitted. The existing execution proofs
supply termination; this theorem propagates encoding through that same
actual run. The accepted logical prefix is exactly the old prefix followed by the consumed original caller bytes. Checksum meaning is retained for that same input. EOF settlement, the final block and wrappers follow the loop. -/
theorem default_foreign_slow_loop_run_block_prefix_input {h after : Heap} {r : ZStreamRef}
    {ds owner oo origin base offset : Nat} {z : ZStream} {d : DeflateState}
    {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig} {final : LoopS} {flush : Int32}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (positive : 0 < config.level.toInt) (pointer : z.next_out = .ref (.dstate_depth owner) oo)
    (memory : config.memory.toNat = 16384) (wrap : config.wrap = 1)
    (publish : PublishReady d) (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    {actualInput : List UInt8} (snapshot : Bytes h z.next_in z.avail_in.toNat actualInput)
    (checksum : z.adler = (ZlibF.Spec.adler32 (inputPrefix input (origin + fillEnd d))).toUInt64)
    (position : offset % 8 = d.bi_valid.toInt.toNat % 8)
    (run : cwhile forever (deflate_slow_body (some (.tab ds)) flush) {} h = .ok (final, after)) :
    ∃ used z' result extended nextOrigin base' ys before written remaining blockBits,
      StrategyBoundary after r ds z' result extended nextOrigin base' ys config ∧ EndFrontier after result ∧
      StreamBuffers after r ∧ StreamAccounting z z' used written.length ∧
      (∀ i, i < origin + fillEnd d → extended i = input i) ∧
      nextOrigin + fillEnd result = origin + fillEnd d + used ∧ base ≤ base' ∧
      PendingBits h d before ∧ Bytes after z.next_out written.length written ∧ PendingBits after result remaining ∧
      ZlibF.Spec.bytesToBits written ++ remaining = before ++ blockBits ∧
      BlockPrefix [] offset (inputPrefix input base) blockBits (inputPrefix extended base') ∧
      (offset + blockBits.length) % 8 = result.bi_valid.toInt.toNat % 8 ∧
      z'.adler = (ZlibF.Spec.adler32 (inputPrefix extended (nextOrigin + fillEnd result))).toUInt64 ∧
      inputPrefix extended (nextOrigin + fillEnd result) =
        inputPrefix input (origin + fillEnd d) ++ actualInput.take used := by
  obtain ⟨pb, buf, trees, _ledger, _balance⟩ := boundary.symbols
  let before := Zlib.Trees.Proofs.Out.outBits buf d
  have initialReady : PublishReady d := publish
  have pendingInitial : PendingBits h d before := pending_bits_base trees initialReady.2.1
  let startEnd := origin + fillEnd d
  let Inv : LoopS → Heap → Prop := fun st heap =>
    ∃ currentZ currentD currentInput currentOrigin currentBase ys accepted written encoded pending,
      StrategyBoundary heap r ds currentZ currentD currentInput currentOrigin currentBase ys config ∧
      EndFrontier heap currentD ∧ StreamBuffers heap r ∧ StreamAccounting z currentZ accepted written.length ∧
      currentOrigin + fillEnd currentD = startEnd + accepted ∧
      (∀ i, i < startEnd → currentInput i = input i) ∧ base ≤ currentBase ∧
      (currentZ.avail_in ≠ 0 → currentZ.next_in ≠ .null) ∧
      (st.ret = none → PublishReady currentD) ∧
      Bytes heap z.next_out written.length written ∧ PendingBits heap currentD pending ∧
      ZlibF.Spec.bytesToBits written ++ pending = before ++ encoded ∧
      BlockPrefix [] offset (inputPrefix input base) encoded (inputPrefix currentInput currentBase) ∧
      (offset + encoded.length) % 8 = currentD.bi_valid.toInt.toNat % 8 ∧
      currentZ.adler = (ZlibF.Spec.adler32 (inputPrefix currentInput (currentOrigin + fillEnd currentD))).toUInt64 ∧
      inputPrefix currentInput (currentOrigin + fillEnd currentD) =
        inputPrefix input startEnd ++ actualInput.take accepted ∧
      heap.libcErrorBorrow = h.libcErrorBorrow ∧
      Shape h heap ∧ BufferFrame h heap (fun b => StreamRoot r b ∨ DeflateOwned ds d b) [⟨z.next_out,written.length⟩]
  have step : ∀ st heap, Inv st heap → st.brk = false → st.ret = none →
      ∀ next middle, deflate_slow_body (some (.tab ds)) flush st heap = .ok (next, middle) → Inv next middle := by
    intro st heap inv _notBreak running next middle actual
    obtain ⟨currentZ, currentD, currentInput, currentOrigin, currentBase, ys, accepted, written, encoded, pending,
      state, endS, buffersS, accountS, endpointS, agreesS, baseS, validS, readyS,
      writtenS, pendingS, wireS, prefixS, positionS, checksumS, inputLedgerS, borrowS, shapeS, frameS⟩ := inv
    have pointerS : currentZ.next_out = .ref (.dstate_depth owner) (oo + written.length) := by
      rw [accountS.2.2.2.2.2.1, pointer]
      rfl
    have publishS := readyS running
    obtain ⟨used, produced, expected, other, nextZ, nextD, nextBase, nextYs, nextInput, nextOrigin,
      pendingBefore, emitted, remaining, blockBits, bodyRun, stateA, endA, buffersA, accountA,
      lengthA, agreesA, endpointA, baseA, _returnsA, continuesA, _lessA, _breakA, _reasonA,
      pendingB, bytesA, pendingA, wireA, prefixA, positionA⟩ :=
      default_foreign_slow_body_composable_prefix (offset := offset + encoded.length) state endS buffersS positive pointerS
        memory wrap publishS validS positionS flush st
    have pair := Prod.mk.inj (Except.ok.inj (bodyRun.symm.trans actual))
    rw [← pair.1, ← pair.2]
    have readyA := default_foreign_slow_body_run_ready_phase state endS buffersS positive pointerS memory wrap publishS validS
      bodyRun stateA.good.live.hs
    have checksumA := default_foreign_slow_body_run_logical_adler state endS buffersS positive pointerS memory wrap publishS validS
      checksumS bodyRun stateA accountA agreesA endpointA
    obtain ⟨copied, copiedBytes, _copiedLength, inputLedgerA⟩ := default_foreign_slow_body_run_input_ledger state endS buffersS
      positive pointerS memory wrap publishS validS bodyRun stateA accountA agreesA endpointA
    have initialBuffers := buffers
    obtain ⟨oldZ, oldGet, callerRange, _outputRange, separated⟩ := initialBuffers
    have oldEq : oldZ = z := Option.some.inj (oldGet.symm.trans boundary.good.live.hz)
    subst oldZ
    have separatedNow : Separate z.next_in z.avail_in.toNat z.next_out written.length := by
      simpa only [advance_zero] using separate_advance_right (used := 0) separated
        (by have outputCount := accountS.2.2.2.1; omega)
    have snapshotS : Bytes heap z.next_in z.avail_in.toNat actualInput :=
      foreign_caller_input_bytes_preserved boundary.good buffers pointer callerRange separatedNow (Nat.le_refl _)
        snapshot frameS borrowS
    have copiedAt : Bytes heap (advance z.next_in accepted) used copied := by
      rw [← accountS.2.2.2.2.1]
      exact copiedBytes
    have countBound : accepted + used ≤ z.avail_in.toNat := by
      have beforeCount := accountS.2.2.1
      have bodyCount := accountA.2.2.1
      omega
    have copiedEq := caller_bytes_advanced_slice snapshotS copiedAt countBound
    have inputLedger : inputPrefix nextInput (nextOrigin + fillEnd nextD) =
        inputPrefix input startEnd ++ actualInput.take (accepted + used) := by
      rw [inputLedgerA, inputLedgerS, List.append_assoc, copiedEq, ← List.take_add]
    obtain ⟨shapeA, _frameA, _liveA, _allocA, _nextA⟩ := default_foreign_slow_body_run_full_storage state endS buffersS
      positive pointerS memory wrap publishS validS bodyRun
    have owned := ConfigFrame.owned (ds := ds)
      (show ConfigFrame d currentD from state.configuration.trans boundary.configuration.symm)
    have frameA := default_foreign_slow_body_run_buffer_frame state endS buffersS positive pointerS memory wrap publishS validS bodyRun stateA.good.live.hz accountA
    rw [owned] at frameA
    have one : BufferFrame h heap (fun b => StreamRoot r b ∨ DeflateOwned ds d b)
        [⟨.ref (.dstate_depth owner) oo,written.length⟩] := by simpa only [pointer] using frameS
    have two : BufferFrame heap other (fun b => StreamRoot r b ∨ DeflateOwned ds d b)
        [⟨.ref (.dstate_depth owner) (oo+written.length),produced⟩] := by simpa only [pointerS] using frameA
    obtain ⟨foreign,getForeign,_⟩ := caller_foreign_output boundary.good buffers pointer
    have fullFrame := foreign_buffer_frame_adjacent one two shapeS shapeA boundary.good.uniq getForeign
      (caller_foreign_owner_outside boundary.good buffers pointer)
    have samePending : pendingBefore = pending :=
      (pending_bits_zero_value publishS.1 pendingB).trans (pending_bits_zero_value publishS.1 pendingS).symm
    have effect := default_foreign_slow_body_run_output_interval state endS buffersS positive pointerS memory wrap publishS validS
      bodyRun stateA.good.live.hz accountA
    have oldBytes : Bytes other z.next_out written.length written := by
      rw [pointer] at writtenS ⊢
      exact effect.keep_published_bytes writtenS
    have newBytes : Bytes other (.ref (.dstate_depth owner) (oo + written.length)) produced emitted := by
      rw [pointerS] at bytesA
      exact bytesA
    have combinedBytes := generic_published_bytes_append (by simpa only [pointer] using oldBytes) newBytes
    have inputA : ∀ i, i < startEnd → nextInput i = input i := by
      intro i hi
      have inside : i < currentOrigin + fillEnd currentD := by omega
      exact (agreesA i inside).trans (agreesS i hi)
    have account : StreamAccounting z nextZ (accepted + used) (written ++ emitted).length := by
      simpa only [List.length_append, lengthA] using stream_accounting_trans accountS accountA
    have wire : ZlibF.Spec.bytesToBits (written ++ emitted) ++ remaining = before ++ (encoded ++ blockBits) := by
      rw [samePending] at wireA
      simp only [ZlibF.Spec.bytesToBits, List.flatMap_append, List.append_assoc] at wireS wireA ⊢
      rw [wireA, ← List.append_assoc, wireS, List.append_assoc]
    have combinedPrefix := block_prefix_append prefixS prefixA
    have nextPosition : (offset + (encoded ++ blockBits).length) % 8 = nextD.bi_valid.toInt.toNat % 8 := by
      simpa only [List.length_append, Nat.add_assoc] using positionA
    exact ⟨nextZ, nextD, nextInput, nextOrigin, nextBase, nextYs, accepted + used,
      written ++ emitted, encoded ++ blockBits, remaining, stateA, endA, buffersA,
      account, by omega, inputA, Nat.le_trans baseS baseA, input_valid_accounting_output validS accountA,
      readyA, by simpa only [List.length_append, lengthA, pointer] using combinedBytes,
      pendingA, wire, combinedPrefix, nextPosition, checksumA, inputLedger,
      (Zlib.Deflate.BorrowProofs.stable_deflate_slow_body _ _ _ _ _ _ bodyRun).trans borrowS,
      shapeS.trans shapeA,
      by simpa only [List.length_append,lengthA,pointer] using fullFrame⟩
  have initialBytes : Bytes h z.next_out 0 [] := by
    obtain ⟨foreign,get,bound,_⟩ := caller_foreign_output boundary.good buffers pointer
    exact Or.inr ⟨.dstate_depth owner,oo,foreign.depth,pointer,BRef.get_dstate_depth get,by omega,by simp⟩
  have initialFrame : BufferFrame h h (fun b => StreamRoot r b ∨ DeflateOwned ds d b) [⟨z.next_out,0⟩] := by
    obtain ⟨foreign,get,_⟩ := caller_foreign_output boundary.good buffers pointer
    rw [pointer]
    exact foreign_buffer_frame_of_fields (full_storage_refl h _).2.1 (Shape.refl h) boundary.good.uniq get
      (ForeignOwnerFields.refl h owner) rfl (ByteOutputInterval.of_same rfl)
  have initial : Inv {} h :=
    ⟨z, d, input, origin, base, xs, 0, [], [], before, boundary, frontier, buffers,
      stream_accounting_zero z, by simp [startEnd], fun _ _ => rfl, Nat.le_refl _, inputValid,
      fun _ => publish, initialBytes, pendingInitial, by simp [ZlibF.Spec.bytesToBits], block_prefix_empty _ _ _, by simpa using position, checksum, by simp [startEnd], rfl, Shape.refl h,
      initialFrame⟩
  have post := forever_run_invariant Inv (deflate_slow_body (some (.tab ds)) flush) step initial run
  obtain ⟨z', result, extended, nextOrigin, base', ys, used, written, encoded, pending,
    stateA, endA, buffersA, accountA, endpointA, agreesA, baseA, _validA, _outputA,
    bytesA, pendingA, wireA, prefixA, positionA, checksumA, inputLedgerA, _borrowA, _shapeA, _frameA⟩ := post
  exact ⟨used, z', result, extended, nextOrigin, base', ys, before, written, pending, encoded,
    stateA, endA, buffersA, accountA, agreesA, endpointA, baseA, pendingInitial,
    bytesA, pendingA, wireA, prefixA, positionA, checksumA, inputLedgerA⟩


end Zlib.Deflate.Engine.Proofs
