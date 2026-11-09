import ZlibF.Proof.«deflate.c.engine.generic-foreign-continuation-ready»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-body-logical-checksum»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-body-all-scalar-interval»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-body-composable»
import ZlibF.Proof.«deflate.c.engine.generic-output-append»
import ZlibF.Proof.«deflate.c.engine.loop-encoding-checksum»

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols ZlibF.Math.DeflateEncoding
set_option autoImplicit false

/-- The same actual all-scalar loop accumulates independent block-prefix meaning,
final-heap caller bytes and logical Adler for one shared returned input. Initial
checksum meaning is explicit; zero caller output is admitted through actual readiness.
This is a refinement of the supplied actual loop run, not a termination assumption
used to construct a public history. EOF and wrapper publication remain separate. -/
theorem default_foreign_slow_loop_run_logical_adler {h after : Heap} {r : ZStreamRef}
    {ds owner oo origin base offset : Nat} {z : ZStream} {d : DeflateState}
    {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig} {final : LoopS} {flush : Int32}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (positive : 0 < config.level.toInt) (pointer : z.next_out = .ref (.dstate_depth owner) oo)
    (memory : config.memory.toNat = 16384) (wrap : config.wrap = 1)
    (publish : PublishReady d) (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
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
      z'.adler = (ZlibF.Spec.adler32 (inputPrefix extended (nextOrigin + fillEnd result))).toUInt64 := by
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
      currentZ.adler = (ZlibF.Spec.adler32 (inputPrefix currentInput (currentOrigin + fillEnd currentD))).toUInt64
  have step : ∀ st heap, Inv st heap → st.brk = false → st.ret = none →
      ∀ next middle, deflate_slow_body (some (.tab ds)) flush st heap = .ok (next, middle) → Inv next middle := by
    intro st heap inv _notBreak running next middle actual
    obtain ⟨currentZ, currentD, currentInput, currentOrigin, currentBase, ys, accepted, written, encoded, pending,
      state, endS, buffersS, accountS, endpointS, agreesS, baseS, validS, readyS,
      writtenS, pendingS, wireS, prefixS, positionS, checksumS⟩ := inv
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
      pendingA, wire, combinedPrefix, nextPosition, checksumA⟩
  have initialBytes : Bytes h z.next_out 0 [] := caller_empty_output_view boundary.good.live.hz buffers pointer
  have initial : Inv {} h :=
    ⟨z, d, input, origin, base, xs, 0, [], [], before, boundary, frontier, buffers,
      stream_accounting_zero z, by simp [startEnd], fun _ _ => rfl, Nat.le_refl _, inputValid,
      fun _ => publish, initialBytes, pendingInitial, by simp [ZlibF.Spec.bytesToBits], block_prefix_empty _ _ _, by simpa using position, checksum⟩
  have post := forever_run_invariant Inv (deflate_slow_body (some (.tab ds)) flush) step initial run
  obtain ⟨z', result, extended, nextOrigin, base', ys, used, written, encoded, pending,
    stateA, endA, buffersA, accountA, endpointA, agreesA, baseA, _validA, _outputA,
    bytesA, pendingA, wireA, prefixA, positionA, checksumA⟩ := post
  exact ⟨used, z', result, extended, nextOrigin, base', ys, before, written, pending, encoded,
    stateA, endA, buffersA, accountA, agreesA, endpointA, baseA, pendingInitial,
    bytesA, pendingA, wireA, prefixA, positionA, checksumA⟩


end Zlib.Deflate.Engine.Proofs
