import ZlibF.Proof.«deflate.c.engine.loop-prefix»
import ZlibF.Proof.«deflate.c.engine.body-ready-phase»

/-! # Complete actual loop encoding at zero and positive caller capacity -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols ZlibF.Math.DeflateEncoding
set_option autoImplicit false

/-- An actual complete slow-loop run retains the independent meaning of
all its emitted nonfinal blocks and the exact full caller byte slice on
the final heap. Refill extends accepted input consistently across slides.
Every signed flush scalar and every caller output capacity are admitted. The existing execution proofs
supply termination; this theorem propagates encoding through that same
actual run. EOF settlement, the final block and wrappers follow the loop. -/
theorem slow_loop_ready_run_block_prefix {h after : Heap} {r : ZStreamRef}
    {ds ob oo origin base offset : Nat} {z : ZStream} {d : DeflateState}
    {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig} {final : LoopS} {flush : Int32}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (positive : 0 < config.level.toInt) (pointer : z.next_out = .ref (.blk ob) oo)
    (memory : config.memory.toNat = 16384) (wrap : config.wrap = 1)
    (publish : PublishReady d) (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
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
      (offset + blockBits.length) % 8 = result.bi_valid.toInt.toNat % 8 := by
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
      (offset + encoded.length) % 8 = currentD.bi_valid.toInt.toNat % 8
  have step : ∀ st heap, Inv st heap → st.brk = false → st.ret = none →
      ∀ next middle, deflate_slow_body (some (.tab ds)) flush st heap = .ok (next, middle) → Inv next middle := by
    intro st heap inv _notBreak running next middle actual
    obtain ⟨currentZ, currentD, currentInput, currentOrigin, currentBase, ys, accepted, written, encoded, pending,
      state, endS, buffersS, accountS, endpointS, agreesS, baseS, validS, readyS,
      writtenS, pendingS, wireS, prefixS, positionS⟩ := inv
    have pointerS : currentZ.next_out = .ref (.blk ob) (oo + written.length) := by
      rw [accountS.2.2.2.2.2.1, pointer]
      rfl
    have publishS := readyS running
    obtain ⟨used, produced, expected, other, nextZ, nextD, nextBase, nextYs, nextInput, nextOrigin,
      pendingBefore, emitted, remaining, blockBits, bodyRun, stateA, endA, buffersA, accountA,
      lengthA, agreesA, endpointA, baseA, _returnsA, continuesA, _lessA, _breakA, _reasonA,
      pendingB, bytesA, pendingA, wireA, prefixA, positionA⟩ :=
      slow_body_composable_prefix (offset := offset + encoded.length) state endS buffersS positive pointerS
        memory wrap publishS validS positionS flush st
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj (bodyRun.symm.trans actual))
    have readyA := slow_body_run_ready_phase state endS buffersS positive pointerS memory wrap publishS validS
      actual stateA.good.live.hs
    have samePending : pendingBefore = pending :=
      (pending_bits_zero_value publishS.1 pendingB).trans (pending_bits_zero_value publishS.1 pendingS).symm
    have effect := slow_body_all_scalar_run_output_effect state endS buffersS positive pointerS memory wrap publishS validS
      actual stateA.good.live.hz accountA
    have oldBytes : Bytes other z.next_out written.length written := by
      rw [pointer] at writtenS ⊢
      exact effect.keep_published_bytes writtenS
    have newBytes : Bytes other (.ref (.blk ob) (oo + written.length)) produced emitted := by
      rw [pointerS] at bytesA
      exact bytesA
    have combinedBytes := published_bytes_append (by simpa only [pointer] using oldBytes) newBytes
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
      pendingA, wire, combinedPrefix, nextPosition⟩
  have initialBytes : Bytes h z.next_out 0 [] := by
    obtain ⟨array, get, _writable, bound, _owned⟩ := caller_raw_output boundary.good buffers pointer
    exact Or.inr ⟨.blk ob, oo, array, pointer, get, by omega, by simp⟩
  have initial : Inv {} h :=
    ⟨z, d, input, origin, base, xs, 0, [], [], before, boundary, frontier, buffers,
      stream_accounting_zero z, by simp [startEnd], fun _ _ => rfl, Nat.le_refl _, inputValid,
      fun _ => publish, initialBytes, pendingInitial, by simp [ZlibF.Spec.bytesToBits], block_prefix_empty _ _ _, by simpa using position⟩
  have post := forever_run_invariant Inv (deflate_slow_body (some (.tab ds)) flush) step initial run
  obtain ⟨z', result, extended, nextOrigin, base', ys, used, written, encoded, pending,
    stateA, endA, buffersA, accountA, endpointA, agreesA, baseA, _validA, _outputA,
    bytesA, pendingA, wireA, prefixA, positionA⟩ := post
  exact ⟨used, z', result, extended, nextOrigin, base', ys, before, written, pending, encoded,
    stateA, endA, buffersA, accountA, agreesA, endpointA, baseA, pendingInitial,
    bytesA, pendingA, wireA, prefixA, positionA⟩

/-- The complete actual loop terminates and returns its accumulated encoded
prefix and final-heap caller bytes. Termination comes from the existing
proved NO_FLUSH and nonzero-scalar executions, not a successful-run premise.
Publication readiness replaces a positive output premise. EOF/final-block/wrapper composition follows separately. -/
theorem slow_loop_ready_block_prefix {h : Heap} {r : ZStreamRef}
    {ds ob oo origin base offset : Nat} {z : ZStream} {d : DeflateState}
    {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig} {flush : Int32}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (positive : 0 < config.level.toInt) (pointer : z.next_out = .ref (.blk ob) oo)
    (memory : config.memory.toNat = 16384) (wrap : config.wrap = 1)
    (publish : PublishReady d) (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (position : offset % 8 = d.bi_valid.toInt.toNat % 8) :
    ∃ final after used z' result extended nextOrigin base' ys before written remaining blockBits,
      cwhile forever (deflate_slow_body (some (.tab ds)) flush) {} h = .ok (final, after) ∧
      StrategyBoundary after r ds z' result extended nextOrigin base' ys config ∧ EndFrontier after result ∧
      StreamBuffers after r ∧ StreamAccounting z z' used written.length ∧
      (∀ i, i < origin + fillEnd d → extended i = input i) ∧
      nextOrigin + fillEnd result = origin + fillEnd d + used ∧ base ≤ base' ∧
      PendingBits h d before ∧ Bytes after z.next_out written.length written ∧ PendingBits after result remaining ∧
      ZlibF.Spec.bytesToBits written ++ remaining = before ++ blockBits ∧
      BlockPrefix [] offset (inputPrefix input base) blockBits (inputPrefix extended base') ∧
      (offset + blockBits.length) % 8 = result.bi_valid.toInt.toNat % 8 := by
  have terminates : ∃ final after,
      cwhile forever (deflate_slow_body (some (.tab ds)) flush) {} h = .ok (final, after) := by
    by_cases waiting : flush = Z_NO_FLUSH
    · subst flush
      obtain ⟨_used, _produced, _after, _z, _d, _base, _symbols, _input, _origin, safe, _rest⟩ :=
        deflate_slow_no_flush_ready boundary frontier buffers positive pointer memory wrap
          publish inputValid
      cases loop : cwhile forever (deflate_slow_body (some (.tab ds)) Z_NO_FLUSH) {} h with
      | error fault =>
        unfold deflate_slow at safe
        rw [bind_app, loop] at safe
        cases safe
      | ok pair => exact ⟨pair.1, pair.2, rfl⟩
    · obtain ⟨_used, _produced, final, after, _z, _d, _base, _symbols, _input, _origin, run, _rest⟩ :=
        slow_positive_ready_loop boundary frontier buffers positive pointer memory wrap
          publish inputValid flush waiting
      exact ⟨final, after, run⟩
  obtain ⟨final, after, run⟩ := terminates
  obtain ⟨used, z', result, extended, nextOrigin, base', ys, before, written, remaining, blockBits, post⟩ :=
    slow_loop_ready_run_block_prefix (offset := offset) boundary frontier buffers positive pointer memory wrap publish inputValid position run
  exact ⟨final, after, used, z', result, extended, nextOrigin, base', ys, before, written, remaining, blockBits, run, post⟩

end Zlib.Deflate.Engine.Proofs
