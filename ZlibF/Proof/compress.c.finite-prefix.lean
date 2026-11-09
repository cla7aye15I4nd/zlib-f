import ZlibF.Proof.«compress.c.prefix»

/-! # Soundness of finite prefixes of the actual compressor do-while -/
namespace ZlibF.Spec.Public.Proofs.CompressPrefix
open C Zlib.Compress Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open Zlib.Deflate.Engine.Proofs
open ZlibF.Spec.Public.Proofs.CompressLoop ZlibF.Spec.Public.Proofs.CompressCaller
set_option autoImplicit false
set_option maxRecDepth 100000

/-- Only actual body runs and the real OK guard are recorded. No memory
or callee contract is a constructor. Successful initialization starts at OK. -/
inductive ActualPrefix (slot : Nat) (start : Heap) (first : Locals) : Nat → Heap → Locals → Prop
  | nil : ActualPrefix slot start first 0 start first
  | step {k : Nat} {h after : Heap} {current next : Locals} :
      ActualPrefix slot start first k h current → current.1 = Z_OK →
      body (some (.tab slot)) current h = .ok (next, after) →
      ActualPrefix slot start first (k + 1) after next

/-- Exact observations retain the full original source and physical
contiguous output, as well as the same actual request history. -/
structure PrefixAccount (slot : Nat) (first : ZStream) (firstLeft firstSourceLen : UInt64)
    (source : List UInt8) (k : Nat) (h : Heap) (state : Locals)
    (used : Nat) (log : DataLog) (z : ZStream) : Prop where
  usedBound : used ≤ source.length
  history : DefaultDataTrace (.tab slot) h log
  get : h.streams slot = some z
  input : log.input = source.take used
  remaining : Ranges h (.tab slot) z state.2.1 state.2.2 (source.drop used)
  inputCount : z.avail_in.toNat + state.2.2.toNat + used = first.avail_in.toNat + firstSourceLen.toNat
  outputCount : z.avail_out.toNat + state.2.1.toNat + log.output.length = first.avail_out.toNat + firstLeft.toNat
  inputPtr : z.next_in = advance first.next_in used
  outputPtr : z.next_out = advance first.next_out log.output.length
  outputBytes : Bytes h first.next_out log.output.length log.output
  result : 0 < k → log.result = state.1
  ended : state.1 = Z_STREAM_END → state.2.2 = 0 ∧ z.avail_in = 0

/-- Every actual finite execution has exact trace, unread suffix, counts and
physical output. New buffer domains follow from retained caller extents.
No progress, capacity bound or whole-loop termination is assumed. -/
theorem actual_prefix_sound {slot ob oo k : Nat} {start after : Heap} {state : Locals}
    {first : ZStream} {left sourceLen : UInt64} {source : List UInt8}
    (history : DefaultDataTrace (.tab slot) start {}) (get : start.streams slot = some first)
    (ranges : Ranges start (.tab slot) first left sourceLen source)
    (pointer : first.next_out = .ref (.blk ob) oo)
    (execution : ActualPrefix slot start (Z_OK, left, sourceLen) k after state) :
    ∃ used log z, PrefixAccount slot first left sourceLen source k after state used log z := by
  induction execution with
  | nil =>
    have emptyOutput : Bytes start first.next_out 0 [] := by
      rcases ranges.output with null | ⟨⟨xs, bytes⟩, _writable, _outside⟩
      · exact Or.inl ⟨null, rfl, rfl⟩
      · simpa only [List.take_zero] using bytes_take bytes (Nat.zero_le _)
    exact ⟨0, {}, first, {
      usedBound := Nat.zero_le _, history := history, get := get,
      input := by simp, remaining := by simpa only [List.drop_zero] using ranges,
      inputCount := by simp, outputCount := by simp,
      inputPtr := (advance_zero _).symm, outputPtr := (advance_zero _).symm,
      outputBytes := emptyOutput, result := by intro bad; omega,
      ended := fun e => False.elim ((by decide : Z_OK ≠ Z_STREAM_END) e) }⟩
  | @step k h after current next previous guard actual ih =>
    rcases current with ⟨old, l, n⟩
    obtain ⟨already, oldLog, currentZ, known⟩ := ih
    have currentPointer : currentZ.next_out = .ref (.blk ob) (oo + oldLog.output.length) := by
      rw [known.outputPtr, pointer]
      rfl
    obtain ⟨used, written, rc, computed, z', run, traceA, getA, rangesA, inputCount, outputCount,
      inputPtr, outputPtr, outputBytes, effect, ended⟩ :=
      body_observed_step known.history known.get old l n (source.drop already) known.remaining currentPointer
    obtain ⟨states, heaps⟩ := Prod.mk.inj (Except.ok.inj (run.symm.trans actual))
    subst computed next
    have unreadLength := caller_bytes_length known.remaining.snapshot
    have totalBound : already + used ≤ source.length := by
      simp only [List.length_drop] at unreadLength
      have beforeBound := known.usedBound
      omega
    let newLog := DeflateCore.advanceLog oldLog
      (if (prepare h slot currentZ l n).2.1 != 0 then Z_NO_FLUSH else Z_FINISH)
      rc (source.drop already) written used
    have published : Bytes h (.ref (.blk ob) oo) oldLog.output.length oldLog.output := by
      rw [← pointer]
      exact known.outputBytes
    have kept := effect.keep_published_bytes published
    have newBytes : Bytes after (.ref (.blk ob) (oo + oldLog.output.length)) written.length written := by
      rw [← currentPointer]
      exact outputBytes
    have combined := published_bytes_append kept newBytes
    refine ⟨already + used, newLog, z', {
      usedBound := totalBound, history := traceA, get := getA,
      input := ?_, remaining := ?_, inputCount := ?_, outputCount := ?_,
      inputPtr := ?_, outputPtr := ?_, outputBytes := ?_, result := fun _ => rfl, ended := ended }⟩
    · change oldLog.input ++ (source.drop already).take used = source.take (already + used)
      rw [known.input, ← List.take_add]
    · simpa only [List.drop_drop] using rangesA
    · have previousCount := known.inputCount
      dsimp only at previousCount ⊢
      omega
    · change z'.avail_out.toNat + (prepare h slot currentZ l n).1.toNat +
        (oldLog.output ++ written).length = _
      rw [List.length_append]
      have previousCount := known.outputCount
      dsimp only at previousCount
      omega
    · rw [inputPtr, known.inputPtr, advance_add]
    · change z'.next_out = advance first.next_out (oldLog.output ++ written).length
      rw [outputPtr, known.outputPtr, advance_add, List.length_append]
    · change Bytes after first.next_out (oldLog.output ++ written).length (oldLog.output ++ written)
      rw [pointer, List.length_append]
      exact combined

/-- A real END execution consumed the entire original source. Its physical
contiguous output is independently valid. END reachability and capacity
sufficiency remain separate. -/
theorem actual_prefix_end_encoding {slot ob oo k : Nat} {start after : Heap} {state : Locals}
    {first : ZStream} {left sourceLen : UInt64} {source : List UInt8}
    (history : DefaultDataTrace (.tab slot) start {}) (get : start.streams slot = some first)
    (ranges : Ranges start (.tab slot) first left sourceLen source)
    (pointer : first.next_out = .ref (.blk ob) oo)
    (execution : ActualPrefix slot start (Z_OK, left, sourceLen) k after state)
    (ended : state.1 = Z_STREAM_END) :
    ∃ output, Bytes after first.next_out output.length output ∧ ZlibF.Spec.Zlib.Valid source output := by
  obtain ⟨used, log, z, sound⟩ := actual_prefix_sound history get ranges pointer execution
  have positive : 0 < k := by
    cases execution with
    | nil => exact False.elim ((by decide : Z_OK ≠ Z_STREAM_END) ended)
    | step => omega
  have stopped := sound.ended ended
  have length := caller_bytes_length ranges.snapshot
  have count := sound.inputCount
  rw [stopped.1, stopped.2] at count
  have all : used = source.length := by
    simp only [UInt64.toNat_zero, UInt32.toNat_zero, Nat.zero_add] at count
    omega
  have input : log.input = source := by rw [sound.input, all, List.take_length]
  obtain ⟨_ds, _z, _d, _config, _encoding, valid⟩ := sound.history.encoding
  have correct := valid ((sound.result positive).trans ended)
  rw [input] at correct
  exact ⟨log.output, sound.outputBytes, correct⟩

/-- Concatenation retains actual runs and the real guard at the join. -/
theorem ActualPrefix.append {slot k j : Nat} {start middle after : Heap}
    {first mid last : Locals}
    (one : ActualPrefix slot start first k middle mid)
    (two : ActualPrefix slot middle mid j after last) :
    ActualPrefix slot start first (k + j) after last := by
  induction two with
  | nil => simpa only [Nat.add_zero] using one
  | step _ guard actual ih =>
    simpa only [Nat.add_assoc] using ActualPrefix.step ih guard actual

/-- A returning execution of the real fuelled loop determines a finite
actual prefix. No engine totality, byte progress or fuel adequacy is assumed. -/
theorem loop_go_prefix {slot n : Nat} {h after : Heap} {first last : Locals}
    (ok : first.1 = Z_OK)
    (actual : cdoWhile.go (body (some (.tab slot))) condition n first h = .ok (last, after)) :
    ∃ k, 0 < k ∧ k ≤ n ∧ ActualPrefix slot h first k after last := by
  induction n generalizing h after first last with
  | zero => cases actual
  | succ n ih =>
    rw [cdoWhile.go] at actual
    simp only [bind_app] at actual
    cases run : body (some (.tab slot)) first h with
    | error e => simp only [run] at actual; cases actual
    | ok pair =>
      rcases pair with ⟨next, middle⟩
      simp only [run, condition, pure_app, bind_app] at actual
      have firstStep : ActualPrefix slot h first 1 middle next := ActualPrefix.step .nil ok run
      by_cases again : next.1 = Z_OK
      · simp only [beq_iff_eq, again, ite_true] at actual
        obtain ⟨k, positive, bound, tail⟩ := ih again actual
        exact ⟨1 + k, by omega, by omega, firstStep.append tail⟩
      · simp only [beq_iff_eq, again, ite_false, pure_app] at actual
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj actual)
        exact ⟨1, by omega, by omega, firstStep⟩

/-- This is the same loop used in compress2_z_unfold. A returning END
execution encodes the original full input in its actual output allocation. -/
theorem actual_loop_end_encoding {slot ob oo : Nat} {start after : Heap}
    {first : ZStream} {left sourceLen finalLeft finalSourceLen : UInt64} {source : List UInt8}
    (history : DefaultDataTrace (.tab slot) start {}) (get : start.streams slot = some first)
    (ranges : Ranges start (.tab slot) first left sourceLen source)
    (pointer : first.next_out = .ref (.blk ob) oo)
    (actual : loop (some (.tab slot)) (Z_OK, left, sourceLen) start =
      .ok ((Z_STREAM_END, finalLeft, finalSourceLen), after)) :
    ∃ output, Bytes after first.next_out output.length output ∧ ZlibF.Spec.Zlib.Valid source output := by
  obtain ⟨k, _positive, _bound, execution⟩ := loop_go_prefix (slot := slot) rfl actual
  exact actual_prefix_end_encoding history get ranges pointer execution rfl

end ZlibF.Spec.Public.Proofs.CompressPrefix
