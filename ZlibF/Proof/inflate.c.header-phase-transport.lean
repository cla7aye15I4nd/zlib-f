import ZlibF.Proof.«inflate.c.header-phase-view»

namespace Zlib.Inflate.Proofs.HeaderPhaseView
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs
set_option autoImplicit false

/-- Exactly the unchanged original DataTrace.step ledger update. -/
def credit (log : DataLog) (input output : List UInt8) (used : Nat) (rc : Int32) : DataLog :=
  { log with input := log.input ++ input.take used, output := log.output ++ output, result := rc, finished := log.finished || rc == Z_STREAM_END }

theorem PhaseData.input_congr {phase : Phase} {state : InflateState} {before after : DataLog}
    (data : PhaseData phase state before) (same : after.input = before.input) : PhaseData phase state after := by
  cases phase <;> simpa only [PhaseData, same] using data

/-- Actual caller edits preserve the pure phase relation and allocator. -/
theorem Meaning.rebuffer {phase : Phase} {h after : Heap} {r : ZStreamRef} {zs : Nat} {log : DataLog}
    (before : Meaning phase h r zs log) (edit : Rebuffer h after r) (platform : ZlibF.PlatformMemory.ByteObjectsFit after) :
    Meaning phase after r zs log := by
  obtain ⟨z, state, current, allocator, window, empty, data⟩ := before
  obtain ⟨stream0, next⟩ := rebuffer_default_origin current edit platform
  obtain ⟨other, fields, good⟩ := rebuffer_inflate_good current.good edit
  have same : other = stream0 := Option.some.inj (good.live.hz.symm.trans next.good.live.hz)
  subst other
  refine ⟨stream0, state, next, ?_, window, empty, data⟩
  rw [fields]; exact allocator

/-- Original actual refusal is a phase-preserving zero-byte call for
arbitrary flush. The real temporary allocation/free heap is retained. -/
theorem Meaning.refused {phase : Phase} {h after : Heap} {r : ZStreamRef} {zs : Nat} {log : DataLog}
    {flush rc : Int32} {input output : List UInt8} {used : Nat} {stream0 : ZStream}
    (before : Meaning phase h r zs log) (get : r.get h = some stream0)
    (rejected : (stream0.next_out == .null || (stream0.next_in == .null && stream0.avail_in != 0)) = true)
    (actual : DataStep .inflate h after r flush rc input output used) :
    Meaning phase after r zs (credit log input output used rc) := by
  obtain ⟨z, state, current, allocator, window, empty, data⟩ := before
  have same : stream0 = z := Option.some.inj (get.symm.trans current.good.live.hz)
  subst stream0
  obtain ⟨_heap, _rc, next, zero, noOutput⟩ := ParserRefusal.dataStep_refused_stutter current actual rejected
  refine ⟨z, state, next, allocator, window, ?_, data.input_congr ?_⟩
  · simp only [credit, empty, noOutput, List.nil_append]
  · simp only [credit, zero, List.take_zero, List.append_nil]

/-- The actual HEAD waiting DataStep advances the original input ledger
and establishes the next unified phase, with no assumed callee postcondition. -/
theorem Meaning.head_wait {h after : Heap} {r : ZStreamRef} {zs : Nat} {log : DataLog}
    {flush rc : Int32} {input output : List UInt8} {used : Nat} {stream0 : ZStream} {observedState : InflateState}
    (before : Meaning .head h r zs log) (getZ : r.get h = some stream0) (getS : h.istates zs = some observedState)
    (selected : observedState.mode = HEAD) (short : observedState.bits.toNat + 8 * stream0.avail_in.toNat < 16)
    (actual : DataStep .inflate h after r flush rc input output used) : Meaning .head after r zs (credit log input output used rc) := by
  obtain ⟨z, state, current, allocator, window, empty, mode, last, wrap, below, count, word, bound⟩ := before
  have sameZ : stream0 = z := Option.some.inj (getZ.symm.trans current.good.live.hz)
  have sameS : observedState = state := Option.some.inj (getS.symm.trans current.good.live.hs)
  subst stream0 observedState
  obtain ⟨nextZ, nextS, next, nextAllocator, usedBound, nextMode, nextLast, nextWrap, nextWindow, nextBelow, nextCount, nextWord, noOutput⟩ :=
    EntryPath.HeadHistory.head_wait_observed current allocator actual selected (Or.inr wrap) window short
  have takeLength : (input.take used).length = used := by rw [List.length_take, Nat.min_eq_left usedBound]
  refine ⟨nextZ, nextS, next, nextAllocator, nextWindow, ?_, nextMode, nextLast.trans last, nextWrap.trans wrap, nextBelow, ?_, ?_, ?_⟩
  · simp only [credit, empty, noOutput, List.nil_append]
  · change nextS.bits.toNat = 8 * (log.input ++ input.take used).length
    rw [List.length_append, takeLength]; omega
  · change natBits nextS.bits.toNat nextS.hold.toNat = bytesBits (log.input ++ input.take used)
    rw [nextWord, word, bytesBits_append]
  · change (log.input ++ input.take used).length ≤ 1
    have total : nextS.bits.toNat = 8 * (log.input ++ input.take used).length := by rw [List.length_append, takeLength]; omega
    omega

#print axioms PhaseData.input_congr
#print axioms Meaning.rebuffer
#print axioms Meaning.refused
#print axioms Meaning.head_wait
end Zlib.Inflate.Proofs.HeaderPhaseView
