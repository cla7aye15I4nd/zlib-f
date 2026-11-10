import ZlibF.Proof.«inflate.c.whole-epoch-v4-init-rebuffer»
import ZlibF.Proof.«inflate.c.whole-epoch-entry-refusal-v4»
import ZlibF.Proof.«inflate.c.whole-epoch-final-type-check-v4»
namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.FunctionalTrailer ZlibF.Math.LZ77Copy
set_option autoImplicit false

/-- Actual local declaration transports all new source cases, including
unchecked MATCH and inverse CODE parsing, through its concrete heap. -/
def Invariant4.syncAlloc {h : Heap} {r : ZStreamRef} {log : DataLog}
    (before : Invariant4 h r log) : Invariant4 (Zlib.Inflate.Spec.syncAlloc h) r log := by
  let origin := default_origin_syncAlloc before.origin
  let point : CausalInput.AtPublic (Zlib.Inflate.Spec.syncAlloc h) r log before.source.wire :=
    ⟨before.source.point.zs, before.source.point.z, before.source.point.state, origin.good, before.source.point.source⟩
  let source : AtPublic4 (Zlib.Inflate.Spec.syncAlloc h) r log :=
    ⟨before.source.wire, point, before.source.phase, before.source.saved⟩
  exact {
    source := source
    origin := origin
    allocator := before.allocator
    materialized := SourcePhase4.Materialized.of_views before.source.phase before.materialized (by intro ref; cases ref <;> rfl)
    window := fun active => WindowHistory.dictionary_syncAlloc before.origin.toDefaultStateJ (before.window active)
    checksum := before.checksum
    wrapperOrigins := before.wrapperOrigins }

def SourcePhase4.reindex {log next : DataLog} {s : InflateState} {wire : List Bool}
    (phase : SourcePhase4 log s wire) (same : next = log) : SourcePhase4 next s wire := same ▸ phase

theorem SourcePhase4.Materialized.reindex {h : Heap} {log next : DataLog} {s : InflateState} {wire : List Bool}
    (phase : SourcePhase4 log s wire) (same : next = log) (tables : phase.Materialized h) :
    (phase.reindex same).Materialized h := by cases same; exact tables

/-- Real entry LOAD and counter assignments establish the revised finite
call cut for every non-TYPE saved state. In particular a real unchecked
MATCH wait never requires a fabricated old phase. -/
theorem Invariant4.call_entry_not_type
    {c : Ctx} {h : Heap} {r : ZStreamRef} {log : DataLog} {raw : List UInt8}
    (before : Invariant4 h r log)
    (E : Env c h r before.source.point.zs before.source.point.z before.source.point.state)
    (buffers : StreamBuffers h r) (nonnull : before.source.point.z.next_out ≠ .null)
    (input : Bytes h before.source.point.z.next_in before.source.point.z.avail_in.toNat raw)
    (notType : before.source.point.state.mode ≠ TYPE) :
    Nonempty (EpochCallCut4 c h h r before.source.point.zs before.source.point.z before.source.point.z
      before.source.point.state (dispatchRegs before.source.point.z before.source.point.state) log raw) := by
  let z := before.source.point.z
  let s := before.source.point.state
  let l := dispatchRegs z s
  have sourceEq : sourceLog (callLog log raw 0 []) = sourceLog log := by
    simp only [sourceLog, callLog, List.take_zero, List.append_nil]
  let phase := before.source.phase.reindex sourceEq
  have get : r.get h = some z := before.source.point.good.live.hz
  have originalBuffers := buffers
  obtain ⟨stream, streamGet, inputRange, outputRange, separate⟩ := buffers
  have streams : stream = z := Option.some.inj (streamGet.symm.trans get)
  subst stream
  have packet : DispatchBuffers h r l raw :=
    ⟨inputRange, dispatchRegs_output get originalBuffers nonnull s, separate,
      header_input_view_of_bytes input before.origin.held⟩
  have main : runX (inflate_run c) IL.init h = runX (xwhile (pure true) (inflate_dispatch c)) l h := by
    unfold inflate_run
    rw [runX_bind, runX_rdS E]
    simp only [notType, beq_iff_eq, ↓reduceIte, runX_bind]
    rw [LOAD_run E]
    simp only []
    rw [runX_modify]
    rfl
  have credit : TYPE ≤ s.mode → s.mode ≤ DONE → ∃ count, OutputCredit h z s l log.output [] count := by
    intro lower upper
    have seed := before.checksum lower upper
    have writable : Writable h z.next_out z.avail_out.toNat := by
      rcases outputRange with null | ⟨_read, write, _owned⟩
      · exact False.elim (nonnull null)
      · exact write rfl
    rcases writable with null | ⟨dest, off, array, pointer, arrayGet, _readonly, bound⟩
    · exact False.elim (nonnull null.1)
    refine ⟨0, ⟨by simp, ?_, ?_, dest, off, array, pointer, arrayGet, by simp, by omega, ?_⟩⟩
    · simpa only [List.take_zero, List.append_nil] using seed
    · change (z.avail_out - z.avail_out).toNat = 0 - 0
      simp
    · simp [writtenBytes]
  let facts : CallFacts c h h r before.source.point.zs z z s l log raw := {
    used := 0
    usedBound := Nat.zero_le _
    emitted := []
    word := before.source.wire
    env := E
    origin := before.origin
    allocator := before.allocator
    wrapperOrigins := before.wrapperOrigins
    main := main
    buffers := by simpa only [List.drop_zero] using packet
    bits := before.source.point.good.inv.bits
    next := by change z.next_in = inputAdvance z.next_in 0; cases z.next_in <;> rfl
    haveCount := by change z.avail_in.toNat + 0 = z.avail_in.toNat; omega
    put := by change z.next_out = inputAdvance z.next_out 0; cases z.next_out <;> rfl
    leftCount := by change z.avail_out.toNat + 0 = z.avail_out.toNat; omega
    credited := by simpa only [List.take_zero, List.append_nil, l, s, dispatchRegs] using before.source.point.source
    window := before.window
    physical := by intro dest off array _pointer _get; simp [writtenBytes]
    checksum := credit
    registers := ⟨rfl, fun _ => rfl⟩
    outputStart := fun _ => rfl
    normalRet := fun _ => rfl
    allocationOracle := rfl }
  exact ⟨⟨facts, phase, SourcePhase4.Materialized.reindex before.source.phase sourceEq before.materialized⟩⟩

#print axioms Invariant4.syncAlloc
#print axioms SourcePhase4.Materialized.reindex
#print axioms Invariant4.call_entry_not_type
end Zlib.Inflate.Proofs.WholeEpoch
