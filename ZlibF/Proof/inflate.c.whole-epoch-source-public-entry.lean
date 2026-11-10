import ZlibF.Proof.«inflate.c.whole-epoch-source-dispatch-lifts»
namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.FunctionalTrailer ZlibF.Math.LZ77Copy
set_option autoImplicit false

theorem SourcePhase4.Routed.reindex {log next : DataLog} {s : InflateState} {wire : List Bool}
    (phase : SourcePhase4 log s wire) (same : next = log) (routed : phase.Routed) :
    (phase.reindex same).Routed := by cases same; exact routed

def SourceInvariant.syncAlloc {h : Heap} {r : ZStreamRef} {log : DataLog}
    (before : SourceInvariant h r log) : SourceInvariant (Zlib.Inflate.Spec.syncAlloc h) r log :=
  ⟨before.core.syncAlloc, before.routed⟩

/-- Exact accepted-entry source construction also retains alphabet routing;
there is no existential replacement of an ordinary CODE source witness. -/
theorem SourceInvariant.call_entry_not_type
    {c : Ctx} {h : Heap} {r : ZStreamRef} {log : DataLog} {raw : List UInt8}
    (before : SourceInvariant h r log)
    (E : Env c h r before.core.source.point.zs before.core.source.point.z before.core.source.point.state)
    (buffers : StreamBuffers h r) (nonnull : before.core.source.point.z.next_out ≠ .null)
    (input : Bytes h before.core.source.point.z.next_in before.core.source.point.z.avail_in.toNat raw)
    (notType : before.core.source.point.state.mode ≠ TYPE) :
    Nonempty (SourceCallCut c h h r before.core.source.point.zs before.core.source.point.z before.core.source.point.z
      before.core.source.point.state (dispatchRegs before.core.source.point.z before.core.source.point.state) log raw) := by
  let z := before.core.source.point.z
  let s := before.core.source.point.state
  let l := dispatchRegs z s
  have sourceEq : sourceLog (callLog log raw 0 []) = sourceLog log := by
    simp only [sourceLog, callLog, List.take_zero, List.append_nil]
  let phase := before.core.source.phase.reindex sourceEq
  have get : r.get h = some z := before.core.source.point.good.live.hz
  have originalBuffers := buffers
  obtain ⟨stream, streamGet, inputRange, outputRange, separate⟩ := buffers
  have streams : stream = z := Option.some.inj (streamGet.symm.trans get)
  subst stream
  have packet : DispatchBuffers h r l raw :=
    ⟨inputRange, dispatchRegs_output get originalBuffers nonnull s, separate,
      header_input_view_of_bytes input before.core.origin.held⟩
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
    have seed := before.core.checksum lower upper
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
  let facts : CallFacts c h h r before.core.source.point.zs z z s l log raw := {
    used := 0
    usedBound := Nat.zero_le _
    emitted := []
    word := before.core.source.wire
    env := E
    origin := before.core.origin
    allocator := before.core.allocator
    wrapperOrigins := before.core.wrapperOrigins
    main := main
    buffers := by simpa only [List.drop_zero] using packet
    bits := before.core.source.point.good.inv.bits
    next := by change z.next_in = inputAdvance z.next_in 0; cases z.next_in <;> rfl
    haveCount := by change z.avail_in.toNat + 0 = z.avail_in.toNat; omega
    put := by change z.next_out = inputAdvance z.next_out 0; cases z.next_out <;> rfl
    leftCount := by change z.avail_out.toNat + 0 = z.avail_out.toNat; omega
    credited := by simpa only [List.take_zero, List.append_nil, l, s, dispatchRegs] using before.core.source.point.source
    window := before.core.window
    physical := by intro dest off array _pointer _get; simp [writtenBytes]
    checksum := credit
    registers := ⟨rfl, fun _ => rfl⟩
    outputStart := fun _ => rfl
    normalRet := fun _ => rfl
    allocationOracle := rfl }
  exact ⟨⟨⟨facts, phase, SourcePhase4.Materialized.reindex before.core.source.phase sourceEq before.core.materialized⟩, SourcePhase4.Routed.reindex before.core.source.phase sourceEq before.routed⟩⟩

#print axioms SourcePhase4.Routed.reindex
#print axioms SourceInvariant.syncAlloc
#print axioms SourceInvariant.call_entry_not_type
end Zlib.Inflate.Proofs.WholeEpoch
