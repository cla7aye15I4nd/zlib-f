import ZlibF.Proof.«inflate.c.header-data-trace»

namespace Zlib.Inflate.Proofs.HeaderSourceTrace
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs
set_option autoImplicit false

/-- Only actual continuing switch trips. No representation or parser
postcondition is a constructor premise. -/
inductive DispatchPrefix (c : Ctx) (start : IL) (before : Heap) : IL → Heap → Prop where
  | begin : DispatchPrefix c start before start before
  | step {l next : IL} {h after : Heap} : DispatchPrefix c start before l h →
      runX (inflate_dispatch c) l h = .ok ((.ok (), next), after) → DispatchPrefix c start before next after

/-- A finite actual main loop exits at one final observed switch trip. -/
def DispatchExit (c : Ctx) (start : IL) (before : Heap) (exit : Ex) (regs : IL) (after : Heap) : Prop :=
  ∃ l h, DispatchPrefix c start before l h ∧ runX (inflate_dispatch c) l h = .ok ((.error exit, regs), after)

/-- The existing closed rank proof produces a finite source-only trace
of the actual main loop, with every intermediate state established by the
real dispatch theorem rather than supplied as a callee contract. -/
theorem loop_actual_trace {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultOriginState h r zs z s)
    (buffers : DispatchBuffers h r l bs) (incoming : l.bits.toNat ≤ 39) :
    ∃ exit regs after stream0 state used made, used ≤ bs.length ∧
      runX (xwhile (pure true) (inflate_dispatch c)) l h = .ok ((.error exit, regs), after) ∧
      DefaultOriginState after r zs stream0 state ∧ DispatchBuffers after r regs (bs.drop used) ∧
      regs.bits.toNat ≤ 39 ∧ ByteViewSizes h after ∧
      regs.next = inputAdvance l.next used ∧ regs.have_.toNat + used = l.have_.toNat ∧
      regs.put = inputAdvance l.put made ∧ regs.left.toNat + made = l.left.toNat ∧
      DispatchExit c l h exit regs after := by
  let P := fun regs heap => DefaultOriginLoopInv r zs h l bs regs heap ∧ DispatchPrefix c l h regs heap
  let Q := fun (outcome : Except Ex Unit) (regs : IL) (after : Heap) =>
    ∃ exit, outcome = .error exit ∧ DefaultOriginLoopInv r zs h l bs regs after ∧ DispatchExit c l h exit regs after
  have initial : P l h := ⟨⟨z, s, 0, 0, by omega, invariant,
    by simpa only [List.drop_zero] using buffers, incoming, ByteViewSizes.refl h,
    (inputAdvance_zero l.next).symm, rfl, (inputAdvance_zero l.put).symm, rfl⟩, .begin⟩
  have step : ∀ regs heap, P regs heap → ∃ test regs1 heap1,
      runX (pure true : X Bool) regs heap = .ok ((test, regs1), heap1) ∧
      (match test with
       | .error fault => Q (.error fault) regs1 heap1
       | .ok false => Q (.ok ()) regs1 heap1
       | .ok true => ∃ result regs2 heap2,
           runX (do inflate_dispatch c; pure false) regs1 heap1 = .ok ((result, regs2), heap2) ∧
           (match result with
            | .error fault => Q (.error fault) regs2 heap2
            | .ok true => Q (.ok ()) regs2 heap2
            | .ok false => P regs2 heap2 ∧ defaultViewHeapRank zs regs2 heap2 < defaultViewHeapRank zs regs heap)) := by
    intro regs heap current
    obtain ⟨currentInv, trace⟩ := current
    obtain ⟨stream0, state, used, made, bound, currentJ, packet, bits, sizes, next, count, put, left⟩ := currentInv
    have currentEnv : Env c heap r zs stream0 state := ⟨E.strm, E.st, currentJ.good.live.hz, currentJ.good.live.hs⟩
    obtain ⟨outcome, finalRegs, finalHeap, finalStream, finalState, used2, made2, bound2,
      run, finalJ, finalPacket, finalSizes, next2, count2, put2, left2, finalBits, progress⟩ :=
      inflate_dispatch_default_origin_state_rank currentEnv currentJ packet bits
    have totalBound : used + used2 ≤ bs.length := by simp only [List.length_drop] at bound2; omega
    have final : DefaultOriginLoopInv r zs h l bs finalRegs finalHeap := by
      refine ⟨finalStream, finalState, used + used2, made + made2, totalBound, finalJ, ?_, finalBits,
        sizes.trans finalSizes, ?_, by omega, ?_, by omega⟩
      · simpa only [List.drop_drop, Nat.add_comm] using finalPacket
      · rw [next2, next, inputAdvance_add]
      · rw [put2, put, inputAdvance_add]
    refine ⟨.ok true, regs, heap, rfl, ?_⟩
    cases outcome with
    | error fault =>
      refine ⟨.error fault, finalRegs, finalHeap, ?_, fault, rfl, final, regs, heap, trace, run⟩
      rw [runX_bind, run]
    | ok unit =>
      cases unit
      refine ⟨.ok false, finalRegs, finalHeap, ?_, ⟨final, trace.step run⟩, ?_⟩
      · rw [runX_bind, run]; rfl
      · rw [defaultViewHeapRank_eq finalJ.good, defaultViewHeapRank_eq currentJ.good]
        exact progress rfl
  have budget : defaultViewHeapRank zs l h + 2 < fuel := by
    rw [defaultViewHeapRank_eq invariant.good]
    exact dispatchRank_fuel l s.mode incoming
  obtain ⟨outcome, regs, after, run, exit, normal, final, trace⟩ := xwhileBrk_rank P (defaultViewHeapRank zs) Q step initial budget
  subst outcome
  obtain ⟨stream0, state, used, made, bound, finalJ, packet, bits, sizes, next, count, put, left⟩ := final
  exact ⟨exit, regs, after, stream0, state, used, made, bound, run, finalJ, packet, bits, sizes, next, count, put, left, trace⟩

/-- The actual public-body entry supplies TYPE normalization and the LOAD
packet before the source trace. All source states are obtained from code. -/
theorem run_actual_trace {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (E : Env c h r zs z s) (initial : DefaultOriginState h r zs z s)
    (buffers : StreamBuffers h r) (nonnull : z.next_out ≠ .null) (inputValid : z.next_in = .null → z.avail_in = 0) :
    ∃ (entryHeap : Heap) (entryState : InflateState) (bs : List UInt8) (exit : Ex) (regs : IL) (after : Heap)
      (stream0 : ZStream) (state : InflateState) (used made : Nat),
      DefaultOriginState entryHeap r zs z entryState ∧
      runX (inflate_run c) IL.init h = .ok ((.error exit, regs), after) ∧
      DispatchExit c (dispatchRegs z entryState) entryHeap exit regs after ∧
      DefaultOriginState after r zs stream0 state ∧ DispatchBuffers after r regs (bs.drop used) ∧
      used ≤ bs.length ∧ regs.bits.toNat ≤ 39 ∧ ByteViewSizes h after ∧
      regs.next = inputAdvance z.next_in used ∧ regs.have_.toNat + used = z.avail_in.toNat ∧
      regs.put = inputAdvance z.next_out made ∧ regs.left.toNat + made = z.avail_out.toNat := by
  obtain ⟨entryHeap, entryState, bs, entryRun, currentJ, env, packet, bits, sizes, frame, _⟩ :=
    inflate_run_default_view_entry E initial.toDefaultStateJ buffers nonnull inputValid
  have origins := initial.decode_update currentJ frame
  obtain ⟨exit, regs, after, stream0, state, used, made, bound, run, final, finalPacket,
    finalBits, finalSizes, next, count, put, left, trace⟩ := loop_actual_trace env origins packet bits
  exact ⟨entryHeap, entryState, bs, exit, regs, after, stream0, state, used, made, origins, entryRun.trans run, trace,
    final, finalPacket, bound, finalBits, sizes.trans finalSizes, next, count, put, left⟩

#print axioms loop_actual_trace
#print axioms run_actual_trace

/-- The actual public suffix, including direct returns and inf_leave. -/
inductive BodyFinish (c : Ctx) (regs : IL) (heap : Heap) : Ex → Int32 → Heap → Prop where
  | direct (value : Int32) : BodyFinish c regs heap (.ret value) value heap
  | leave {rc : Int32} {after : Heap} : inflate_leave c regs heap = .ok (rc, after) → BodyFinish c regs heap .leave rc after

/-- Accepted public source observations. Constructors/fields record only
actual execution, reads and cleanup; no parser or representation invariant
of an intermediate state is an incoming premise. -/
inductive AcceptedCallSource (h after : Heap) (r : ZStreamRef) (zs : Nat) (z : ZStream) (s : InflateState)
    (flush rc : Int32) : Prop where
  | observed (entryHeap : Heap) (entryState : InflateState) (exit : Ex) (regs : IL)
      (bodyHeap localHeap : Heap) (localBytes : Array UInt8) :
      r.get h = some z → z.state = some (.inflate zs) → h.istates zs = some s →
      r.get entryHeap = some z → entryHeap.istates zs = some entryState →
      runX (inflate_run ⟨some r, some (.tab zs), syncBuf h, flush⟩) IL.init (syncAlloc h) = .ok ((.error exit, regs), bodyHeap) →
      DispatchExit ⟨some r, some (.tab zs), syncBuf h, flush⟩ (dispatchRegs z entryState) entryHeap exit regs bodyHeap →
      BodyFinish ⟨some r, some (.tab zs), syncBuf h, flush⟩ regs bodyHeap exit rc localHeap →
      localHeap.bytes h.nextBlk = some localBytes → localBytes.size = 4 → localHeap.ro h.nextBlk = false →
      after = freeWin localHeap (syncBuf h) → AcceptedCallSource h after r zs z s flush rc

/-- Every accepted actual DataStep from the unchanged original default
DataTrace supplies a finite source-only switch trace and real cleanup.
Initialization, all preceding calls and caller edits establish the needed
state internally through origin_from_init. -/
theorem accepted_from_data_trace
    {h after : Heap} {r : ZStreamRef} {log : DataLog} {flush rc : Int32}
    {input output : List UInt8} {used : Nat}
    (history : InflateDataTrace 15 r h log) (scope : HeaderDataTrace.PlatformScope history)
    (observed : DataStep .inflate h after r flush rc input output used)
    (accepted : ∀ z, r.get h = some z → z.next_out ≠ .null ∧ (z.next_in = .null → z.avail_in = 0)) :
    ∃ zs z s, AcceptedCallSource h after r zs z s flush rc := by
  have observed0 := observed
  obtain ⟨zs, z, s, initial, allocator⟩ := HeaderDataTrace.origin_from_init history scope
  obtain ⟨nonnull, inputValid⟩ := accepted z initial.good.live.hz
  obtain ⟨_z0, _z1, _get0, _get1, buffers, _header, _input, _used, _output, actual⟩ := observed
  let c : Ctx := ⟨some r, some (.tab zs), syncBuf h, flush⟩
  have allocated := default_origin_syncAlloc initial
  have env : Env c (syncAlloc h) r zs z s := ⟨rfl, rfl, allocated.good.live.hz, allocated.good.live.hs⟩
  have buffers0 := streamBuffers_syncAlloc initial.good.fresh buffers
  obtain ⟨entryHeap, entryState, _bs, exit, regs, bodyHeap, _stream0, _state0, _used0, _made0,
    entryOrigin, mainRun, switches, _current, _packet, _bound, _bits, _sizes, _next, _count, _put, _left⟩ :=
    run_actual_trace env allocated buffers0 nonnull inputValid
  obtain ⟨code, localHeap, returned, returnedState, localBytes, bodyRun, _final, _allocator,
    localGet, localSize, localRo⟩ := inflate_default_origin_local_state_return env allocated allocator buffers0 nonnull inputValid
      (syncAlloc_bytes_buf h) (by simp only [syncJunk, Array.size_ofFn]) (syncAlloc_ro_buf h)
  have finish : BodyFinish c regs bodyHeap exit code localHeap := by
    cases exit with
    | ret value =>
      rw [bind_app, mainRun] at bodyRun
      have same := Except.ok.inj bodyRun
      cases same
      exact .direct _
    | leave =>
      rw [bind_app, mainRun] at bodyRun
      exact .leave bodyRun
  have publicRun : C.run (inflate (some r) flush) h = .ok (code, freeWin localHeap (syncBuf h)) := by
    have entry : (z.next_out == .null || (z.next_in == .null && z.avail_in != 0)) = false := by
      by_cases null : z.next_in = .null
      · simp [nonnull, null, inputValid null]
      · simp [nonnull, null]
    unfold C.run inflate
    rw [bind_app, allocLocalB_run h initial.good.fresh]
    simp only []
    rw [bind_app]
    simp only [bind_app, stateCheck_live allocated.good.live, bne_self_eq_false, Bool.false_eq_true, ite_false,
      ldZStream_ok allocated.good.live.hz, entry, allocated.good.live.zst, castI]
    rw [bind_app] at bodyRun
    unfold runX at bodyRun
    dsimp only [c] at bodyRun
    erw [bodyRun]
    simp only []
    change (do freeB (syncBuf h); pure code) localHeap = .ok (code, freeWin localHeap (syncBuf h))
    rw [bind_app]
    dsimp only [syncBuf]
    rw [freeBuf_run localGet localRo]
    rfl
  have same := Except.ok.inj (actual.symm.trans publicRun)
  cases same
  exact ⟨zs, z, s, .observed entryHeap entryState exit regs bodyHeap localHeap localBytes
    initial.good.live.hz initial.good.live.zst initial.good.live.hs entryOrigin.good.live.hz entryOrigin.good.live.hs
    mainRun switches finish localGet localSize localRo rfl⟩

#print axioms accepted_from_data_trace


/-- The two actual public entry branches. Refusal records the real
allocated/freed heap, rather than identifying it with the original heap. -/
inductive CallSource (h after : Heap) (r : ZStreamRef) (zs : Nat) (z : ZStream) (s : InflateState)
    (flush rc : Int32) : Prop where
  | accepted : AcceptedCallSource h after r zs z s flush rc → CallSource h after r zs z s flush rc
  | refused : r.get h = some z → h.istates zs = some s →
      (z.next_out == .null || (z.next_in == .null && z.avail_in != 0)) = true →
      after = tmpFreed h → rc = Z_STREAM_ERROR → CallSource h after r zs z s flush rc

/-- Every actual DataStep has source observations from its real wb15 init
and prior calls. This classifier assumes no source-state invariant. -/
theorem data_step_source
    {h after : Heap} {r : ZStreamRef} {log : DataLog} {flush rc : Int32} {input output : List UInt8} {used : Nat}
    (history : InflateDataTrace 15 r h log) (scope : HeaderDataTrace.PlatformScope history)
    (observed : DataStep .inflate h after r flush rc input output used) :
    ∃ zs z s, CallSource h after r zs z s flush rc := by
  obtain ⟨zs, z, s, initial, _allocator⟩ := HeaderDataTrace.origin_from_init history scope
  by_cases refused : (z.next_out == .null || (z.next_in == .null && z.avail_in != 0)) = true
  · obtain ⟨heapEq, rcEq, _next, _zero, _empty⟩ := ParserRefusal.dataStep_refused_stutter initial observed refused
    exact ⟨zs, z, s, .refused initial.good.live.hz initial.good.live.hs refused heapEq rcEq⟩
  · have accepted : ∀ stream0, r.get h = some stream0 → stream0.next_out ≠ .null ∧ (stream0.next_in = .null → stream0.avail_in = 0) := by
      intro stream0 get
      have same : stream0 = z := Option.some.inj (get.symm.trans initial.good.live.hz)
      subst stream0
      refine ⟨?_, ?_⟩
      · intro null
        exact refused (by simp [null])
      · intro null
        by_cases empty : z.avail_in = 0
        · exact empty
        · exact False.elim (refused (by simp [null, empty]))
    obtain ⟨zs, z, s, source⟩ := accepted_from_data_trace history scope observed accepted
    exact ⟨zs, z, s, .accepted source⟩

/-- One source-only observation for each constructor of the unchanged
original DataTrace. Accepted calls include every actual switch trip;
refusals and dictionary calls retain their original source executions. -/
inductive ObservedEpoch {r : ZStreamRef} : {h : Heap} → {log : DataLog} → InflateDataTrace 15 r h log → Prop where
  | init {before after : Heap} {version : BPtr} {domain : InitDomain before r version}
      {actual : C.run (inflateInit2_ (some r) 15 version 112) before = .ok (Z_OK, after)} :
      ZlibF.PlatformMemory.ByteObjectsFit before → before.allocOk before.nalloc = true → ObservedEpoch (.init domain actual)
  | caller {before after : Heap} {log : DataLog} {prior : InflateDataTrace 15 r before log} {edit : Rebuffer before after r} :
      ObservedEpoch prior → ZlibF.PlatformMemory.ByteObjectsFit after → ObservedEpoch (.caller prior edit)
  | step {before after : Heap} {log : DataLog} {flush rc : Int32} {input output : List UInt8} {used : Nat}
      {prior : InflateDataTrace 15 r before log} {actual : DataStep .inflate before after r flush rc input output used} :
      ObservedEpoch prior → (∃ zs z s, CallSource before after r zs z s flush rc) → ObservedEpoch (.step prior actual)
  | dictionary {before after : Heap} {log : DataLog} {source : BPtr} {n : UInt32} {bytes : List UInt8} {rc : Int32}
      {prior : InflateDataTrace 15 r before log} {arguments : StreamArguments before r (.inflateSetDictionary (some r) source n)}
      {input : Bytes before source n.toNat bytes} {actual : C.run (inflateSetDictionary (some r) source n) before = .ok (rc, after)} :
      ObservedEpoch prior → ObservedEpoch (.dictionary prior arguments input actual)

/-- Production of all source constructors is proved for the actual original
trace, rather than being an assumed semantic history of earlier calls. -/
theorem observe_original {h : Heap} {r : ZStreamRef} {log : DataLog} {history : InflateDataTrace 15 r h log}
    (scope : HeaderDataTrace.PlatformScope history) : ObservedEpoch history := by
  induction scope with
  | @init before after version domain actual platform allocation => exact .init (domain := domain) (actual := actual) platform allocation
  | @caller before after log prior edit earlier platform ih => exact .caller (edit := edit) ih platform
  | @step before after log flush rc input output used prior actual earlier ih =>
    exact .step (actual := actual) ih (data_step_source prior earlier actual)
  | @dictionary before after log source n bytes rc prior arguments input actual earlier ih =>
    exact .dictionary (arguments := arguments) (input := input) (actual := actual) ih

#print axioms data_step_source
#print axioms observe_original


/-- The actual cast state index and records can be taken directly from
original public observations, without a caller-provided representation invariant. -/
theorem accepted_for_records
    {h after : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState} {log : DataLog}
    {flush rc : Int32} {input output : List UInt8} {used : Nat}
    (history : InflateDataTrace 15 r h log) (scope : HeaderDataTrace.PlatformScope history)
    (observed : DataStep .inflate h after r flush rc input output used)
    (getZ : r.get h = some z) (pointer : z.state = some (.inflate zs)) (getS : h.istates zs = some s)
    (nonnull : z.next_out ≠ .null) (inputValid : z.next_in = .null → z.avail_in = 0) :
    AcceptedCallSource h after r zs z s flush rc := by
  have accepted : ∀ stream0, r.get h = some stream0 → stream0.next_out ≠ .null ∧ (stream0.next_in = .null → stream0.avail_in = 0) := by
    intro stream0 get
    have same : stream0 = z := Option.some.inj (get.symm.trans getZ)
    subst stream0
    exact ⟨nonnull, inputValid⟩
  obtain ⟨index, stream0, state, source⟩ := accepted_from_data_trace history scope observed accepted
  have source0 := source
  cases source with
  | observed entryHeap entryState exit regs bodyHeap localHeap localBytes initialStream initialPointer initialState entryStream entryRecord mainRun switches finish localGet localSize localWritable freed =>
    have sameZ : stream0 = z := Option.some.inj (initialStream.symm.trans getZ)
    subst stream0
    have sameIndex : index = zs := by rw [pointer] at initialPointer; cases initialPointer; rfl
    subst index
    have sameState : state = s := Option.some.inj (initialState.symm.trans getS)
    subst state
    exact source0

#print axioms accepted_for_records

end Zlib.Inflate.Proofs.HeaderSourceTrace
