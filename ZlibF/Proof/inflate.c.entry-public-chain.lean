import ZlibF.Proof.«inflate.c.constructor-entry-chain»

namespace Zlib.Inflate.Proofs.EntryPath
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs
set_option autoImplicit false

theorem table_dispatch_wait_leave_seed
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (initial : DefaultOriginState h r zs z s)
    (allocator : DefAlloc z) (buffers : DispatchBuffers h r l bs)
    (mode : s.mode = TABLE) :
    ∃ outcome pulled used,
      runX (NEEDBITS 14) l h = .ok ((outcome, pulled), h) ∧ used ≤ bs.length ∧
      BitInv h pulled (bs.drop used) ∧
      (outcome = .ok () →
        ¬ ((tableCounts s pulled.hold).nlen > 286 ∨ (tableCounts s pulled.hold).ndist > 30) →
        (stream (tableRegs pulled) (bs.drop used)).length / 3 <
          (tableCounts s pulled.hold).ncode.toNat →
        ∃ regs waitingHeap rc after stream0 state,
          runX (inflate_dispatch c) l h = .ok ((.error Ex.leave, regs), waitingHeap) ∧
          inflate_leave c regs waitingHeap = .ok (rc, after) ∧
          DefaultOriginState after r zs stream0 state ∧ DefAlloc stream0 ∧
          LenlensProgress state state.hold state.bits
            (natBits (tableRegs pulled).bits.toNat (tableRegs pulled).hold.toNat ++
              bytesBits (bs.drop used)) ∧
          state.ncode = (tableCounts s pulled.hold).ncode ∧
          state.nlen = (tableCounts s pulled.hold).nlen ∧
          state.ndist = (tableCounts s pulled.hold).ndist ∧
          ∃ hlit hdist hclen firstRest secondRest,
            readBits 5 (Zlib.Inflate.Proofs.stream l bs) = some (hlit, firstRest) ∧
            readBits 5 firstRest = some (hdist, secondRest) ∧
            readBits 4 secondRest = some (hclen, Zlib.Inflate.Proofs.stream (tableRegs pulled) (bs.drop used)) ∧
            state.nlen.toNat = hlit + 257 ∧ state.ndist.toNat = hdist + 1 ∧
            state.ncode.toNat = hclen + 4) := by
  obtain ⟨outcome, pulled, used, pull, bound, inv, accepted⟩ :=
    inflate_TABLE_header_phase_start E initial buffers mode
  refine ⟨outcome, pulled, used, pull, bound, inv, ?_⟩
  intro normal valid short
  obtain ⟨phase, phasePacket, seed, fields, tableRun⟩ := accepted normal valid
  let startState := { tableCounts s pulled.hold with «have» := 0, mode := LENLENS }
  let startHeap := setI h zs startState
  have phaseEnv : Env c startHeap r zs z startState :=
    ⟨E.strm, E.st, phase.good.live.hz, phase.good.live.hs⟩
  have short0 : (Zlib.Inflate.Proofs.stream (tableRegs pulled) (bs.drop used)).length / 3 <
      startState.ncode.toNat - startState.«have».toNat := by
    simpa only [startState, UInt32.toNat_zero, Nat.sub_zero] using short
  obtain ⟨regs, heap0, state0, waiting, current, packet0, bits, trace⟩ :=
    inflate_dispatch_LENLENS_header_wait phaseEnv phase phasePacket rfl seed short0
  have readCounts := inflate_dispatch_LENLENS_header_wait_counts phaseEnv phase
    phasePacket rfl short0 waiting current.good.live.hs
  have step : runX (inflate_dispatch c) l h =
      .ok ((.error Ex.leave, regs), heap0) := by
    rw [inflate_dispatch_TABLE E _ mode, tableRun]
    rw [inflate_dispatch_LENLENS phaseEnv _ rfl] at waiting
    exact waiting
  have env0 : Env c heap0 r zs z state0 :=
    ⟨E.strm, E.st, current.good.live.hz, current.good.live.hs⟩
  obtain ⟨rc, after, stream0, state, leave, final, finalAllocator, finalTrace,
    _nextIn, _availIn, _nextOut, _availOut⟩ :=
    inflate_leave_header_progress_accounting env0 current allocator trace packet0 (by omega)
  obtain ⟨rc0, after0, stream1, state1, leave0, final0, _allocator0, codeCount, litCount, distCount⟩ :=
    inflate_leave_header_counts env0 current allocator packet0 (by omega)
  have same : (rc, after) = (rc0, after0) := Except.ok.inj (leave.symm.trans leave0)
  cases same
  have sameState : state = state1 := Option.some.inj (final.good.live.hs.symm.trans final0.good.live.hs)
  subst state1
  have code := codeCount.trans readCounts.1
  have lit := litCount.trans readCounts.2.1
  have dist := distCount.trans readCounts.2.2
  refine ⟨regs, heap0, rc, after, stream0, state, step, leave,
    final, finalAllocator, finalTrace, code, lit, dist, ?_⟩
  obtain ⟨hlit, hdist, hclen, firstRest, secondRest, firstRead, secondRead, thirdRead,
    lit0, dist0, code0⟩ := fields
  exact ⟨hlit, hdist, hclen, firstRest, secondRest, firstRead, secondRead, thirdRead,
    by rw [lit]; exact lit0, by rw [dist]; exact dist0, by rw [code]; exact code0⟩


#print axioms table_dispatch_wait_leave_seed

/-- Source-run equations produced by the closed branch lemmas compose
three real switch trips into the original LOAD/loop/leave body. -/
theorem head_type_table_body_run
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {headRegs tableRegs finalRegs : IL} {headHeap tableHeap waitingHeap after : Heap} {rc : Int32}
    (E : Env c h r zs z s) (mode : s.mode = HEAD)
    (headRun : runX (inflate_dispatch c) (dispatchRegs z s) h = .ok ((.ok (), headRegs), headHeap))
    (typeRun : runX (inflate_dispatch c) headRegs headHeap = .ok ((.ok (), tableRegs), tableHeap))
    (tableRun : runX (inflate_dispatch c) tableRegs tableHeap = .ok ((.error Ex.leave, finalRegs), waitingHeap))
    (leave : inflate_leave c finalRegs waitingHeap = .ok (rc, after)) :
    (do
      let (result, regs) ← runX (inflate_run c) IL.init
      match result with
      | .error (.ret value) => pure value
      | _ => inflate_leave c regs) h = .ok (rc, after) := by
  let locals : Nat → IL := fun j => if j = 0 then dispatchRegs z s else if j = 1 then headRegs else tableRegs
  let heaps : Nat → Heap := fun j => if j = 0 then h else if j = 1 then headHeap else tableHeap
  have steps : ∀ j, j < 2 → runX (inflate_dispatch c) (locals j) (heaps j) =
      .ok ((.ok (), locals (j + 1)), heaps (j + 1)) := by
    intro j bound
    have cases : j = 0 ∨ j = 1 := by omega
    rcases cases with rfl | rfl
    · simpa only [locals, heaps, Nat.zero_add, ite_true, Nat.add_zero,
        show ¬ (1 : Nat) = 0 from by decide, ite_false] using headRun
    · simpa only [locals, heaps, show ¬ (1 : Nat) = 0 from by decide,
        show ¬ (2 : Nat) = 0 from by decide, show ¬ (2 : Nat) = 1 from by decide,
        ite_true, ite_false, show 1 + 1 = (2 : Nat) from rfl] using typeRun
  have stop : runX (inflate_dispatch c) (locals 2) (heaps 2) =
      .ok ((.error Ex.leave, finalRegs), waitingHeap) := by
    simpa only [locals, heaps, show ¬ (2 : Nat) = 0 from by decide,
      show ¬ (2 : Nat) = 1 from by decide, ite_false] using tableRun
  have loop := xwhile_run_chain (inflate_dispatch c) locals heaps 2 (by unfold fuel; decide)
    Ex.leave finalRegs waitingHeap steps stop
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
  change runX (xwhile (pure true) (inflate_dispatch c)) (dispatchRegs z s) h = _ at loop
  rw [bind_app, entry, loop]
  exact leave

#print axioms head_type_table_body_run

/-- A fresh HEAD call follows the real HEAD, TYPE and TABLE switch trips
in one body invocation. TABLE consumes the live local registers from TYPE;
no RESTORE/LOAD round-trip is inserted between those source states. -/
theorem fresh_head_dynamic_wait_body_seed
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs : List UInt8}
    (E : Env c h r zs z s) (initial : DefaultOriginState h r zs z s)
    (allocator : DefAlloc z) (buffers : StreamBuffers h r) (nonnull : z.next_out ≠ .null)
    (input : BitInv h (dispatchRegs z s) bs) (mode : s.mode = HEAD)
    (wrap : s.wrap = 1 ∨ s.wrap = 5) (freshBits : s.bits = 0) (last : s.last = 0)
    (flushing : c.flush ≠ Z_BLOCK ∧ c.flush ≠ Z_TREES) :
    ∃ headOutcome headPulled headUsed,
      runX (NEEDBITS 16) (dispatchRegs z s) h = .ok ((headOutcome, headPulled), h) ∧
      headUsed ≤ bs.length ∧ BitInv h headPulled (bs.drop headUsed) ∧
      (headOutcome = .ok () → headHeaderRejected s headPulled = false →
        headMethodRejected headPulled = false → (headWindowRegs headPulled).len.toNat ≤ 15 →
        headDefaultMode headPulled = TYPE →
        let headRegs := { headWindowRegs headPulled with hold := 0, bits := 0 }
        let headState := headDefaultState s headPulled
        let headHeap := setI (r.put h { z with adler := 1 }) zs headState
        ∃ blockOutcome blockPulled blockUsed,
          runX (NEEDBITS 3) headRegs headHeap = .ok ((blockOutcome, blockPulled), headHeap) ∧
          blockUsed ≤ (bs.drop headUsed).length ∧ BitInv headHeap blockPulled ((bs.drop headUsed).drop blockUsed) ∧
          (blockOutcome = .ok () →
            let blockFirst := { blockPulled with hold := blockPulled.hold >>> 1, bits := blockPulled.bits - 1 }
            let dynamicRegs := { blockFirst with hold := blockFirst.hold >>> 2, bits := blockFirst.bits - 2 }
            let dynamicState := { headState with last := u2i (blockPulled.hold.toUInt32 &&& ((1 : UInt32) <<< 1 - 1)), mode := TABLE }
            let dynamicHeap := setI headHeap zs dynamicState
            let remaining := bs.drop (headUsed + blockUsed)
            blockFirst.hold.toNat % 4 = 2 →
            ∃ tableOutcome tablePulled tableUsed,
              runX (NEEDBITS 14) dynamicRegs dynamicHeap = .ok ((tableOutcome, tablePulled), dynamicHeap) ∧
              tableUsed ≤ remaining.length ∧ BitInv dynamicHeap tablePulled (remaining.drop tableUsed) ∧
              (tableOutcome = .ok () →
                ¬ ((tableCounts dynamicState tablePulled.hold).nlen > 286 ∨
                    (tableCounts dynamicState tablePulled.hold).ndist > 30) →
                (stream (tableRegs tablePulled) (remaining.drop tableUsed)).length / 3 <
                  (tableCounts dynamicState tablePulled.hold).ncode.toNat →
                ∃ rc after stream0 state,
                  (do
                    let (result, regs) ← runX (inflate_run c) IL.init
                    match result with
                    | .error (.ret value) => pure value
                    | _ => inflate_leave c regs) h = .ok (rc, after) ∧
                  DefaultOriginState after r zs stream0 state ∧ DefAlloc stream0 ∧
                  LenlensProgress state state.hold state.bits
                    (natBits (tableRegs tablePulled).bits.toNat (tableRegs tablePulled).hold.toNat ++
                      bytesBits (remaining.drop tableUsed)) ∧
                  state.ncode = (tableCounts dynamicState tablePulled.hold).ncode ∧
                  state.nlen = (tableCounts dynamicState tablePulled.hold).nlen ∧
                  state.ndist = (tableCounts dynamicState tablePulled.hold).ndist ∧
                  ∃ hlit hdist hclen firstRest secondRest,
                    readBits 5 (stream dynamicRegs remaining) = some (hlit, firstRest) ∧
                    readBits 5 firstRest = some (hdist, secondRest) ∧
                    readBits 4 secondRest = some (hclen, stream (tableRegs tablePulled) (remaining.drop tableUsed)) ∧
                    state.nlen.toNat = hlit + 257 ∧ state.ndist.toNat = hdist + 1 ∧ state.ncode.toNat = hclen + 4))) := by
  have output := dispatchRegs_output E.hz buffers nonnull s
  obtain ⟨z0, zget, inputRange, _outputRange, separate⟩ := buffers
  have sameZ : z0 = z := Option.some.inj (zget.symm.trans E.hz)
  subst z0
  have packet : DispatchBuffers h r (dispatchRegs z s) bs := ⟨inputRange, output, separate, input⟩
  obtain ⟨headOutcome, headPulled, headUsed, headPull, headBound, headInv, headAccepted⟩ :=
    fresh_head_dynamic_table_entry E initial packet mode wrap freshBits last flushing
  refine ⟨headOutcome, headPulled, headUsed, headPull, headBound, headInv, ?_⟩
  intro headNormal header method window noDictionary
  dsimp only
  obtain ⟨blockOutcome, blockPulled, blockUsed, headRun, _headJ, blockPull, blockBound, blockInv, blockAccepted⟩ :=
    headAccepted headNormal header method window noDictionary
  refine ⟨blockOutcome, blockPulled, blockUsed, blockPull, blockBound, blockInv, ?_⟩
  intro blockNormal dynamic
  obtain ⟨blockRun, tableJ, tablePacket, _headRead, _lastRead, _typeRead, _bits⟩ := blockAccepted blockNormal dynamic
  have tableEnv : Env c _ r zs { z with adler := 1 } _ :=
    ⟨E.strm, E.st, tableJ.good.live.hz, tableJ.good.live.hs⟩
  obtain ⟨tableOutcome, tablePulled, tableUsed, tablePull, tableBound, tableInv, tableAccepted⟩ :=
    table_dispatch_wait_leave_seed tableEnv tableJ allocator tablePacket rfl
  refine ⟨tableOutcome, tablePulled, tableUsed, tablePull, tableBound, tableInv, ?_⟩
  intro tableNormal valid short
  obtain ⟨regs, waitingHeap, rc, after, stream0, state, tableRun, leave,
    final, finalAllocator, trace, codeCount, litCount, distCount, fields⟩ := tableAccepted tableNormal valid short
  exact ⟨rc, after, stream0, state,
    head_type_table_body_run E mode headRun blockRun tableRun leave,
    final, finalAllocator, trace, codeCount, litCount, distCount, fields⟩

#print axioms fresh_head_dynamic_wait_body_seed

/-- The selected complete header path is one actual public call,
including its original temporary allocation and free. Freshness and last
zero are source entry fields supplied by actual initialization/rebuffer. -/
theorem fresh_head_dynamic_wait_public_seed
    {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs : List UInt8}
    (initial : DefaultOriginState h r zs z s)
    (allocator : DefAlloc z) (buffers : StreamBuffers h r) (nonnull : z.next_out ≠ .null)
    (inputValid : z.next_in = .null → z.avail_in = 0)
    (inputBytes : Bytes h z.next_in z.avail_in.toNat bs) (mode : s.mode = HEAD)
    (wrap : s.wrap = 1 ∨ s.wrap = 5) (freshBits : s.bits = 0) (last : s.last = 0)
    (flush : Int32) (flushing : flush ≠ Z_BLOCK ∧ flush ≠ Z_TREES) :
    ∃ headOutcome headPulled headUsed,
      runX (NEEDBITS 16) (dispatchRegs z s) (syncAlloc h) = .ok ((headOutcome, headPulled), syncAlloc h) ∧
      headUsed ≤ bs.length ∧ BitInv (syncAlloc h) headPulled (bs.drop headUsed) ∧
      (headOutcome = .ok () → headHeaderRejected s headPulled = false →
        headMethodRejected headPulled = false → (headWindowRegs headPulled).len.toNat ≤ 15 →
        headDefaultMode headPulled = TYPE →
        let headRegs := { headWindowRegs headPulled with hold := 0, bits := 0 }
        let headState := headDefaultState s headPulled
        let headHeap := setI (r.put (syncAlloc h) { z with adler := 1 }) zs headState
        ∃ blockOutcome blockPulled blockUsed,
          runX (NEEDBITS 3) headRegs headHeap = .ok ((blockOutcome, blockPulled), headHeap) ∧
          blockUsed ≤ (bs.drop headUsed).length ∧ BitInv headHeap blockPulled ((bs.drop headUsed).drop blockUsed) ∧
          (blockOutcome = .ok () →
            let blockFirst := { blockPulled with hold := blockPulled.hold >>> 1, bits := blockPulled.bits - 1 }
            let dynamicRegs := { blockFirst with hold := blockFirst.hold >>> 2, bits := blockFirst.bits - 2 }
            let dynamicState := { headState with last := u2i (blockPulled.hold.toUInt32 &&& ((1 : UInt32) <<< 1 - 1)), mode := TABLE }
            let dynamicHeap := setI headHeap zs dynamicState
            let remaining := bs.drop (headUsed + blockUsed)
            blockFirst.hold.toNat % 4 = 2 →
            ∃ tableOutcome tablePulled tableUsed,
              runX (NEEDBITS 14) dynamicRegs dynamicHeap = .ok ((tableOutcome, tablePulled), dynamicHeap) ∧
              tableUsed ≤ remaining.length ∧ BitInv dynamicHeap tablePulled (remaining.drop tableUsed) ∧
              (tableOutcome = .ok () →
                ¬ ((tableCounts dynamicState tablePulled.hold).nlen > 286 ∨
                    (tableCounts dynamicState tablePulled.hold).ndist > 30) →
                (stream (tableRegs tablePulled) (remaining.drop tableUsed)).length / 3 <
                  (tableCounts dynamicState tablePulled.hold).ncode.toNat →
                ∃ rc after stream0 state,
                  C.run (inflate (some r) flush) h = .ok (rc, after) ∧
                  after.bytes h.nextBlk = none ∧
                  DefaultOriginState after r zs stream0 state ∧ DefAlloc stream0 ∧
                  LenlensProgress state state.hold state.bits
                    (natBits (tableRegs tablePulled).bits.toNat (tableRegs tablePulled).hold.toNat ++
                      bytesBits (remaining.drop tableUsed)) ∧
                  state.ncode = (tableCounts dynamicState tablePulled.hold).ncode ∧
                  state.nlen = (tableCounts dynamicState tablePulled.hold).nlen ∧
                  state.ndist = (tableCounts dynamicState tablePulled.hold).ndist ∧
                  ∃ hlit hdist hclen firstRest secondRest,
                    readBits 5 (stream dynamicRegs remaining) = some (hlit, firstRest) ∧
                    readBits 5 firstRest = some (hdist, secondRest) ∧
                    readBits 4 secondRest = some (hclen, stream (tableRegs tablePulled) (remaining.drop tableUsed)) ∧
                    state.nlen.toNat = hlit + 257 ∧ state.ndist.toNat = hdist + 1 ∧ state.ncode.toNat = hclen + 4))) := by
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
  obtain ⟨rc, heap1, stream0, state, bytes, bodyRun, current, finalAllocator,
    localGet, localSize, localRo⟩ :=
    inflate_default_origin_local_state_return env allocated allocator
      (streamBuffers_syncAlloc initial.good.fresh buffers) nonnull inputValid
      (syncAlloc_bytes_buf h) (by simp only [syncJunk, Array.size_ofFn]) (syncAlloc_ro_buf h)
  have publicRun : C.run (inflate (some r) flush) h = .ok (rc, freeWin heap1 (syncBuf h)) := by
    have entry : (z.next_out == .null || (z.next_in == .null && z.avail_in != 0)) = false := by
      by_cases null : z.next_in = .null
      · simp [nonnull, null, inputValid null]
      · simp [nonnull, null]
    unfold C.run inflate
    rw [bind_app, allocLocalB_run h initial.good.fresh]
    simp only []
    rw [bind_app]
    simp only [bind_app, stateCheck_live allocated.good.live,
      bne_self_eq_false, Bool.false_eq_true, ite_false,
      ldZStream_ok allocated.good.live.hz, entry, allocated.good.live.zst, castI]
    rw [bind_app] at bodyRun
    unfold runX at bodyRun
    dsimp only [c] at bodyRun
    erw [bodyRun]
    simp only []
    change (do freeB (syncBuf h); pure rc) heap1 = .ok (rc, freeWin heap1 (syncBuf h))
    rw [bind_app]
    dsimp only [syncBuf]
    rw [freeBuf_run localGet localRo]
    rfl
  have final := current.free_local localGet localSize
  obtain ⟨headOutcome, headPulled, headUsed, headPull, headBound, headInv, headAccepted⟩ :=
    fresh_head_dynamic_wait_body_seed env allocated allocator
      (streamBuffers_syncAlloc initial.good.fresh buffers) nonnull input0 mode wrap freshBits last flushing
  refine ⟨headOutcome, headPulled, headUsed, headPull, headBound, headInv, ?_⟩
  intro headNormal header method window noDictionary
  dsimp only
  obtain ⟨blockOutcome, blockPulled, blockUsed, blockPull, blockBound, blockInv, blockAccepted⟩ :=
    headAccepted headNormal header method window noDictionary
  refine ⟨blockOutcome, blockPulled, blockUsed, blockPull, blockBound, blockInv, ?_⟩
  intro blockNormal dynamic
  obtain ⟨tableOutcome, tablePulled, tableUsed, tablePull, tableBound, tableInv, tableAccepted⟩ :=
    blockAccepted blockNormal dynamic
  refine ⟨tableOutcome, tablePulled, tableUsed, tablePull, tableBound, tableInv, ?_⟩
  intro tableNormal valid short
  obtain ⟨traceRc, traceHeap, traceStream, traceState, traceRun, traceFinal,
    _traceAllocator, trace, codeCount, litCount, distCount, fields⟩ := tableAccepted tableNormal valid short
  have same : (rc, heap1) = (traceRc, traceHeap) := Except.ok.inj (bodyRun.symm.trans traceRun)
  cases same
  have sameState : state = traceState :=
    Option.some.inj (current.good.live.hs.symm.trans traceFinal.good.live.hs)
  refine ⟨rc, freeWin heap1 (syncBuf h), stream0, state, publicRun, ?_, final, finalAllocator, ?_⟩
  · simp only [syncBuf, freeWin, upd_same]
  · rw [sameState]
    exact ⟨trace, codeCount, litCount, distCount, fields⟩

#print axioms fresh_head_dynamic_wait_public_seed

/-- The selected public dynamic-header path starts at the actual default
initializer and a legal caller buffer replacement. In particular last
zero and the fresh held word are proved by the source initializer, not
assumed from a weaker initialization postcondition. -/
theorem initialized_rebuffer_dynamic_public_seed
    (before : Heap) (r : ZStreamRef) (version : BPtr)
    (domain : InitDomain before r version) (platform : ZlibF.PlatformMemory.ByteObjectsFit before)
    (allocation : before.allocOk before.nalloc = true) :
    ∃ initialized z s,
      C.run (inflateInit_ (some r) version 112) before = .ok (Z_OK, initialized) ∧
      DefaultOriginState initialized r before.nextBlk z s ∧ DefAlloc z ∧
      StreamReachable .inflate initialized r ∧
      ∀ incoming, Rebuffer initialized incoming r → ZlibF.PlatformMemory.ByteObjectsFit incoming →
        ∃ stream0, DefaultOriginState incoming r before.nextBlk stream0 s ∧ DefAlloc stream0 ∧
          ∀ bs flush, StreamBuffers incoming r → stream0.next_out ≠ .null →
            (stream0.next_in = .null → stream0.avail_in = 0) →
            Bytes incoming stream0.next_in stream0.avail_in.toNat bs →
            (flush ≠ Z_BLOCK ∧ flush ≠ Z_TREES) →
            ∃ headOutcome headPulled headUsed,
              runX (NEEDBITS 16) (dispatchRegs stream0 s) (syncAlloc incoming) = .ok ((headOutcome, headPulled), syncAlloc incoming) ∧
              headUsed ≤ bs.length ∧ BitInv (syncAlloc incoming) headPulled (bs.drop headUsed) ∧
              (headOutcome = .ok () → headHeaderRejected s headPulled = false →
                headMethodRejected headPulled = false → (headWindowRegs headPulled).len.toNat ≤ 15 →
                headDefaultMode headPulled = TYPE →
                let headRegs := { headWindowRegs headPulled with hold := 0, bits := 0 }
                let headState := headDefaultState s headPulled
                let headHeap := setI (r.put (syncAlloc incoming) { stream0 with adler := 1 }) before.nextBlk headState
                ∃ blockOutcome blockPulled blockUsed,
                  runX (NEEDBITS 3) headRegs headHeap = .ok ((blockOutcome, blockPulled), headHeap) ∧
                  blockUsed ≤ (bs.drop headUsed).length ∧ BitInv headHeap blockPulled ((bs.drop headUsed).drop blockUsed) ∧
                  (blockOutcome = .ok () →
                    let blockFirst := { blockPulled with hold := blockPulled.hold >>> 1, bits := blockPulled.bits - 1 }
                    let dynamicRegs := { blockFirst with hold := blockFirst.hold >>> 2, bits := blockFirst.bits - 2 }
                    let dynamicState := { headState with last := u2i (blockPulled.hold.toUInt32 &&& ((1 : UInt32) <<< 1 - 1)), mode := TABLE }
                    let dynamicHeap := setI headHeap before.nextBlk dynamicState
                    let remaining := bs.drop (headUsed + blockUsed)
                    blockFirst.hold.toNat % 4 = 2 →
                    ∃ tableOutcome tablePulled tableUsed,
                      runX (NEEDBITS 14) dynamicRegs dynamicHeap = .ok ((tableOutcome, tablePulled), dynamicHeap) ∧
                      tableUsed ≤ remaining.length ∧ BitInv dynamicHeap tablePulled (remaining.drop tableUsed) ∧
                      (tableOutcome = .ok () →
                        ¬ ((tableCounts dynamicState tablePulled.hold).nlen > 286 ∨
                            (tableCounts dynamicState tablePulled.hold).ndist > 30) →
                        (stream (tableRegs tablePulled) (remaining.drop tableUsed)).length / 3 <
                          (tableCounts dynamicState tablePulled.hold).ncode.toNat →
                        ∃ rc after stream0 state,
                          C.run (inflate (some r) flush) incoming = .ok (rc, after) ∧
                          after.bytes incoming.nextBlk = none ∧
                          DefaultOriginState after r before.nextBlk stream0 state ∧ DefAlloc stream0 ∧
                          LenlensProgress state state.hold state.bits
                            (natBits (tableRegs tablePulled).bits.toNat (tableRegs tablePulled).hold.toNat ++
                              bytesBits (remaining.drop tableUsed)) ∧
                          state.ncode = (tableCounts dynamicState tablePulled.hold).ncode ∧
                          state.nlen = (tableCounts dynamicState tablePulled.hold).nlen ∧
                          state.ndist = (tableCounts dynamicState tablePulled.hold).ndist ∧
                          ∃ hlit hdist hclen firstRest secondRest,
                            readBits 5 (stream dynamicRegs remaining) = some (hlit, firstRest) ∧
                            readBits 5 firstRest = some (hdist, secondRest) ∧
                            readBits 4 secondRest = some (hclen, stream (tableRegs tablePulled) (remaining.drop tableUsed)) ∧
                            state.nlen.toNat = hlit + 257 ∧ state.ndist.toNat = hdist + 1 ∧ state.ncode.toNat = hclen + 4))) := by
  obtain ⟨initialized, z, s, initRun, initial, allocator, reachable,
    head, last, _held, bits, wrap, caller⟩ :=
    default_initialized_rebuffer_entry before r version domain platform allocation
  refine ⟨initialized, z, s, initRun, initial, allocator, reachable, ?_⟩
  intro incoming edit nextPlatform
  obtain ⟨stream0, current, currentAllocator, _localBits, _inputView⟩ := caller incoming edit nextPlatform
  refine ⟨stream0, current, currentAllocator, ?_⟩
  intro bs flush buffers nonnull inputValid inputBytes flushing
  exact fresh_head_dynamic_wait_public_seed current currentAllocator buffers nonnull
    inputValid inputBytes head (Or.inr wrap) bits last flush flushing

#print axioms initialized_rebuffer_dynamic_public_seed
end Zlib.Inflate.Proofs.EntryPath
