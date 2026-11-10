import ZlibF.Proof.«inflate.c.sync-flags-history»
import ZlibF.Proof.«inflate.c.default-loop»
import ZlibF.Proof.«inflate.c.default-run»
import ZlibF.Proof.«inflate.c.construction-no-sync»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- All actual default dispatch branches now preserve the complete flag
relation, including dynamic construction and direct terminal exits. -/
theorem inflate_dispatch_default_flag
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL}
    {bs : List UInt8}
    (E : Env c h r zs z s)
    (invariant : DefaultFlagJ h r zs z s)
    (buffers : DispatchBuffers h r l bs)
    (raw : RawFastIO l)
    (incoming : l.bits.toNat ≤ 39) :
    ∃ outcome regs after stream state,
      runX (inflate_dispatch c) l h =
        .ok ((outcome, regs), after) ∧
      DefaultFlagJ after r zs stream state := by
  rcases defaultMode_cases invariant.modes with
    head | dictionary | block | stored | construction | data |
    trailer | terminal
  · exact inflate_dispatch_HEAD_default_flag E invariant buffers
      head incoming
  · exact inflate_dispatch_DICTIONARY_default_flag E invariant buffers
      dictionary incoming
  · exact inflate_dispatch_TYPE_default_flag E invariant buffers
      block incoming
  · exact inflate_dispatch_STORED_default_flag E invariant buffers
      stored incoming
  · exact inflate_dispatch_CONSTRUCTION_default_flag E invariant
      buffers construction raw incoming
  · exact inflate_dispatch_DATA_default_flag E invariant buffers
      data (fun _ => raw)
  · rcases trailer with check | length
    · exact inflate_dispatch_CHECK_default_flag E invariant buffers
        check incoming
    · obtain ⟨run, current⟩ :=
        inflate_LENGTH_default_flag E invariant buffers length
      exact ⟨.error Ex.leave, { l with ret := Z_STREAM_END },
        setI h zs { s with mode := DONE }, z,
        { s with mode := DONE },
        (inflate_dispatch_LENGTH E l length).trans run,
        current⟩
  · obtain ⟨run, current⟩ :=
      inflate_dispatch_TERMINAL_default_flag E invariant buffers
        terminal
    exact ⟨terminalExit s.mode, terminalRegs s.mode l,
      h, z, s, run, current⟩

/-- The real default mode loop retains the header flag through every
iteration. Continuing iterations keep the full sync-search relation;
the final exit retains the flag and the original default state relation. -/
theorem inflate_default_raw_loop_flags
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s)
    (invariant : DefaultFlagJ h r zs z s)
    (buffers : DispatchBuffers h r l bs)
    (raw : RawFastIO l) (incoming : l.bits.toNat ≤ 39) :
    ∃ exit regs after stream state used made, used ≤ bs.length ∧
      runX (xwhile (pure true) (inflate_dispatch c)) l h =
        .ok ((.error exit, regs), after) ∧
      DefaultStateJ after r zs stream state ∧
      (state.flags = -1 ∨ state.flags = 0) ∧
      DispatchBuffers after r regs (bs.drop used) ∧
      RawFastIO regs ∧ regs.bits.toNat ≤ 39 ∧
      ByteViewSizes h after ∧
      regs.next = inputAdvance l.next used ∧
      regs.have_.toNat + used = l.have_.toNat ∧
      regs.put = inputAdvance l.put made ∧
      regs.left.toNat + made = l.left.toNat := by
  let P := fun regs heap =>
    DefaultLoopInv r zs h l bs regs heap ∧
    ∃ stream state, DefaultFlagJ heap r zs stream state
  let Q := fun (outcome : Except Ex Unit) regs heap =>
    outcome ≠ .ok () ∧ DefaultLoopInv r zs h l bs regs heap ∧
    ∃ stream state, Good heap r zs stream state ∧
      (state.flags = -1 ∨ state.flags = 0)
  have initial : P l h := by
    refine ⟨?_, z, s, invariant⟩
    exact ⟨z, s, 0, 0, by omega, invariant.toDefaultStateJ,
      by simpa only [List.drop_zero] using buffers,
      raw, incoming, ByteViewSizes.refl h,
      (inputAdvance_zero l.next).symm, by rfl,
      (inputAdvance_zero l.put).symm, by rfl⟩
  have step : ∀ regs heap, P regs heap → ∃ test regs1 heap1,
      runX (pure true : X Bool) regs heap =
        .ok ((test, regs1), heap1) ∧
      (match test with
       | .error fault => Q (.error fault) regs1 heap1
       | .ok false => Q (.ok ()) regs1 heap1
       | .ok true => ∃ result regs2 heap2,
           runX (do inflate_dispatch c; pure false) regs1 heap1 =
             .ok ((result, regs2), heap2) ∧
           (match result with
            | .error fault => Q (.error fault) regs2 heap2
            | .ok true => Q (.ok ()) regs2 heap2
            | .ok false => P regs2 heap2 ∧
                defaultHeapRank zs regs2 heap2 <
                  defaultHeapRank zs regs heap)) := by
    intro regs heap ⟨current, flagWitness⟩
    obtain ⟨stream, state, used, made, bound, currentJ, packet,
      currentRaw, bits, sizes, next, count, put, left⟩ := current
    obtain ⟨flagStream, flagState, currentFlag⟩ := flagWitness
    have sameStream : flagStream = stream :=
      Option.some.inj
        (currentFlag.good.live.hz.symm.trans currentJ.good.live.hz)
    have sameState : flagState = state :=
      Option.some.inj
        (currentFlag.good.live.hs.symm.trans currentJ.good.live.hs)
    subst flagStream flagState
    have currentEnv : Env c heap r zs stream state :=
      ⟨E.strm, E.st, currentJ.good.live.hz, currentJ.good.live.hs⟩
    obtain ⟨outcome, finalRegs, finalHeap, finalStream, finalState,
      used2, made2, bound2, run, finalJ, finalPacket, finalSizes,
      next2, count2, put2, left2, finalBits, progress⟩ :=
      inflate_dispatch_default_state_rank currentEnv
        currentFlag.toDefaultStateJ packet currentRaw bits
    obtain ⟨flagOutcome, flagRegs, flagHeap, flagStream, flagState,
      flagRun, flagGood, flagValue⟩ :=
      inflate_dispatch_default_flags_two currentEnv currentFlag packet
        currentRaw bits
    rw [run] at flagRun
    cases flagRun
    have stateEq : flagState = finalState :=
      Option.some.inj
        (flagGood.live.hs.symm.trans finalJ.good.live.hs)
    subst flagState
    have totalBound : used + used2 ≤ bs.length := by
      simp only [List.length_drop] at bound2
      omega
    have finalLoop : DefaultLoopInv r zs h l bs
        finalRegs finalHeap := by
      refine ⟨finalStream, finalState, used + used2, made + made2,
        totalBound, finalJ, ?_, currentRaw.advance next2 put2,
        finalBits, sizes.trans finalSizes, ?_, ?_, ?_, ?_⟩
      · simpa only [List.drop_drop, Nat.add_comm] using finalPacket
      · rw [next2, next, inputAdvance_add]
      · omega
      · rw [put2, put, inputAdvance_add]
      · omega
    refine ⟨.ok true, regs, heap, rfl, ?_⟩
    cases outcome with
    | error fault =>
      refine ⟨.error fault, finalRegs, finalHeap, ?_, ?_⟩
      · rw [runX_bind, run]
      · exact ⟨(by intro impossible; cases impossible), finalLoop,
          finalStream, finalState, finalJ.good, flagValue⟩
    | ok unit =>
      cases unit
      have finalFlag : DefaultFlagJ finalHeap r zs
          finalStream finalState :=
        inflate_dispatch_default_flag_normal currentEnv currentFlag
          packet currentRaw bits run finalJ
      refine ⟨.ok false, finalRegs, finalHeap, ?_,
        ⟨finalLoop, finalStream, finalState, finalFlag⟩, ?_⟩
      · rw [runX_bind, run]
        rfl
      · rw [defaultHeapRank_eq finalJ.good,
          defaultHeapRank_eq currentJ.good]
        exact progress rfl
  have budget : defaultHeapRank zs l h + 2 < fuel := by
    rw [defaultHeapRank_eq invariant.good]
    exact dispatchRank_fuel l s.mode incoming
  obtain ⟨outcome, regs, after, run, stopped, final⟩ :=
    xwhileBrk_rank P (defaultHeapRank zs) Q step initial budget
  cases outcome with
  | ok unit => exact False.elim (stopped (by cases unit; rfl))
  | error exit =>
    obtain ⟨loop, witness⟩ := final
    obtain ⟨stream, state, used, made, bound, finalJ, packet,
      finalRaw, bits, sizes, next, count, put, left⟩ := loop
    obtain ⟨otherStream, otherState, otherGood, flag⟩ := witness
    have sameState : otherState = state :=
      Option.some.inj
        (otherGood.live.hs.symm.trans finalJ.good.live.hs)
    subst otherState
    exact ⟨exit, regs, after, stream, state, used, made, bound,
      run, finalJ, flag, packet, finalRaw, bits, sizes, next, count,
      put, left⟩

/-- The full default raw mode loop preserves `DefaultFlagJ` at its final
exit as well as at every continuing iteration. -/
theorem inflate_default_raw_loop_default_flag
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL}
    {bs : List UInt8}
    (E : Env c h r zs z s)
    (invariant : DefaultFlagJ h r zs z s)
    (buffers : DispatchBuffers h r l bs)
    (raw : RawFastIO l)
    (incoming : l.bits.toNat ≤ 39) :
    ∃ exit regs after stream state used made,
      used ≤ bs.length ∧
      runX (xwhile (pure true) (inflate_dispatch c)) l h =
        .ok ((.error exit, regs), after) ∧
      DefaultFlagJ after r zs stream state ∧
      DispatchBuffers after r regs (bs.drop used) ∧
      RawFastIO regs ∧ regs.bits.toNat ≤ 39 ∧
      ByteViewSizes h after ∧
      regs.next = inputAdvance l.next used ∧
      regs.have_.toNat + used = l.have_.toNat ∧
      regs.put = inputAdvance l.put made ∧
      regs.left.toNat + made = l.left.toNat := by
  let P := fun regs heap =>
    DefaultLoopInv r zs h l bs regs heap ∧
    ∃ stream state, DefaultFlagJ heap r zs stream state
  let Q := fun (outcome : Except Ex Unit) regs heap =>
    outcome ≠ .ok () ∧ P regs heap
  have initial : P l h := by
    refine ⟨?_, z, s, invariant⟩
    exact ⟨z, s, 0, 0, by omega, invariant.toDefaultStateJ,
      by simpa only [List.drop_zero] using buffers,
      raw, incoming, ByteViewSizes.refl h,
      (inputAdvance_zero l.next).symm, by rfl,
      (inputAdvance_zero l.put).symm, by rfl⟩
  have step : ∀ regs heap, P regs heap → ∃ test regs1 heap1,
      runX (pure true : X Bool) regs heap =
        .ok ((test, regs1), heap1) ∧
      (match test with
       | .error fault => Q (.error fault) regs1 heap1
       | .ok false => Q (.ok ()) regs1 heap1
       | .ok true => ∃ result regs2 heap2,
           runX (do inflate_dispatch c; pure false) regs1 heap1 =
             .ok ((result, regs2), heap2) ∧
           (match result with
            | .error fault => Q (.error fault) regs2 heap2
            | .ok true => Q (.ok ()) regs2 heap2
            | .ok false => P regs2 heap2 ∧
                defaultHeapRank zs regs2 heap2 <
                  defaultHeapRank zs regs heap)) := by
    intro regs heap ⟨current, flagWitness⟩
    obtain ⟨stream, state, used, made, bound, currentJ, packet,
      currentRaw, bits, sizes, next, count, put, left⟩ := current
    obtain ⟨flagStream, flagState, currentFlag⟩ := flagWitness
    have sameStream : flagStream = stream :=
      Option.some.inj
        (currentFlag.good.live.hz.symm.trans currentJ.good.live.hz)
    have sameState : flagState = state :=
      Option.some.inj
        (currentFlag.good.live.hs.symm.trans currentJ.good.live.hs)
    subst flagStream flagState
    have currentEnv : Env c heap r zs stream state :=
      ⟨E.strm, E.st, currentJ.good.live.hz,
        currentJ.good.live.hs⟩
    obtain ⟨outcome, finalRegs, finalHeap, finalStream, finalState,
      used2, made2, bound2, run, finalJ, finalPacket,
      finalSizes, next2, count2, put2, left2, finalBits,
      progress⟩ :=
      inflate_dispatch_default_state_rank currentEnv
        currentFlag.toDefaultStateJ packet currentRaw bits
    obtain ⟨flagOutcome, flagRegs, flagHeap, flagStream,
      flagState, flagRun, finalFlag⟩ :=
      inflate_dispatch_default_flag currentEnv currentFlag packet
        currentRaw bits
    rw [run] at flagRun
    cases flagRun
    have sameFinalState : flagState = finalState :=
      Option.some.inj
        (finalFlag.good.live.hs.symm.trans finalJ.good.live.hs)
    subst flagState
    have sameFinalStream : flagStream = finalStream :=
      Option.some.inj
        (finalFlag.good.live.hz.symm.trans finalJ.good.live.hz)
    subst flagStream
    have totalBound : used + used2 ≤ bs.length := by
      simp only [List.length_drop] at bound2
      omega
    have finalLoop : DefaultLoopInv r zs h l bs
        finalRegs finalHeap := by
      refine ⟨finalStream, finalState, used + used2,
        made + made2, totalBound, finalJ, ?_,
        currentRaw.advance next2 put2, finalBits,
        sizes.trans finalSizes, ?_, ?_, ?_, ?_⟩
      · simpa only [List.drop_drop, Nat.add_comm] using finalPacket
      · rw [next2, next, inputAdvance_add]
      · omega
      · rw [put2, put, inputAdvance_add]
      · omega
    have final : P finalRegs finalHeap :=
      ⟨finalLoop, finalStream, finalState, finalFlag⟩
    refine ⟨.ok true, regs, heap, rfl, ?_⟩
    cases outcome with
    | error fault =>
      refine ⟨.error fault, finalRegs, finalHeap, ?_, ?_⟩
      · rw [runX_bind, run]
      · exact ⟨(by intro impossible; cases impossible), final⟩
    | ok unit =>
      cases unit
      refine ⟨.ok false, finalRegs, finalHeap, ?_,
        final, ?_⟩
      · rw [runX_bind, run]
        rfl
      · rw [defaultHeapRank_eq finalJ.good,
          defaultHeapRank_eq currentJ.good]
        exact progress rfl
  have budget : defaultHeapRank zs l h + 2 < fuel := by
    rw [defaultHeapRank_eq invariant.good]
    exact dispatchRank_fuel l s.mode incoming
  obtain ⟨outcome, regs, after, run, stopped, final⟩ :=
    xwhileBrk_rank P (defaultHeapRank zs) Q step initial budget
  cases outcome with
  | ok unit =>
    exact False.elim (stopped (by cases unit; rfl))
  | error exit =>
    obtain ⟨loop, witness⟩ := final
    obtain ⟨stream, state, used, made, bound, finalJ, packet,
      finalRaw, bits, sizes, next, count, put, left⟩ := loop
    obtain ⟨otherStream, otherState, otherFlag⟩ := witness
    have sameState : otherState = state :=
      Option.some.inj
        (otherFlag.good.live.hs.symm.trans finalJ.good.live.hs)
    have sameStream : otherStream = stream :=
      Option.some.inj
        (otherFlag.good.live.hz.symm.trans finalJ.good.live.hz)
    subst otherState otherStream
    exact ⟨exit, regs, after, stream, state, used, made, bound,
      run, otherFlag, packet, finalRaw, bits, sizes, next,
      count, put, left⟩

/-- The actual source entry changes TYPE to TYPEDO and otherwise keeps the
incoming mode. This companion retains the normalization fact needed to carry
the sync-search clause; the existing entry theorem does not expose that fact. -/
theorem inflate_run_default_flag_entry
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState}
    (E : Env c h r zs z s)
    (invariant : DefaultFlagJ h r zs z s)
    (buffers : StreamBuffers h r)
    (nonnull : z.next_out ≠ .null)
    (inputValid : z.next_in = .null → z.avail_in = 0) :
    ∃ after state bs,
      runX (inflate_run c) IL.init h =
        runX (xwhile (pure true) (inflate_dispatch c))
          (dispatchRegs z state) after ∧
      DefaultFlagJ after r zs z state ∧
      Env c after r zs z state ∧
      DispatchBuffers after r (dispatchRegs z state) bs ∧
      (dispatchRegs z state).bits.toNat ≤ 39 ∧
      ByteViewSizes h after := by
  let base := invariant.toDefaultStateJ
  let good := invariant.good
  let tables := invariant.tables
  let pending := invariant.pending
  let hold := invariant.held
  obtain ⟨after, state, run, finalGood, env, output, sizes,
    frame, heapEq, stateEq⟩ :=
    inflate_run_output_entry_frame_state E good buffers nonnull
  have currentBuffers : StreamBuffers after r := by
    obtain ⟨stream, streamGet, input, out, separate⟩ := buffers
    have eq : stream = z :=
      Option.some.inj (streamGet.symm.trans good.live.hz)
    subst stream
    refine ⟨z, finalGood.live.hz, ?_, ?_, separate⟩
    · apply callerRange_transport good finalGood (by rw [frame])
        _ _ input
      · intro ref
        rw [heapEq, byte_view_get_setI]
      · intro ref
        rw [heapEq, byte_view_ro_setI]
    · apply callerRange_transport good finalGood (by rw [frame])
        _ _ out
      · intro ref
        rw [heapEq, byte_view_get_setI]
      · intro ref
        rw [heapEq, byte_view_ro_setI]
  obtain ⟨bs, inv, separate⟩ :=
    dispatchRegs_input (s := state) finalGood.live.hz
      currentBuffers inputValid (by rw [frame]; exact hold)
  have input : CallerRange after r z.next_in z.avail_in.toNat
      false := by
    obtain ⟨stream, get, input, _⟩ := currentBuffers
    have eq : stream = z :=
      Option.some.inj (get.symm.trans finalGood.live.hz)
    subst stream
    exact input
  have finalTables : DataTableInvariant after state := by
    by_cases type : s.mode = TYPE
    · intro active
      rw [stateEq, if_pos type] at active
      change DataTableMode TYPEDO at active
      rcases active with eq | eq | eq | eq | eq | eq | eq <;>
        contradiction
    · have sameState : state = s := by
        rw [stateEq, if_neg type]
      have sameHeap : after = h := by
        rw [heapEq, sameState]
        simp [setI, upd_self _ _ _ good.live.hs]
      rwa [sameHeap, sameState]
  have finalPending : DataPendingInvariant state := by
    by_cases type : s.mode = TYPE
    · apply dataPendingInvariant_idle
        (by rw [frame]; exact pending.sane)
      rw [stateEq, if_pos type]
      change TYPEDO ≠ LENEXT ∧ TYPEDO ≠ DIST ∧
        TYPEDO ≠ DISTEXT ∧ TYPEDO ≠ MATCH
      decide
    · rw [stateEq, if_neg type]
      exact pending
  have finalJ : DefaultStateJ after r zs z state := by
    by_cases type : s.mode = TYPE
    · have blockFrame : BlockHeaderFrame s state := by
        rw [stateEq, if_pos type]
        rfl
      have modes : BlockControlMode state.mode := by
        rw [stateEq, if_pos type]
        exact Or.inr (Or.inl rfl)
      have format := base.block_format (Or.inl type)
      have next := base.toDefaultDecodeJ.block_update
        finalGood finalTables finalPending blockFrame modes
        format sizes (by rw [heapEq]; rfl)
      exact base.config_update next frame.default_config format
    · have sameState : state = s := by
        rw [stateEq, if_neg type]
      have sameHeap : after = h := by
        rw [heapEq, sameState]
        simp [setI, upd_self _ _ _ good.live.hs]
      rwa [sameHeap, sameState]
  have flags : state.flags = -1 ∨ state.flags = 0 := by
    rw [frame]
    exact invariant.defaultFlags
  have search : state.mode = SYNC →
      state.«have».toNat ≤ 4 := by
    intro synced
    by_cases type : s.mode = TYPE
    · rw [stateEq, if_pos type] at synced
      have different : TYPEDO ≠ SYNC := by decide
      exact False.elim (different synced)
    · have sameState : state = s := by
        rw [stateEq, if_neg type]
      rw [sameState] at synced ⊢
      exact invariant.searchBound synced
  exact ⟨after, state, bs, run,
    ⟨⟨finalJ, search⟩, flags⟩, env,
    ⟨input, output, separate, inv⟩,
    finalGood.inv.bits, sizes⟩

/-- The actual default `inflate_run` prefix and full mode loop retain the
header flag, exact cursors, and the original state relation. -/
theorem inflate_run_default_raw_flags
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState}
    (E : Env c h r zs z s)
    (invariant : DefaultFlagJ h r zs z s)
    (buffers : StreamBuffers h r)
    (nonnull : z.next_out ≠ .null)
    (inputValid : z.next_in = .null → z.avail_in = 0)
    (raw : RawFastIO (dispatchRegs z s)) :
    ∃ (bs : List UInt8), ∃ exit regs after stream state used made,
      used ≤ bs.length ∧
      runX (inflate_run c) IL.init h =
        .ok ((.error exit, regs), after) ∧
      DefaultStateJ after r zs stream state ∧
      (state.flags = -1 ∨ state.flags = 0) ∧
      DispatchBuffers after r regs (bs.drop used) ∧
      RawFastIO regs ∧ regs.bits.toNat ≤ 39 ∧
      ByteViewSizes h after ∧
      regs.next = inputAdvance z.next_in used ∧
      regs.have_.toNat + used = z.avail_in.toNat ∧
      regs.put = inputAdvance z.next_out made ∧
      regs.left.toNat + made = z.avail_out.toNat := by
  obtain ⟨heap0, state0, bs, entryRun, currentFlag, currentEnv,
    packet, bits, sizes⟩ :=
    inflate_run_default_flag_entry E invariant buffers nonnull inputValid
  have currentRaw : RawFastIO (dispatchRegs z state0) := raw
  obtain ⟨exit, regs, after, stream, state, used, made, bound,
    run, final, finalFlags, finalPacket, finalRaw, finalBits,
    finalSizes, next, count, put, left⟩ :=
    inflate_default_raw_loop_flags currentEnv currentFlag packet
      currentRaw bits
  exact ⟨bs, exit, regs, after, stream, state, used, made, bound,
    entryRun.trans run, final, finalFlags, finalPacket, finalRaw,
    finalBits, sizes.trans finalSizes, next, count, put, left⟩

/-- The actual default `inflate_run` body preserves the complete flag and
sync-search relation through entry and final exit. -/
theorem inflate_run_default_raw_default_flag
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState}
    (E : Env c h r zs z s)
    (invariant : DefaultFlagJ h r zs z s)
    (buffers : StreamBuffers h r)
    (nonnull : z.next_out ≠ .null)
    (inputValid : z.next_in = .null → z.avail_in = 0)
    (raw : RawFastIO (dispatchRegs z s)) :
    ∃ (bs : List UInt8), ∃ exit regs after stream state used made,
      used ≤ bs.length ∧
      runX (inflate_run c) IL.init h =
        .ok ((.error exit, regs), after) ∧
      DefaultFlagJ after r zs stream state ∧
      DispatchBuffers after r regs (bs.drop used) ∧
      RawFastIO regs ∧ regs.bits.toNat ≤ 39 ∧
      ByteViewSizes h after ∧
      regs.next = inputAdvance z.next_in used ∧
      regs.have_.toNat + used = z.avail_in.toNat ∧
      regs.put = inputAdvance z.next_out made ∧
      regs.left.toNat + made = z.avail_out.toNat := by
  obtain ⟨heap0, state0, bs, entryRun, currentFlag, currentEnv,
    packet, bits, sizes⟩ :=
    inflate_run_default_flag_entry E invariant buffers nonnull
      inputValid
  have currentRaw : RawFastIO (dispatchRegs z state0) := raw
  obtain ⟨exit, regs, after, stream, state, used, made, bound,
    run, final, finalPacket, finalRaw, finalBits,
    finalSizes, next, count, put, left⟩ :=
    inflate_default_raw_loop_default_flag currentEnv currentFlag
      packet currentRaw bits
  exact ⟨bs, exit, regs, after, stream, state, used, made,
    bound, entryRun.trans run, final, finalPacket, finalRaw,
    finalBits, sizes.trans finalSizes, next, count, put, left⟩

end Zlib.Inflate.Proofs
