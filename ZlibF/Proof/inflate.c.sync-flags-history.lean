import ZlibF.Proof.«inflate.c.sync-default-history»
import ZlibF.Proof.«inflate.c.default-query-history»
import ZlibF.Proof.«inflate.c.sync-byte-views»
import ZlibF.Proof.«inflate.c.head-flags»
import ZlibF.Proof.«inflate.c.check-return-shape»
import ZlibF.Proof.«inflate.c.normal-dispatch-mode»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The default zlib wrapper has either not read a header or has read its
zlib header. This internal history clause is needed when sync resets to TYPE. -/
structure DefaultFlagJ (h : Heap) (r : ZStreamRef) (zs : Nat) (z : ZStream)
    (s : InflateState) : Prop extends DefaultSyncJ h r zs z s where
  defaultFlags : s.flags = -1 ∨ s.flags = 0

/-- The actual HEAD dispatch preserves the two default-wrapper flag values
through partial input, rejected headers and accepted headers. -/
theorem inflate_dispatch_HEAD_default_flag {c : Ctx} {h : Heap}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s)
    (invariant : DefaultFlagJ h r zs z s)
    (buffers : DispatchBuffers h r l bs)
    (mode : s.mode = HEAD) (incoming : l.bits.toNat ≤ 39) :
    ∃ outcome regs after stream state,
      runX (inflate_dispatch c) l h = .ok ((outcome, regs), after) ∧
      DefaultFlagJ after r zs stream state := by
  obtain ⟨outcome, regs, after, stream, state, used, bound, run,
    current, packet, sizes, next, count, put, left, bits, static,
    frame, streamFrame, progress⟩ :=
    inflate_dispatch_HEAD_state_rank E invariant.toDefaultStateJ buffers mode
      incoming
  have flagStep := inflate_dispatch_HEAD_flags_two E
    invariant.toDefaultStateJ buffers mode run current.good
  have flags : state.flags = -1 ∨ state.flags = 0 := by
    rcases flagStep with same | zero
    · rw [same]
      exact invariant.defaultFlags
    · exact Or.inr zero
  have boundCount : state.mode = SYNC → state.«have».toNat ≤ 4 := by
    intro synced
    exact False.elim
      ((inflate_dispatch_HEAD_not_sync E invariant.toDefaultStateJ
        buffers mode run current.good) synced)
  exact ⟨outcome, regs, after, stream, state, run,
    ⟨⟨current, boundCount⟩, flags⟩⟩

/-- Block-type dispatch changes table selectors and the mode, while keeping
the default header flag and never entering SYNC. -/
theorem inflate_dispatch_TYPE_default_flag {c : Ctx} {h : Heap}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s)
    (invariant : DefaultFlagJ h r zs z s)
    (buffers : DispatchBuffers h r l bs)
    (mode : s.mode = TYPE ∨ s.mode = TYPEDO)
    (incoming : l.bits.toNat ≤ 39) :
    ∃ outcome regs after stream state,
      runX (inflate_dispatch c) l h = .ok ((outcome, regs), after) ∧
      DefaultFlagJ after r zs stream state := by
  obtain ⟨outcome, regs, after, stream, state, used, bound, run,
    current, modes, packet, sizes, next, count, put, left, bits,
    static, frame, streamFrame, progress⟩ :=
    inflate_dispatch_type_state_rank E invariant.toDefaultStateJ buffers mode
      incoming
  have flags : state.flags = -1 ∨ state.flags = 0 := by
    rw [frame]
    exact invariant.defaultFlags
  have boundCount : state.mode = SYNC → state.«have».toNat ≤ 4 := by
    intro synced
    rcases modes with selected | selected | selected | selected | selected | selected | selected <;>
      rw [selected] at synced <;> contradiction
  exact ⟨outcome, regs, after, stream, state, run,
    ⟨⟨current, boundCount⟩, flags⟩⟩

/-- A dictionary request retains the flag, while a supplied dictionary
continues through the checked TYPE path. -/
theorem inflate_DICT_default_flag {c : Ctx} {h : Heap}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s)
    (invariant : DefaultFlagJ h r zs z s)
    (buffers : DispatchBuffers h r l bs)
    (mode : s.mode = DICT) (incoming : l.bits.toNat ≤ 39) :
    ∃ outcome regs after stream state,
      runX (inflate_DICT c) l h = .ok ((outcome, regs), after) ∧
      DefaultFlagJ after r zs stream state := by
  by_cases missing : s.havedict = 0
  · obtain ⟨run, current, tables, pending, _, sizes, static, held, _, _⟩ :=
      inflate_DICT_wait_boundary E invariant.good invariant.pending buffers
        mode missing incoming
    have final := invariant.toDefaultStateJ.dictionary_update
      (Or.inr mode) current tables pending (by rfl) (Or.inl mode)
      held sizes static
    have bound : (leaveState s l).mode = SYNC →
        (leaveState s l).«have».toNat ≤ 4 := by
      intro synced
      rw [show (leaveState s l).mode = s.mode by rfl, mode] at synced
      have different : DICT ≠ SYNC := by decide
      exact False.elim (different synced)
    have flags : (leaveState s l).flags = -1 ∨
        (leaveState s l).flags = 0 := by
      simpa [leaveState] using invariant.defaultFlags
    exact ⟨.error (Ex.ret Z_NEED_DICT), l, _, _, _, run,
      ⟨⟨final, bound⟩, flags⟩⟩
  · let ready := { s with check := 1, mode := TYPE }
    let stream0 := { z with adler := 1 }
    let heap0 := setI (r.put h stream0) zs ready
    have good0 : Good heap0 r zs stream0 ready :=
      invariant.good.setZI rfl invariant.good.live.zalloc
        invariant.good.live.zfree rfl
        (by change HEAD ≤ TYPE ∧ TYPE ≤ SYNC; decide)
        (invariant.good.inv.of_fields rfl rfl rfl rfl rfl rfl rfl rfl
          rfl invariant.good.inv.bits rfl rfl rfl)
    have views : ∀ ref : BRef,
        (Space.get heap0 ref : Option (Array UInt8)) = Space.get h ref := by
      intro ref
      rw [byte_view_get_setI, byte_view_get_stream_put]
    have readonly : ∀ ref : BRef,
        Space.ro heap0 ref = Space.ro h ref := by
      intro ref
      rw [byte_view_ro_setI, byte_view_ro_stream_put]
    have sizes0 : ByteViewSizes h heap0 := by
      intro ref
      rw [views]
    have static0 : heap0.static = h.static := by
      simp only [heap0, setI, ZStreamRef.put_static]
    have E0 : Env c heap0 r zs stream0 ready :=
      ⟨E.strm, E.st, good0.live.hz, good0.live.hs⟩
    have pending0 : DataPendingInvariant ready := by
      apply dataPendingInvariant_idle (s := ready) invariant.pending.sane
      change TYPE ≠ LENEXT ∧ TYPE ≠ DIST ∧ TYPE ≠ DISTEXT ∧ TYPE ≠ MATCH
      decide
    have tables0 : DataTableInvariant heap0 ready :=
      dataTableInvariant_inactive
        (by change ¬ DataTableMode TYPE; unfold DataTableMode; decide)
    have state0 := invariant.toDefaultStateJ.dictionary_update
      (Or.inr mode) good0 tables0 pending0 (by rfl) (Or.inr rfl)
      invariant.held sizes0 static0
    have flag0 : DefaultFlagJ heap0 r zs stream0 ready := by
      refine ⟨⟨state0, ?_⟩, ?_⟩
      · intro synced
        have different : TYPE ≠ SYNC := by decide
        exact False.elim (different synced)
      · simpa [ready] using invariant.defaultFlags
    have packet0 := buffers.byte_views invariant.good good0 rfl
      views readonly
    obtain ⟨outcome, regs, after, stream, state, run, final⟩ :=
      inflate_dispatch_TYPE_default_flag E0 flag0 packet0
        (Or.inl rfl) incoming
    have selector : runX (inflate_dispatch c) l heap0 =
        runX (inflate_TYPE c) l heap0 := by
      rw [inflate_dispatch_block_type E0 l (Or.inl rfl), if_pos rfl]
    exact ⟨outcome, regs, after, stream, state,
      (inflate_DICT_ready_cut E l missing).trans
        (selector.symm.trans run), final⟩

/-- Dictionary-id parsing retains the default flag through input waits and
through its actual DICT continuation. -/
theorem inflate_DICTID_default_flag {c : Ctx} {h : Heap}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s)
    (invariant : DefaultFlagJ h r zs z s)
    (buffers : DispatchBuffers h r l bs)
    (mode : s.mode = DICTID) (incoming : l.bits.toNat ≤ 39) :
    ∃ outcome regs after stream state,
      runX (inflate_DICTID c) l h = .ok ((outcome, regs), after) ∧
      DefaultFlagJ after r zs stream state := by
  obtain ⟨outcome, current, used, pull, usedBound, bitInv, _, _, shape,
    _, _, _, _, kinds, cursor⟩ :=
    NEEDBITS_run_cursor buffers.bits 32 (by decide)
  have packet : DispatchBuffers h r current (bs.drop used) :=
    buffers.consume invariant.good invariant.good rfl
      (fun _ => rfl) (fun _ => rfl)
      (by rw [shape]; rfl) cursor usedBound bitInv
  rcases kinds with normal | wait
  · rw [normal] at pull
    let value := ZSWAP32 current.hold
    let ready := { s with check := value, mode := DICT }
    let stream0 := { z with adler := value }
    let heap0 := setI (r.put h stream0) zs ready
    let first := { current with hold := 0, bits := 0 }
    have good0 : Good heap0 r zs stream0 ready :=
      invariant.good.setZI rfl invariant.good.live.zalloc
        invariant.good.live.zfree rfl
        (by change HEAD ≤ DICT ∧ DICT ≤ SYNC; decide)
        (invariant.good.inv.of_fields rfl rfl rfl rfl rfl rfl rfl rfl
          rfl invariant.good.inv.bits rfl rfl rfl)
    have E0 : Env c heap0 r zs stream0 ready :=
      ⟨E.strm, E.st, good0.live.hz, good0.live.hs⟩
    have pending0 : DataPendingInvariant ready := by
      apply dataPendingInvariant_idle (s := ready) invariant.pending.sane
      change DICT ≠ LENEXT ∧ DICT ≠ DIST ∧ DICT ≠ DISTEXT ∧ DICT ≠ MATCH
      decide
    have inv0 : BitInv heap0 first (bs.drop used) := by
      have inv := (INITBITS_inv bitInv).1
      apply inv.byte_views
      intro ref
      rw [byte_view_get_setI, byte_view_get_stream_put]
    have packet0 : DispatchBuffers heap0 r first (bs.drop used) :=
      buffers.consume invariant.good good0 rfl
        (fun ref => by rw [byte_view_get_setI, byte_view_get_stream_put])
        (fun ref => by rw [byte_view_ro_setI, byte_view_ro_stream_put])
        (by dsimp only [first]; rw [shape]; rfl)
        cursor usedBound inv0
    have sizes0 : ByteViewSizes h heap0 := by
      intro ref
      rw [byte_view_get_setI, byte_view_get_stream_put]
    have static0 : heap0.static = h.static := by
      simp only [heap0, setI, ZStreamRef.put_static]
    have tables0 : DataTableInvariant heap0 ready :=
      dataTableInvariant_inactive
        (by change ¬ DataTableMode DICT; unfold DataTableMode; decide)
    have state0 := invariant.toDefaultStateJ.dictionary_update
      (Or.inl mode) good0 tables0 pending0 (by rfl) (Or.inl rfl)
      invariant.held sizes0 static0
    have flag0 : DefaultFlagJ heap0 r zs stream0 ready := by
      refine ⟨⟨state0, ?_⟩, ?_⟩
      · intro synced
        have different : DICT ≠ SYNC := by decide
        exact False.elim (different synced)
      · simpa [ready] using invariant.defaultFlags
    obtain ⟨exit, regs, after, stream, state, run, final⟩ :=
      inflate_DICT_default_flag E0 flag0 packet0 rfl
        (by change 0 ≤ 39; decide)
    exact ⟨exit, regs, after, stream, state,
      (inflate_DICTID_parsed_cut E l current pull).trans run, final⟩
  · have run := inflate_DICTID_wait (c := c) (by rwa [wait] at pull)
    exact ⟨.error Ex.leave, current, h, z, s, run, invariant⟩

/-- Both dictionary switch entries preserve the default history flag. -/
theorem inflate_dispatch_DICTIONARY_default_flag {c : Ctx} {h : Heap}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s)
    (invariant : DefaultFlagJ h r zs z s)
    (buffers : DispatchBuffers h r l bs)
    (mode : s.mode = DICTID ∨ s.mode = DICT)
    (incoming : l.bits.toNat ≤ 39) :
    ∃ outcome regs after stream state,
      runX (inflate_dispatch c) l h = .ok ((outcome, regs), after) ∧
      DefaultFlagJ after r zs stream state := by
  rcases mode with id | dictionary
  · rw [inflate_dispatch_DICTID E l id]
    exact inflate_DICTID_default_flag E invariant buffers id incoming
  · rw [inflate_dispatch_DICT E l dictionary]
    exact inflate_DICT_default_flag E invariant buffers dictionary incoming

/-- The actual CHECK source either waits with the old state, writes BAD,
or completes LENGTH. Its checksum accounting never writes the header flag. -/
theorem inflate_CHECK_flags_two
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s state : InflateState} {l regs : IL}
    {bs : List UInt8} {outcome : Except Ex Unit}
    (E : Env c h r zs z s)
    (invariant : DefaultFlagJ h r zs z s)
    (buffers : DispatchBuffers h r l bs)
    (mode : s.mode = CHECK)
    (run : runX (inflate_CHECK c) l h = .ok ((outcome, regs), after))
    (getAfter : after.istates zs = some state) :
    state.flags = -1 ∨ state.flags = 0 := by
  by_cases raw : s.wrap = 0
  · have lengthRun := inflate_LENGTH_skip (l := l) E.st
      (show (setI h zs { s with mode := LENGTH }).istates zs =
        some { s with mode := LENGTH } by simp)
      (Or.inl raw)
    have whole := (inflate_CHECK_nowrap E.st E.hs raw).trans lengthRun
    rw [run] at whole
    cases whole
    have stateEq : { { s with mode := LENGTH } with mode := DONE } =
        state := by
      simpa only [setI, upd_same, Option.some.injEq] using getAfter
    rw [← stateEq]
    exact invariant.defaultFlags
  · have flags : s.flags = 0 :=
      (invariant.trailer (Or.inl mode)).resolve_left raw
    have statics : Zlib.Crc32.Proofs.StaticsOK h := by
      unfold Zlib.Crc32.Proofs.StaticsOK
      rw [invariant.globals]
      exact ⟨rfl, rfl⟩
    obtain ⟨rr, current, used, pull, _, _, _, _, _, _, _, _, _, kinds, _⟩ :=
      NEEDBITS_run_cursor buffers.bits 32 (by decide)
    obtain ⟨result, regs1, count, read, _, _, _, waitRun, fullRun⟩ :=
      inflate_CHECK_views_run (l.out_ - l.left) rfl E.strm E.st
        E.hz E.hs raw buffers.bits statics
        (fun _ => leaveOutputView_of_cursor invariant.good buffers.output)
    rw [pull] at read
    cases read
    rcases kinds with normal | wait
    · obtain ⟨_, value, rejected, accepted⟩ := fullRun normal
      let chargedState := chkS s (l.out_ - l.left) value
      let chargedHeap := chkH h r zs z s (l.out_ - l.left) value
      by_cases invalid : (s.wrap &&& 4) ≠ 0 ∧
          (if s.flags ≠ 0 then current.hold else ZSWAP32 current.hold) ≠
            chargedState.check
      · obtain ⟨index, _, badRun⟩ := rejected invalid.1 invalid.2
        rw [run] at badRun
        cases badRun
        have stateEq : { chargedState with mode := BAD } = state := by
          simpa only [tcBadHeap, setI, upd_same, Option.some.injEq]
            using getAfter
        rw [← stateEq]
        exact Or.inr (by simpa [chargedState, chkS] using flags)
      · have stateGet :
            (setI chargedHeap zs { chargedState with mode := LENGTH }).istates zs =
              some { chargedState with mode := LENGTH } := by simp
        have lengthRun := inflate_LENGTH_skip
          (l := { current with out_ := l.left, hold := 0, bits := 0 })
          E.st stateGet
          (Or.inr (show ({ chargedState with mode := LENGTH } :
            InflateState).flags = 0 from flags))
        have whole := (accepted invalid).trans lengthRun
        rw [run] at whole
        cases whole
        have stateEq :
            { { chargedState with mode := LENGTH } with mode := DONE } =
              state := by
          simpa only [setI, upd_same, Option.some.injEq] using getAfter
        rw [← stateEq]
        exact Or.inr (by simpa [chargedState, chkS] using flags)
    · obtain ⟨_, _, _, stopped⟩ := waitRun wait
      rw [run] at stopped
      cases stopped
      have stateEq : s = state :=
        Option.some.inj (E.hs.symm.trans getAfter)
      rw [← stateEq]
      exact invariant.defaultFlags

/-- CHECK retains the full default flag relation on every dispatch exit. -/
theorem inflate_dispatch_CHECK_default_flag {c : Ctx} {h : Heap}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s)
    (invariant : DefaultFlagJ h r zs z s)
    (buffers : DispatchBuffers h r l bs)
    (mode : s.mode = CHECK) (incoming : l.bits.toNat ≤ 39) :
    ∃ outcome regs after stream state,
      runX (inflate_dispatch c) l h = .ok ((outcome, regs), after) ∧
      DefaultFlagJ after r zs stream state := by
  obtain ⟨outcome, regs, after, stream, state, used, bound, run,
    current, packet, sizes, next, count, put, left, bits, static,
    progress⟩ :=
    inflate_CHECK_default_state_rank E invariant.toDefaultStateJ
      buffers mode incoming
  have flags := inflate_CHECK_flags_two E invariant buffers mode
    run current.good.live.hs
  have shape := inflate_CHECK_default_return_shape E
    invariant.toDefaultStateJ buffers mode run current.good.live.hs
  have search : state.mode = SYNC → state.«have».toNat ≤ 4 := by
    intro synced
    rcases shape with ⟨_, _, same, _⟩ | ⟨_, _, bad, _⟩ |
      ⟨_, _, done, _⟩
    · rw [same, mode] at synced
      have different : CHECK ≠ SYNC := by decide
      exact False.elim (different synced)
    · rw [bad] at synced
      have different : BAD ≠ SYNC := by decide
      exact False.elim (different synced)
    · rw [done] at synced
      have different : DONE ≠ SYNC := by decide
      exact False.elim (different synced)
  exact ⟨outcome, regs, after, stream, state,
    (inflate_dispatch_CHECK E l mode).trans run,
    ⟨⟨current, search⟩, flags⟩⟩

/-- Table construction keeps the header flag through its actual LEN_
continuation, including the fast decoder entry when enabled. -/
theorem inflate_dispatch_CONSTRUCTION_flags_two {c : Ctx} {h : Heap}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s)
    (invariant : DefaultFlagJ h r zs z s)
    (buffers : DispatchBuffers h r l bs)
    (mode : s.mode = TABLE ∨ s.mode = LENLENS ∨ s.mode = CODELENS)
    (raw : RawFastIO l) :
    ∃ outcome regs after stream state,
      runX (inflate_dispatch c) l h = .ok ((outcome, regs), after) ∧
      Good after r zs stream state ∧
      (state.flags = -1 ∨ state.flags = 0) := by
  obtain ⟨regs, after, stream, state, used, bound, nextJ, config,
    packet, sizes, cursor, count, put, left, total, bits, budget,
    stopped | continued⟩ :=
    inflate_dispatch_construction_state_boundary E
      invariant.toDefaultStateJ buffers mode
  · obtain ⟨outcome, run, why⟩ := stopped
    exact ⟨outcome, regs, after, stream, state, run, nextJ.good,
      by rw [config.2.2.2]; exact invariant.defaultFlags⟩
  · obtain ⟨nextMode, source⟩ := continued
    by_cases trees : c.flush = Z_TREES
    · rw [if_pos trees] at source
      exact ⟨.error Ex.leave, regs, after, stream, state, source,
        nextJ.good, by rw [config.2.2.2]; exact invariant.defaultFlags⟩
    · rw [if_neg trees] at source
      have nextEnv : Env c after r zs stream state :=
        ⟨E.strm, E.st, nextJ.good.live.hz, nextJ.good.live.hs⟩
      have dataMode : DataTableMode state.mode := by
        rw [nextMode]
        unfold DataTableMode
        decide
      have nextRaw := raw.advance cursor
        (show regs.put = inputAdvance l.put 0 by
          rw [put, inputAdvance_zero])
      obtain ⟨outcome, finalRegs, finalHeap, finalStream,
        finalState, run, good, frame⟩ :=
        inflate_dispatch_data_configuration nextEnv
          nextJ.toDefaultDecodeJ packet dataMode (fun _ => nextRaw)
      have actual : runX (inflate_dispatch c) l h =
          .ok ((outcome, finalRegs), finalHeap) :=
        source.trans
          ((inflate_dispatch_LEN_start nextEnv regs nextMode).symm.trans
            run)
      have finalFlags : finalState.flags = -1 ∨
          finalState.flags = 0 := by
        rw [frame.2.2.2, config.2.2.2]
        exact invariant.defaultFlags
      exact ⟨outcome, finalRegs, finalHeap, finalStream, finalState,
        actual, good, finalFlags⟩

/-- Stored-block dispatch retains the header flag while parsing or copying
stored bytes, and all its exits stay outside SYNC. -/
theorem inflate_dispatch_STORED_default_flag {c : Ctx} {h : Heap}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s)
    (invariant : DefaultFlagJ h r zs z s)
    (buffers : DispatchBuffers h r l bs)
    (mode : s.mode = STORED ∨ s.mode = COPY_ ∨ s.mode = COPY)
    (incoming : l.bits.toNat ≤ 39) :
    ∃ outcome regs after stream state,
      runX (inflate_dispatch c) l h = .ok ((outcome, regs), after) ∧
      DefaultFlagJ after r zs stream state := by
  obtain ⟨outcome, regs, after, stream, state, used, made, bound, run,
    current, modes, packet, sizes, frame, next, count, put, left,
    bits, progress, static, shape⟩ :=
    inflate_dispatch_stored_state_rank E invariant.toDefaultStateJ buffers
      mode incoming
  have flags : state.flags = -1 ∨ state.flags = 0 := by
    rw [frame]
    exact invariant.defaultFlags
  have boundCount : state.mode = SYNC → state.«have».toNat ≤ 4 := by
    intro synced
    rcases modes with selected | selected | selected | selected | selected <;>
      rw [selected] at synced <;> contradiction
  exact ⟨outcome, regs, after, stream, state, run,
    ⟨⟨current, boundCount⟩, flags⟩⟩

/-- Data-mode dispatch preserves the header flag through the checked
configuration frame and cannot enter SYNC. -/
theorem inflate_dispatch_DATA_default_flag {c : Ctx} {h : Heap}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s)
    (invariant : DefaultFlagJ h r zs z s)
    (buffers : DispatchBuffers h r l bs)
    (mode : DataTableMode s.mode)
    (raw : (s.mode = LEN_ ∨ s.mode = LEN) ∧
      (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true → RawFastIO l) :
    ∃ outcome regs after stream state,
      runX (inflate_dispatch c) l h = .ok ((outcome, regs), after) ∧
      DefaultFlagJ after r zs stream state := by
  obtain ⟨outcome, regs, after, stream, state, used, made, bound, run,
    current, modes, packet, sizes, next, count, put, left, bits,
    progress⟩ :=
    inflate_dispatch_data_state_rank E invariant.toDefaultStateJ buffers
      mode raw
  obtain ⟨otherOutcome, otherRegs, otherHeap, otherStream,
    otherState, otherRun, otherGood, config⟩ :=
    inflate_dispatch_data_configuration E invariant.toDefaultDecodeJ
      buffers mode raw
  rw [run] at otherRun
  cases otherRun
  have sameState : otherState = state :=
    Option.some.inj (otherGood.live.hs.symm.trans current.good.live.hs)
  subst otherState
  have flags : state.flags = -1 ∨ state.flags = 0 := by
    rw [config.2.2.2]
    exact invariant.defaultFlags
  have boundCount : state.mode = SYNC → state.«have».toNat ≤ 4 := by
    intro synced
    rcases modes with
      (selected | selected | selected | selected | selected | selected | selected) |
      selected | selected <;>
      rw [selected] at synced <;> contradiction
  exact ⟨outcome, regs, after, stream, state, run,
    ⟨⟨current, boundCount⟩, flags⟩⟩

/-- Terminal dispatch changes neither the heap nor the decoder record. -/
theorem inflate_dispatch_TERMINAL_default_flag {c : Ctx} {h : Heap}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s)
    (invariant : DefaultFlagJ h r zs z s)
    (buffers : DispatchBuffers h r l bs)
    (mode : TerminalMode s.mode) :
    runX (inflate_dispatch c) l h =
      .ok ((terminalExit s.mode, terminalRegs s.mode l), h) ∧
      DefaultFlagJ h r zs z s := by
  exact ⟨(inflate_dispatch_terminal_state E invariant.toDefaultStateJ
    buffers mode).1, invariant⟩

/-- The LENGTH trailer exit writes only DONE and retains the flag. -/
theorem inflate_LENGTH_default_flag {c : Ctx} {h : Heap}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s)
    (invariant : DefaultFlagJ h r zs z s)
    (buffers : DispatchBuffers h r l bs)
    (mode : s.mode = LENGTH) :
    runX (inflate_LENGTH c) l h =
      .ok ((.error Ex.leave, { l with ret := Z_STREAM_END }),
        setI h zs { s with mode := DONE }) ∧
      DefaultFlagJ (setI h zs { s with mode := DONE }) r zs z
        { s with mode := DONE } := by
  obtain ⟨run, current, _, _⟩ :=
    inflate_LENGTH_default_state_boundary E invariant.toDefaultStateJ
      buffers mode
  have bound : ({ s with mode := DONE } : InflateState).mode = SYNC →
      ({ s with mode := DONE } : InflateState).«have».toNat ≤ 4 := by
    intro impossible
    have different : DONE ≠ SYNC := by decide
    exact False.elim (different impossible)
  have flags : ({ s with mode := DONE } : InflateState).flags = -1 ∨
      ({ s with mode := DONE } : InflateState).flags = 0 := by
    simpa using invariant.defaultFlags
  exact ⟨run, ⟨⟨current, bound⟩, flags⟩⟩

/-- Every actual default dispatch branch retains one of the two header
flag values. The construction branch uses its checked configuration frame. -/
theorem inflate_dispatch_default_flags_two {c : Ctx} {h : Heap}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s)
    (invariant : DefaultFlagJ h r zs z s)
    (buffers : DispatchBuffers h r l bs)
    (raw : RawFastIO l) (incoming : l.bits.toNat ≤ 39) :
    ∃ outcome regs after stream state,
      runX (inflate_dispatch c) l h = .ok ((outcome, regs), after) ∧
      Good after r zs stream state ∧
      (state.flags = -1 ∨ state.flags = 0) := by
  rcases defaultMode_cases invariant.modes with
    head | dictionary | block | stored | construction | data |
    trailer | terminal
  · obtain ⟨outcome, regs, after, stream, state, run, current⟩ :=
      inflate_dispatch_HEAD_default_flag E invariant buffers head incoming
    exact ⟨outcome, regs, after, stream, state, run,
      current.good, current.defaultFlags⟩
  · obtain ⟨outcome, regs, after, stream, state, run, current⟩ :=
      inflate_dispatch_DICTIONARY_default_flag E invariant buffers
        dictionary incoming
    exact ⟨outcome, regs, after, stream, state, run,
      current.good, current.defaultFlags⟩
  · obtain ⟨outcome, regs, after, stream, state, run, current⟩ :=
      inflate_dispatch_TYPE_default_flag E invariant buffers block incoming
    exact ⟨outcome, regs, after, stream, state, run,
      current.good, current.defaultFlags⟩
  · obtain ⟨outcome, regs, after, stream, state, run, current⟩ :=
      inflate_dispatch_STORED_default_flag E invariant buffers stored incoming
    exact ⟨outcome, regs, after, stream, state, run,
      current.good, current.defaultFlags⟩
  · exact inflate_dispatch_CONSTRUCTION_flags_two E invariant buffers
      construction raw
  · obtain ⟨outcome, regs, after, stream, state, run, current⟩ :=
      inflate_dispatch_DATA_default_flag E invariant buffers data
        (fun _ => raw)
    exact ⟨outcome, regs, after, stream, state, run,
      current.good, current.defaultFlags⟩
  · rcases trailer with check | length
    · obtain ⟨outcome, regs, after, stream, state, run, current⟩ :=
        inflate_dispatch_CHECK_default_flag E invariant buffers check incoming
      exact ⟨outcome, regs, after, stream, state, run,
        current.good, current.defaultFlags⟩
    · obtain ⟨run, current⟩ :=
        inflate_LENGTH_default_flag E invariant buffers length
      exact ⟨.error Ex.leave, { l with ret := Z_STREAM_END },
        setI h zs { s with mode := DONE }, z, { s with mode := DONE },
        (inflate_dispatch_LENGTH E l length).trans run,
        current.good, current.defaultFlags⟩
  · obtain ⟨run, current⟩ :=
      inflate_dispatch_TERMINAL_default_flag E invariant buffers terminal
    exact ⟨terminalExit s.mode, terminalRegs s.mode l,
      h, z, s, run, current.good, current.defaultFlags⟩

/-- Every continuing default dispatch step preserves the complete flag and
sync-search relation. A normal result is at or below BAD, so SYNC is absent. -/
theorem inflate_dispatch_default_flag_normal
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z stream : ZStream} {s state : InflateState}
    {l regs : IL} {bs : List UInt8}
    (E : Env c h r zs z s)
    (invariant : DefaultFlagJ h r zs z s)
    (buffers : DispatchBuffers h r l bs)
    (raw : RawFastIO l) (incoming : l.bits.toNat ≤ 39)
    (run : runX (inflate_dispatch c) l h =
      .ok ((.ok (), regs), after))
    (current : DefaultStateJ after r zs stream state) :
    DefaultFlagJ after r zs stream state := by
  obtain ⟨outcome, otherRegs, otherHeap, otherStream,
    otherState, otherRun, otherGood, otherFlags⟩ :=
    inflate_dispatch_default_flags_two E invariant buffers raw incoming
  rw [run] at otherRun
  cases otherRun
  have sameState : otherState = state :=
    Option.some.inj
      (otherGood.live.hs.symm.trans current.good.live.hs)
  subst otherState
  have modeBound : state.mode ≤ BAD :=
    inflate_dispatch_default_normal_mode E invariant.toDefaultStateJ
      buffers raw incoming run current.good.live.hs
  have search : state.mode = SYNC → state.«have».toNat ≤ 4 := by
    intro synced
    have low : state.mode.toNat ≤ BAD.toNat :=
      UInt32.le_iff_toNat_le.mp modeBound
    rw [synced] at low
    have high : BAD.toNat < SYNC.toNat := by decide
    omega
  exact ⟨⟨current, search⟩, otherFlags⟩

/-- Actual default initialization starts before the zlib header. -/
theorem inflate_default_flag_initial (h : Heap) (r : ZStreamRef) (version : BPtr)
    (domain : InitDomain h r version) (platform : ZlibF.PlatformMemory.ByteObjectsFit h)
    (allocation : h.allocOk h.nalloc = true) :
    ∃ after z s, C.run (inflateInit_ (some r) version 112) h = .ok (Z_OK, after) ∧
      DefaultFlagJ after r h.nextBlk z s ∧ StreamReachable .inflate after r := by
  obtain ⟨after, z, s, run, current, flags, reachable⟩ :=
    inflate_default_sync_flags_initial h r version domain platform allocation
  exact ⟨after, z, s, run, ⟨current, Or.inl flags⟩, reachable⟩

/-- Caller buffer replacement does not change the decoder's header flag. -/
theorem rebuffer_default_flag_history {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (reachable : StreamReachable .inflate h r)
    (invariant : DefaultFlagJ h r zs z s)
    (edit : Rebuffer h after r) (platform : ZlibF.PlatformMemory.ByteObjectsFit after) :
    ∃ stream, DefaultFlagJ after r zs stream s ∧
      StreamReachable .inflate after r := by
  obtain ⟨stream, current⟩ :=
    rebuffer_default_sync invariant.toDefaultSyncJ edit platform
  exact ⟨stream, ⟨current, invariant.defaultFlags⟩,
    StreamReachable.rebuffer reachable edit⟩

/-- The three scalar queries leave the complete flag relation unchanged. -/
theorem inflateSyncPoint_default_flag_state {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (invariant : DefaultFlagJ h r zs z s) :
    (Call.inflateSyncPoint (some r)).execute default h =
      .ok (((if s.mode = STORED ∧ s.bits = 0 then (1 : Int32) else (0 : Int32)),
        default), h) ∧ DefaultFlagJ h r zs z s := by
  obtain ⟨run, _⟩ := inflateSyncPoint_default_state invariant.toDefaultStateJ
  exact ⟨run, invariant⟩

theorem inflateMark_default_flag_state {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (invariant : DefaultFlagJ h r zs z s) :
    ∃ value, (Call.inflateMark (some r)).execute default h =
      .ok ((value, default), h) ∧ DefaultFlagJ h r zs z s := by
  obtain ⟨value, run, _, _⟩ := inflateMark_default_state invariant.toDefaultStateJ
  exact ⟨value, run, invariant⟩

theorem inflateCodesUsed_default_flag_state {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (invariant : DefaultFlagJ h r zs z s) :
    ∃ used, used ≤ 1444 ∧
      (Call.inflateCodesUsed (some r)).execute default h =
        .ok ((UInt64.ofNat used, default), h) ∧ DefaultFlagJ h r zs z s := by
  obtain ⟨used, bound, run, _⟩ :=
    inflateCodesUsed_default_state invariant.toDefaultStateJ
  exact ⟨used, bound, run, invariant⟩

/-- A default zlib stream refuses a gzip header without changing its state;
the actual refusal extends the legal call history. -/
theorem inflateGetHeader_default_flag_history {h : Heap} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState}
    (reachable : StreamReachable .inflate h r)
    (invariant : DefaultFlagJ h r zs z s) (head : GzHeaderPtr)
    (arguments : StreamArguments h r (.inflateGetHeader (some r) head)) :
    C.run (inflateGetHeader (some r) head) h = .ok (Z_STREAM_ERROR, h) ∧
    DefaultFlagJ h r zs z s ∧ StreamReachable .inflate h r := by
  have run := (inflateGetHeader_default_J invariant.toDefaultDecodeJ head).1
  have executed : (Call.inflateGetHeader (some r) head).execute default h =
      .ok ((Z_STREAM_ERROR, default), h) := by
    change inflateGetHeader (some r) head h = _ at run
    simp only [Call.execute, heapCall, run]
  have operation : StreamOperation .inflate r (.inflateGetHeader (some r) head) := by
    simp [StreamOperation]
  exact ⟨run, invariant,
    StreamReachable.step reachable operation arguments executed⟩

/-- The selected build refuses `inflateUndermine` without changing the
decoder or its flag relation. -/
theorem inflateUndermine_default_flag_history {h : Heap} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState}
    (reachable : StreamReachable .inflate h r)
    (invariant : DefaultFlagJ h r zs z s) (subvert : Int32)
    (arguments : StreamArguments h r (.inflateUndermine (some r) subvert)) :
    C.run (inflateUndermine (some r) subvert) h = .ok (Z_DATA_ERROR, h) ∧
    DefaultFlagJ h r zs z s ∧ StreamReachable .inflate h r := by
  have run := (inflateUndermine_default_J invariant.toDefaultDecodeJ subvert).1
  have executed : (Call.inflateUndermine (some r) subvert).execute default h =
      .ok ((Z_DATA_ERROR, default), h) := by
    change inflateUndermine (some r) subvert h = _ at run
    simp only [Call.execute, heapCall, run]
  have operation : StreamOperation .inflate r (.inflateUndermine (some r) subvert) := by
    simp [StreamOperation]
  exact ⟨run, invariant,
    StreamReachable.step reachable operation arguments executed⟩

/-- Reset-keep writes the unread-header value on its actual returned state. -/
theorem inflateResetKeep_default_flag_history {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (reachable : StreamReachable .inflate h r)
    (invariant : DefaultFlagJ h r zs z s) (allocator : DefAlloc z) :
    ∃ after stream state, C.run (inflateResetKeep (some r)) h = .ok (Z_OK, after) ∧
      DefaultFlagJ after r zs stream state ∧ DefAlloc stream ∧
      StreamReachable .inflate after r := by
  obtain ⟨after, stream, state, run, current, finalAllocator, next⟩ :=
    inflateResetKeep_default_sync_history reachable invariant.toDefaultSyncJ allocator
  obtain ⟨after0, run0, _, good0, _⟩ := inflateResetKeep_safe invariant.good
  have sameHeap : after = after0 :=
    congrArg Prod.snd (Except.ok.inj (run.symm.trans run0))
  rw [← sameHeap] at good0
  have sameState : state = resetKeepState zs s :=
    Option.some.inj (current.good.live.hs.symm.trans good0.live.hs)
  have flag : state.flags = -1 := by rw [sameState]; rfl
  exact ⟨after, stream, state, run, ⟨current, Or.inl flag⟩,
    finalAllocator, next⟩

/-- Ordinary reset re-establishes the unread-header flag. -/
theorem inflateReset_default_flag_history {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (reachable : StreamReachable .inflate h r)
    (invariant : DefaultFlagJ h r zs z s) (allocator : DefAlloc z) :
    ∃ after stream state, C.run (inflateReset (some r)) h = .ok (Z_OK, after) ∧
      DefaultFlagJ after r zs stream state ∧ DefAlloc stream ∧
      StreamReachable .inflate after r := by
  obtain ⟨after, stream, state, run, current, finalAllocator, next⟩ :=
    inflateReset_default_sync_history reachable invariant.toDefaultSyncJ allocator
  obtain ⟨after0, run0, _, good0, _⟩ :=
    inflateReset_safe invariant.good allocator.2
  have sameHeap : after = after0 :=
    congrArg Prod.snd (Except.ok.inj (run.symm.trans run0))
  rw [← sameHeap] at good0
  have sameState : state = resetKeepState zs (resetPre s) :=
    Option.some.inj (current.good.live.hs.symm.trans good0.live.hs)
  have flag : state.flags = -1 := by rw [sameState]; rfl
  exact ⟨after, stream, state, run, ⟨current, Or.inl flag⟩,
    finalAllocator, next⟩

/-- Default-parameter reset2 also re-establishes the unread-header flag. -/
theorem inflateReset2_15_default_flag_history {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (reachable : StreamReachable .inflate h r)
    (invariant : DefaultFlagJ h r zs z s) (allocator : DefAlloc z) :
    ∃ after stream state, C.run (inflateReset2 (some r) 15) h = .ok (Z_OK, after) ∧
      DefaultFlagJ after r zs stream state ∧ DefAlloc stream ∧
      StreamReachable .inflate after r := by
  obtain ⟨after, stream, state, run, current, finalAllocator, next⟩ :=
    inflateReset2_15_default_sync_history reachable invariant.toDefaultSyncJ allocator
  obtain ⟨_, after0, run0, result⟩ :=
    inflateReset2_safe invariant.good allocator.2 15
  have params : reset2Params 15 = some (5, 15) := by decide
  rw [params] at result
  obtain ⟨_, _, good0, _⟩ := result
  have sameHeap : after = after0 :=
    congrArg Prod.snd (Except.ok.inj (run.symm.trans run0))
  rw [← sameHeap] at good0
  have sameState : state = resetKeepState zs (resetPre (reset2Pre 5 15 s)) :=
    Option.some.inj (current.good.live.hs.symm.trans good0.live.hs)
  have flag : state.flags = -1 := by rw [sameState]; rfl
  exact ⟨after, stream, state, run, ⟨current, Or.inl flag⟩,
    finalAllocator, next⟩

/-- Validation changes only wrapper-checking bits, not header status. -/
theorem inflateValidate_default_flag_history {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (reachable : StreamReachable .inflate h r)
    (invariant : DefaultFlagJ h r zs z s) (check : Int32) :
    ∃ after state, C.run (inflateValidate (some r) check) h = .ok (Z_OK, after) ∧
      DefaultFlagJ after r zs z state ∧ StreamReachable .inflate after r := by
  obtain ⟨after, state, run, current, next⟩ :=
    inflateValidate_default_sync_history reachable invariant.toDefaultSyncJ check
  obtain ⟨after0, state0, run0, _, stateEq, good0⟩ :=
    inflateValidate_default_state invariant.toDefaultStateJ check
  have sameHeap : after = after0 :=
    congrArg Prod.snd (Except.ok.inj (run.symm.trans run0))
  rw [← sameHeap] at good0
  have sameState : state = state0 :=
    Option.some.inj (current.good.live.hs.symm.trans good0.good.live.hs)
  have flag : state.flags = -1 ∨ state.flags = 0 := by
    rw [sameState, stateEq]
    simpa [validateState] using invariant.defaultFlags
  exact ⟨after, state, run, ⟨current, flag⟩, next⟩

/-- Reading the current dictionary leaves the private state unchanged. -/
theorem inflateGetDictionary_default_flag_history {h : Heap} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState}
    (reachable : StreamReachable .inflate h r)
    (invariant : DefaultFlagJ h r zs z s) (dest : BPtr) (dl : Option UInt32)
    (arguments : StreamArguments h r (.inflateGetDictionary (some r) dest dl)) :
    ∃ value after, C.run (inflateGetDictionary (some r) dest dl) h =
      .ok (value, after) ∧ DefaultFlagJ after r zs z s ∧
      StreamReachable .inflate after r := by
  obtain ⟨value, after, run, current, next⟩ :=
    inflateGetDictionary_default_sync_history reachable invariant.toDefaultSyncJ
      dest dl arguments
  exact ⟨value, after, run, ⟨current, invariant.defaultFlags⟩, next⟩

/-- The no-input sync return does not change header status. -/
theorem inflateSync_default_buf_flag_history {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (reachable : StreamReachable .inflate h r)
    (invariant : DefaultFlagJ h r zs z s)
    (noInput : z.avail_in = 0) (fewBits : s.bits < 8)
    (arguments : StreamArguments h r (.inflateSync (some r))) :
    C.run (inflateSync (some r)) h = .ok (Z_BUF_ERROR, tmpFreed h) ∧
    DefaultFlagJ (tmpFreed h) r zs z s ∧
    StreamReachable .inflate (tmpFreed h) r := by
  obtain ⟨run, current, next⟩ :=
    inflateSync_default_buf_history reachable invariant.toDefaultSyncJ
      noInput fewBits arguments
  exact ⟨run, ⟨current, invariant.defaultFlags⟩, next⟩

/-- Continued unsuccessful scanning changes the count, not header flags. -/
theorem inflateSync_resume_default_flag_history {h : Heap} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState} {bytes seen : List UInt8}
    (reachable : StreamReachable .inflate h r)
    (invariant : DefaultFlagJ h r zs z s) (allocator : DefAlloc z)
    (mode : s.mode = SYNC) (progress : ¬ (z.avail_in = 0 ∧ s.bits < 8))
    (input : SyncIn h z.next_in z.avail_in bytes)
    (atSpec : SyncAt s.«have» seen)
    (arguments : StreamArguments h r (.inflateSync (some r))) :
    ∃ N G, N.toNat ≤ z.avail_in.toNat ∧
      (G ≠ 4 → ∃ after,
        C.run (inflateSync (some r)) h = .ok (Z_DATA_ERROR, after) ∧
        DefaultFlagJ after r zs (syncAdvance z N) (syncHave s G) ∧
        StreamReachable .inflate after r) := by
  obtain ⟨N, G, used, bad⟩ :=
    inflateSync_resume_default_bad_history reachable invariant.toDefaultSyncJ
      allocator mode progress input atSpec arguments
  refine ⟨N, G, used, ?_⟩
  intro missed
  obtain ⟨after, run, current, next⟩ := bad missed
  have flags : (syncHave s G).flags = -1 ∨ (syncHave s G).flags = 0 := by
    simpa [syncHave] using invariant.defaultFlags
  exact ⟨after, run, ⟨current, flags⟩, next⟩

/-- The first unsuccessful search also retains the header flag. -/
theorem inflateSync_first_default_flag_history {h : Heap} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState} {bytes : List UInt8}
    (reachable : StreamReachable .inflate h r)
    (invariant : DefaultFlagJ h r zs z s) (allocator : DefAlloc z)
    (mode : s.mode ≠ SYNC) (progress : ¬ (z.avail_in = 0 ∧ s.bits < 8))
    (input : SyncIn h z.next_in z.avail_in bytes)
    (arguments : StreamArguments h r (.inflateSync (some r))) :
    ∃ N G, N.toNat ≤ z.avail_in.toNat ∧
      (G ≠ 4 → ∃ after,
        C.run (inflateSync (some r)) h = .ok (Z_DATA_ERROR, after) ∧
        DefaultFlagJ after r zs (syncAdvance z N)
          (syncHave (syncFirstState s) G) ∧
        StreamReachable .inflate after r) := by
  obtain ⟨N, G, used, bad⟩ :=
    inflateSync_first_default_bad_history reachable invariant.toDefaultSyncJ
      allocator mode progress input arguments
  refine ⟨N, G, used, ?_⟩
  intro missed
  obtain ⟨after, run, current, next⟩ := bad missed
  have flags : (syncHave (syncFirstState s) G).flags = -1 ∨
      (syncHave (syncFirstState s) G).flags = 0 := by
    simpa [syncHave, syncFirstState] using invariant.defaultFlags
  exact ⟨after, run, ⟨current, flags⟩, next⟩

/-- Every signed prime request changes at most the held-bit fields; the
actual refusal and clearing paths also retain header status. -/
theorem inflatePrime_default_flag_history {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (reachable : StreamReachable .inflate h r)
    (invariant : DefaultFlagJ h r zs z s) (allocator : DefAlloc z)
    (bits value : Int32) :
    ∃ rc after state, C.run (inflatePrime (some r) bits value) h = .ok (rc, after) ∧
      DefaultFlagJ after r zs z state ∧ DefAlloc z ∧
      StreamReachable .inflate after r := by
  obtain ⟨rc, after, state, run, current, finalAllocator, next⟩ :=
    inflatePrime_default_sync_history reachable invariant.toDefaultSyncJ
      allocator bits value
  obtain ⟨zero, clear, reject, insert⟩ := inflatePrime_spec invariant.good bits value
  have flags : state.flags = -1 ∨ state.flags = 0 := by
    by_cases eq0 : bits = 0
    · have run0 := zero eq0
      have sameHeap : after = h :=
        congrArg Prod.snd (Except.ok.inj (run.symm.trans run0))
      subst after
      have sameState : state = s :=
        Option.some.inj (current.good.live.hs.symm.trans invariant.good.live.hs)
      simpa [sameState] using invariant.defaultFlags
    · by_cases neg : bits < 0
      · obtain ⟨run0, good0⟩ := clear neg
        have sameHeap : after = setI h zs { s with hold := 0, bits := 0 } :=
          congrArg Prod.snd (Except.ok.inj (run.symm.trans run0))
        rw [sameHeap] at current
        have sameState : state = { s with hold := 0, bits := 0 } :=
          Option.some.inj (current.good.live.hs.symm.trans good0.live.hs)
        simpa [sameState] using invariant.defaultFlags
      · have pos : 0 < bits := by
          rw [Int32.lt_iff_toInt_lt] at neg ⊢
          change ¬ bits.toInt < 0 at neg
          change 0 < bits.toInt
          have notZero : bits.toInt ≠ 0 := by
            intro eq
            apply eq0
            exact Int32.toInt_inj.mp eq
          omega
        by_cases wide : 16 < bits.toInt
        · have run0 := reject pos (Or.inl wide)
          have sameHeap : after = h :=
            congrArg Prod.snd (Except.ok.inj (run.symm.trans run0))
          subst after
          have sameState : state = s :=
            Option.some.inj (current.good.live.hs.symm.trans invariant.good.live.hs)
          simpa [sameState] using invariant.defaultFlags
        · by_cases full : 32 < s.bits.toNat + bits.toInt.toNat
          · have run0 := reject pos (Or.inr full)
            have sameHeap : after = h :=
              congrArg Prod.snd (Except.ok.inj (run.symm.trans run0))
            subst after
            have sameState : state = s :=
              Option.some.inj (current.good.live.hs.symm.trans invariant.good.live.hs)
            simpa [sameState] using invariant.defaultFlags
          · obtain ⟨run0, good0⟩ := insert pos (by omega) (by omega)
            have sameHeap : after = setI h zs (primeState bits value s) :=
              congrArg Prod.snd (Except.ok.inj (run.symm.trans run0))
            rw [sameHeap] at current
            have sameState : state = primeState bits value s :=
              Option.some.inj (current.good.live.hs.symm.trans good0.live.hs)
            simpa [sameState, primeState] using invariant.defaultFlags
  exact ⟨rc, after, state, run, ⟨current, flags⟩, finalAllocator, next⟩

/-- Window installation and its allocation-failure path leave header
status unchanged. This is the state transition inside dictionary setup. -/
theorem updatewindow_default_flag_state {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {off : Nat} {source : BRef}
    {bytes : Array UInt8} {copy : UInt32}
    (invariant : DefaultFlagJ h r zs z s) (allocator : DefAlloc z)
    (get : Space.get h source = some bytes) (fit : off + copy.toNat ≤ bytes.size)
    (separate : Separate (.ref source off) copy.toNat s.window (2 ^ s.wbits.toNat)) :
    ∃ rc after state,
      C.run (updatewindow (some r) (.ref source (off + copy.toNat)) copy) h = .ok (rc, after) ∧
      DefaultFlagJ after r zs z state ∧ (rc = 0 ∨ rc = 1) := by
  obtain ⟨rc, after, state, run, current, outcome⟩ :=
    updatewindow_default_sync_state invariant.toDefaultSyncJ allocator get fit separate
  have sep : Separate (.ref source ((off + copy.toNat) - copy.toNat)) copy.toNat
      s.window (2 ^ s.wbits.toNat) := by simpa using separate
  obtain ⟨rc0, after0, state0, run0, good0, cases⟩ :=
    updatewindow_safe_public invariant.good allocator.1 get (by omega) fit sep
  have sameHeap : after = after0 :=
    congrArg Prod.snd (Except.ok.inj (run.symm.trans run0))
  rw [← sameHeap] at good0 run0
  have sameState : state = state0 :=
    Option.some.inj (current.good.live.hs.symm.trans good0.live.hs)
  have flags : state.flags = -1 ∨ state.flags = 0 := by
    rw [sameState]
    rcases cases with ⟨zero, _⟩ | ⟨one, window, failed, heapEq, stateEq⟩
    · have frame := updatewindow_state_frame_public invariant.good allocator.1
        get fit separate (by simpa only [zero] using run0) good0.live.hs
      rw [frame]
      simpa using invariant.defaultFlags
    · rw [stateEq]
      exact invariant.defaultFlags
  exact ⟨rc, after, state, run, ⟨current, flags⟩, outcome⟩

theorem DefaultFlagJ.set_havedict {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (invariant : DefaultFlagJ h r zs z s) :
    DefaultFlagJ (setI h zs { s with havedict := 1 }) r zs z
      { s with havedict := 1 } := by
  exact ⟨invariant.toDefaultSyncJ.set_havedict,
    by simpa using invariant.defaultFlags⟩

theorem DefaultFlagJ.mem_update {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z stream : ZStream} {s : InflateState} (invariant : DefaultFlagJ h r zs z s)
    (good : Good after r zs stream { s with mode := MEM })
    (platform : ZlibF.PlatformMemory.ByteObjectsFit after)
    (static : after.static = h.static) :
    DefaultFlagJ after r zs stream { s with mode := MEM } := by
  exact ⟨invariant.toDefaultSyncJ.mem_update good platform static,
    by simpa using invariant.defaultFlags⟩

/-- Accepted dictionary installation preserves the flag relation through
both the successful window copy and the genuine allocation failure. -/
theorem inflateSetDictionary_accepted_default_flag_state {H : Heap}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {st : InflateState}
    {off : Nat} {source : BRef} {D : Array UInt8} {L : UInt32}
    (invariant : DefaultFlagJ H r zs z st) (allocator : DefAlloc z)
    (hD : Space.get H source = some D) (hfit : off + L.toNat ≤ D.size)
    (hsep : Separate (.ref source off) L.toNat st.window (2 ^ st.wbits.toNat))
    (hwrap : st.wrap = 0 ∨ st.mode = DICT)
    (hadler : st.mode = DICT →
      (ZlibF.Spec.adler32 (Zlib.Adler32.Proofs.seg D off L.toNat)).toUInt64 = st.check) :
    ∃ rc after state,
      C.run (inflateSetDictionary (some r) (.ref source off) L) H = .ok (rc, after) ∧
      DefaultFlagJ after r zs z state ∧ DefAlloc z := by
  have hG := invariant.good
  have hL := hG.live
  obtain ⟨v0, H1, st1, hr1, current, _⟩ :=
    updatewindow_default_flag_state invariant allocator hD hfit hsep
  have hadd' : Ptr.add (Ptr.ref source off) (L.toNat : Int) H =
      .ok (Ptr.ref source (off + L.toNat), H) := Ptr.add_nat_ok hD hfit
  have hnn : (Ptr.ref source off == (Ptr.null : BPtr)) = false := by simp
  have hr1' : updatewindow (some r) (Ptr.ref source (off + L.toNat)) L H =
      .ok (v0, H1) := hr1
  have hrun : inflateSetDictionary (some r) (.ref source off) L H =
      (if v0 = 0 then .ok (Z_OK, setI H1 zs { st1 with havedict := 1 })
       else .ok (Z_MEM_ERROR, setI H1 zs { st1 with mode := MEM })) := by
    have hs1 : H1.istates zs = some st1 := current.good.live.hs
    unfold inflateSetDictionary
    simp only [bind_app, stateCheck_live hL, ldZ_eq, ldI_eq, hL.hz, hL.zst, castI, hL.hs, hnn,
      bne_self_eq_false, Bool.or_self, Bool.false_eq_true, ite_false]
    by_cases hm : st.mode = DICT
    · have hra := adler32_dict_any hD L hfit
      have hck := hadler hm
      have hmb : (st.mode == DICT) = true := by simpa using hm
      simp only [hmb, adler32_init, hra, hck, bne_self_eq_false, hadd', hr1', ite_true,
        Bool.false_eq_true, ite_false, Bool.and_false, hmb, hm, beq_self_eq_true]
      simp only [bind_app, adler32_init, hra, hck, bne_self_eq_false, hadd', hr1',
        Bool.false_eq_true, ite_false, setMode, wrI_eq, hs1]
      by_cases hv0 : v0 = 0
      · simp only [hv0, bne_self_eq_false, Bool.false_eq_true, ite_false, ite_true,
          bind_app, wrI_eq, hs1, pure_app, setI]
      · have hb : (v0 != 0) = true := by simpa using hv0
        simp only [hb, ite_true, hv0, ite_false, setMode, bind_app, wrI_eq, hs1, pure_app, setI]
    · have hw0 : st.wrap = 0 := by rcases hwrap with h | h; exact h; exact absurd h hm
      have hmb : (st.mode == DICT) = false := by simpa using hm
      simp only [hmb, hw0, hadd', hr1', bne_self_eq_false, Bool.false_and,
        Bool.false_eq_true, ite_false, Bool.and_false]
      simp only [bind_app, hadd', hr1', Bool.false_eq_true, ite_false, setMode, wrI_eq, hs1]
      by_cases hv0 : v0 = 0
      · simp only [hv0, bne_self_eq_false, Bool.false_eq_true, ite_false, ite_true,
          bind_app, wrI_eq, hs1, pure_app, setI]
      · have hb : (v0 != 0) = true := by simpa using hv0
        simp only [hb, ite_true, hv0, ite_false, setMode, bind_app, wrI_eq, hs1, pure_app, setI]
  by_cases zero : v0 = 0
  · exact ⟨Z_OK, _, _, by rw [C.run, hrun, if_pos zero], current.set_havedict,
      allocator⟩
  · have good := good_state (st' := { st1 with mode := MEM }) current.good rfl mode_mem
      (current.good.inv.of_fields rfl rfl rfl rfl rfl rfl rfl rfl rfl current.good.inv.bits
        rfl rfl rfl)
    exact ⟨Z_MEM_ERROR, _, _, by rw [C.run, hrun, if_neg zero],
      current.mem_update good (current.platform.with_istates _) rfl, allocator⟩

/-- Every publicly admitted dictionary request preserves the flag relation
on acceptance, refusal, checksum failure and allocation failure. -/
theorem inflateSetDictionary_default_flag_history {h : Heap} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState}
    (reachable : StreamReachable .inflate h r)
    (invariant : DefaultFlagJ h r zs z s) (allocator : DefAlloc z)
    (source : BPtr) (n : UInt32)
    (arguments : StreamArguments h r (.inflateSetDictionary (some r) source n)) :
    ∃ rc after state, C.run (inflateSetDictionary (some r) source n) h = .ok (rc, after) ∧
      DefaultFlagJ after r zs z state ∧ DefAlloc z ∧
      StreamReachable .inflate after r := by
  have range : CallerRange h r source n.toNat false := arguments
  obtain ⟨xs, readable⟩ : ∃ xs, source ≠ .null → Bytes h source n.toNat xs := by
    rcases range with null | ⟨⟨xs, bytes⟩, _, _⟩
    · exact ⟨[], by intro nonnull; exact False.elim (nonnull null)⟩
    · exact ⟨xs, by intro _; exact bytes⟩
  have separate := callerRange_dictionary_window_separate invariant.good range
  have result : ∃ rc after state,
      C.run (inflateSetDictionary (some r) source n) h = .ok (rc, after) ∧
      DefaultFlagJ after r zs z state ∧ DefAlloc z := by
    by_cases null : source = .null
    · exact ⟨Z_STREAM_ERROR, h, s,
        inflateSetDictionary_refused_any invariant.good.live source n (Or.inl null),
        invariant, allocator⟩
    by_cases permitted : s.wrap = 0 ∨ s.mode = DICT
    · rcases readable null with impossible | ⟨ref, off, array, pointer, get, fit, value⟩
      · exact False.elim (null impossible.1)
      subst source
      by_cases wrong : s.mode = DICT ∧
          (ZlibF.Spec.adler32 (Zlib.Adler32.Proofs.seg array off n.toNat)).toUInt64 ≠ s.check
      · exact ⟨Z_DATA_ERROR, h, s,
          inflateSetDictionary_dataerr_any invariant.good.live get fit wrong.1 wrong.2,
          invariant, allocator⟩
      · have accepted : s.mode = DICT →
            (ZlibF.Spec.adler32 (Zlib.Adler32.Proofs.seg array off n.toNat)).toUInt64 = s.check := by
          intro mode
          by_cases equal : (ZlibF.Spec.adler32 (Zlib.Adler32.Proofs.seg array off n.toNat)).toUInt64 = s.check
          · exact equal
          · exact False.elim (wrong ⟨mode, equal⟩)
        obtain ⟨rc, after, state, run, current, finalAllocator⟩ :=
          inflateSetDictionary_accepted_default_flag_state invariant allocator get fit separate
            permitted accepted
        exact ⟨rc, after, state, run, current, finalAllocator⟩
    · have refused : s.wrap ≠ 0 ∧ s.mode ≠ DICT := by
        constructor
        · exact fun equal => permitted (Or.inl equal)
        · exact fun equal => permitted (Or.inr equal)
      exact ⟨Z_STREAM_ERROR, h, s,
        inflateSetDictionary_refused_any invariant.good.live source n (Or.inr refused),
        invariant, allocator⟩
  obtain ⟨rc, after, state, run, current, finalAllocator⟩ := result
  have executed : (Call.inflateSetDictionary (some r) source n).execute default h =
      .ok ((rc, default), after) := by
    change inflateSetDictionary (some r) source n h = _ at run
    simp only [Call.execute, heapCall, run]
  have operation : StreamOperation .inflate r (.inflateSetDictionary (some r) source n) := by
    simp [StreamOperation]
  exact ⟨rc, after, state, run, current, finalAllocator,
    StreamReachable.step reachable operation arguments executed⟩

theorem syncOkState_flags (zs : Nat) (s : InflateState) :
    (syncOkState zs s).flags = s.flags := by
  have hc : (syncC zs s).flags = s.flags := by
    unfold syncC
    split <;> simp [resetKeepState]
  by_cases hw : (syncC zs s).wbits == 0
  · simp [syncOkState, hw, hc]
  · simp [syncOkState, hw, hc]

/-- The marker-found reset carries the complete default history relation
from the searched state to the returned heap. -/
theorem DefaultStateJ.sync_found_flag {H : Heap} {r : ZStreamRef}
    {zs block : Nat} {z : ZStream} {s : InflateState}
    (invariant : DefaultStateJ H r zs z s)
    (flags : s.flags = -1 ∨ s.flags = 0)
    (good : Good
      (freeWin (syncOkHeap H r zs z s) (.ref (.blk block) 0))
      r zs (syncOkStream z s) (syncOkState zs s))
    (platform : ZlibF.PlatformMemory.ByteObjectsFit H) :
    DefaultFlagJ
      (freeWin (syncOkHeap H r zs z s) (.ref (.blk block) 0))
      r zs (syncOkStream z s) (syncOkState zs s) := by
  have sameBits : s.wbits = s.reqbits :=
    invariant.window.trans invariant.requestedBits.symm
  have finalPlatform := platform_sync_done_free
    (H := H) (r := r) (zs := zs) (block := block) (z := z) (s := s)
    platform sameBits invariant.requestedBits
  have finalStatic :
      (freeWin (syncOkHeap H r zs z s) (.ref (.blk block) 0)).static = H.static := by
    rw [show (freeWin (syncOkHeap H r zs z s)
      (.ref (.blk block) 0)).static = (syncOkHeap H r zs z s).static by rfl]
    exact static_syncOkHeap_default H r zs z s sameBits invariant.requestedBits
  have done := invariant.sync_done flags good finalPlatform finalStatic
  have bound : (syncOkState zs s).mode = SYNC →
      (syncOkState zs s).«have».toNat ≤ 4 := by
    intro equal
    have typeMode : (syncOkState zs s).mode = TYPE := by simp [syncOkState]
    rw [typeMode] at equal
    cases equal
  have finalFlags : (syncOkState zs s).flags = -1 ∨
      (syncOkState zs s).flags = 0 := by
    simpa [syncOkState_flags] using flags
  exact ⟨⟨done, bound⟩, finalFlags⟩

/-- A resumed search that finds the marker returns from the actual C model
with the default TYPE invariant and a legal successor history. -/
theorem inflateSync_resume_default_flag_success {h : Heap} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState} {bytes seen : List UInt8}
    (reachable : StreamReachable .inflate h r)
    (invariant : DefaultFlagJ h r zs z s) (allocator : DefAlloc z)
    (mode : s.mode = SYNC) (progress : ¬ (z.avail_in = 0 ∧ s.bits < 8))
    (input : SyncIn h z.next_in z.avail_in bytes)
    (atSpec : SyncAt s.«have» seen)
    (arguments : StreamArguments h r (.inflateSync (some r))) :
    ∃ N G, N.toNat ≤ z.avail_in.toNat ∧
      (G = 4 → ∃ after,
        C.run (inflateSync (some r)) h = .ok (Z_OK, after) ∧
        DefaultFlagJ after r zs
          (syncOkStream (syncAdvance z N) (syncHave s G))
          (syncOkState zs (syncHave s G)) ∧
        StreamReachable .inflate after r) := by
  obtain ⟨N, G, used, _, _, _, success⟩ :=
    inflateSync_resume invariant.good allocator.2 mode progress input atSpec
  refine ⟨N, G, used, ?_⟩
  intro found
  obtain ⟨after, run, shape, good⟩ := success found
  subst after
  let H := setI (r.put (syncAlloc h) (syncAdvance z N)) zs (syncHave s G)
  have initial : DefaultStateJ (syncAlloc h) r zs z s :=
    default_state_syncAlloc invariant.toDefaultStateJ
  have searched : DefaultStateJ H r zs (syncAdvance z N) (syncHave s G) :=
    initial.sync_resume_bad mode
      (good_syncSearch (good_syncAlloc invariant.good) N G)
      (platform_sync_resume_base invariant.platform)
      (by simpa only [H, syncAlloc_static] using
        static_sync_resume_base h r zs z s N G)
  have sameBits : (syncHave s G).wbits = (syncHave s G).reqbits := by
    simpa [syncHave] using invariant.window.trans invariant.requestedBits.symm
  have requested : (syncHave s G).reqbits = 15 := by
    simpa [syncHave] using invariant.requestedBits
  have finalPlatform := platform_sync_done_free
    (H := H) (r := r) (zs := zs) (block := h.nextBlk)
    (z := syncAdvance z N) (s := syncHave s G)
    (platform_sync_resume_base invariant.platform) sameBits requested
  have finalStatic :
      (freeWin (syncOkHeap H r zs (syncAdvance z N) (syncHave s G))
        (syncBuf h)).static = H.static := by
    rw [show (freeWin (syncOkHeap H r zs (syncAdvance z N) (syncHave s G))
      (syncBuf h)).static =
      (syncOkHeap H r zs (syncAdvance z N) (syncHave s G)).static by rfl]
    exact static_syncOkHeap_default H r zs (syncAdvance z N) (syncHave s G)
      sameBits requested
  have flags : (syncHave s G).flags = -1 ∨ (syncHave s G).flags = 0 := by
    simpa [syncHave] using invariant.defaultFlags
  have done : DefaultStateJ
      (freeWin (syncOkHeap H r zs (syncAdvance z N) (syncHave s G))
        (syncBuf h)) r zs
      (syncOkStream (syncAdvance z N) (syncHave s G))
      (syncOkState zs (syncHave s G)) :=
    searched.sync_done flags good finalPlatform finalStatic
  have bound : (syncOkState zs (syncHave s G)).mode = SYNC →
      (syncOkState zs (syncHave s G)).«have».toNat ≤ 4 := by
    intro equal
    have typeMode : (syncOkState zs (syncHave s G)).mode = TYPE := by
      simp [syncOkState]
    rw [typeMode] at equal
    cases equal
  have finalFlags : (syncOkState zs (syncHave s G)).flags = -1 ∨
      (syncOkState zs (syncHave s G)).flags = 0 := by
    simpa [syncOkState_flags] using flags
  have executed : (Call.inflateSync (some r)).execute default h =
      .ok ((Z_OK, default),
        freeWin (syncOkHeap H r zs (syncAdvance z N) (syncHave s G))
          (syncBuf h)) := by
    change inflateSync (some r) h = _ at run
    dsimp [H]
    simp only [Call.execute, heapCall, run]
  have operation : StreamOperation .inflate r (.inflateSync (some r)) := by
    simp [StreamOperation]
  exact ⟨_, run, ⟨⟨done, bound⟩, finalFlags⟩,
    StreamReachable.step reachable operation arguments executed⟩

/-- A first search that finds the marker has the same checked TYPE successor,
including the restored held bytes and the freed temporary block. -/
theorem inflateSync_first_default_flag_success {h : Heap} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState} {bytes : List UInt8}
    (reachable : StreamReachable .inflate h r)
    (invariant : DefaultFlagJ h r zs z s) (allocator : DefAlloc z)
    (mode : s.mode ≠ SYNC) (progress : ¬ (z.avail_in = 0 ∧ s.bits < 8))
    (input : SyncIn h z.next_in z.avail_in bytes)
    (arguments : StreamArguments h r (.inflateSync (some r))) :
    ∃ N G, N.toNat ≤ z.avail_in.toNat ∧
      (G = 4 → ∃ after,
        C.run (inflateSync (some r)) h = .ok (Z_OK, after) ∧
        DefaultFlagJ after r zs
          (syncOkStream (syncAdvance z N) (syncHave (syncFirstState s) G))
          (syncOkState zs (syncHave (syncFirstState s) G)) ∧
        StreamReachable .inflate after r) := by
  obtain ⟨N, G, used, _, _, _, success⟩ :=
    inflateSync_first invariant.good allocator.2 mode progress input
  refine ⟨N, G, used, ?_⟩
  intro found
  obtain ⟨after, run, shape, good⟩ := success found
  subst after
  let H := setI
    (r.put (syncFirstHeap (syncAlloc h) zs h.nextBlk s (syncJunk h))
      (syncAdvance z N)) zs (syncHave (syncFirstState s) G)
  have distinct := win_ne_buf invariant.good.fresh invariant.good.inv.win
  have firstGood : Good
      (syncFirstHeap (syncAlloc h) zs h.nextBlk s (syncJunk h))
      r zs z (syncFirstState s) :=
    good_firstState (good_syncAlloc invariant.good) (syncAlloc_bytes_buf h) distinct
  have searched : DefaultStateJ H r zs (syncAdvance z N)
      (syncHave (syncFirstState s) G) :=
    invariant.toDefaultStateJ.sync_first_bad
      (good_syncSearch firstGood N G)
      (platform_sync_first_base invariant.platform)
      (by simpa only [H] using static_sync_first_base h r zs z s N G)
  have sameBits : (syncHave (syncFirstState s) G).wbits =
      (syncHave (syncFirstState s) G).reqbits := by
    simpa [syncHave, syncFirstState] using
      invariant.window.trans invariant.requestedBits.symm
  have requested : (syncHave (syncFirstState s) G).reqbits = 15 := by
    simpa [syncHave, syncFirstState] using invariant.requestedBits
  have finalPlatform := platform_sync_done_free
    (H := H) (r := r) (zs := zs) (block := h.nextBlk)
    (z := syncAdvance z N) (s := syncHave (syncFirstState s) G)
    (platform_sync_first_base invariant.platform) sameBits requested
  have finalStatic :
      (freeWin (syncOkHeap H r zs (syncAdvance z N)
        (syncHave (syncFirstState s) G)) (syncBuf h)).static = H.static := by
    rw [show (freeWin (syncOkHeap H r zs (syncAdvance z N)
      (syncHave (syncFirstState s) G)) (syncBuf h)).static =
      (syncOkHeap H r zs (syncAdvance z N)
        (syncHave (syncFirstState s) G)).static by rfl]
    exact static_syncOkHeap_default H r zs (syncAdvance z N)
      (syncHave (syncFirstState s) G) sameBits requested
  have flags : (syncHave (syncFirstState s) G).flags = -1 ∨
      (syncHave (syncFirstState s) G).flags = 0 := by
    simpa [syncHave, syncFirstState] using invariant.defaultFlags
  have done : DefaultStateJ
      (freeWin (syncOkHeap H r zs (syncAdvance z N)
        (syncHave (syncFirstState s) G)) (syncBuf h)) r zs
      (syncOkStream (syncAdvance z N) (syncHave (syncFirstState s) G))
      (syncOkState zs (syncHave (syncFirstState s) G)) :=
    searched.sync_done flags good finalPlatform finalStatic
  have bound : (syncOkState zs (syncHave (syncFirstState s) G)).mode = SYNC →
      (syncOkState zs (syncHave (syncFirstState s) G)).«have».toNat ≤ 4 := by
    intro equal
    have typeMode : (syncOkState zs (syncHave (syncFirstState s) G)).mode = TYPE := by
      simp [syncOkState]
    rw [typeMode] at equal
    cases equal
  have finalFlags : (syncOkState zs (syncHave (syncFirstState s) G)).flags = -1 ∨
      (syncOkState zs (syncHave (syncFirstState s) G)).flags = 0 := by
    simpa [syncOkState_flags] using flags
  have executed : (Call.inflateSync (some r)).execute default h =
      .ok ((Z_OK, default),
        freeWin (syncOkHeap H r zs (syncAdvance z N)
          (syncHave (syncFirstState s) G)) (syncBuf h)) := by
    change inflateSync (some r) h = _ at run
    dsimp [H]
    simp only [Call.execute, heapCall, run]
  have operation : StreamOperation .inflate r (.inflateSync (some r)) := by
    simp [StreamOperation]
  exact ⟨_, run, ⟨⟨done, bound⟩, finalFlags⟩,
    StreamReachable.step reachable operation arguments executed⟩

/-- A resumed marker search with any represented public byte view returns
with the complete default history relation. -/
theorem inflateSync_resume_byte_view_flag_success {h : Heap} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState} {bytes seen : List UInt8}
    (reachable : StreamReachable .inflate h r)
    (invariant : DefaultFlagJ h r zs z s) (allocator : DefAlloc z)
    (mode : s.mode = SYNC) (progress : ¬ (z.avail_in = 0 ∧ s.bits < 8))
    (input : Bytes h z.next_in z.avail_in.toNat bytes)
    (atSpec : SyncAt s.«have» seen)
    (arguments : StreamArguments h r (.inflateSync (some r))) :
    ∃ N G, N.toNat ≤ z.avail_in.toNat ∧
      (G = 4 → ∃ after,
        C.run (inflateSync (some r)) h = .ok (Z_OK, after) ∧
        DefaultFlagJ after r zs
          (syncOkStream (syncAdvance z N) (syncHave s G))
          (syncOkState zs (syncHave s G)) ∧
        StreamReachable .inflate after r) := by
  obtain ⟨N, G, used, _, _, _, success⟩ :=
    inflateSync_resume_bytes invariant.good allocator.2 mode progress input atSpec
  refine ⟨N, G, used, ?_⟩
  intro found
  obtain ⟨after, run, shape, good⟩ := success found
  subst after
  let H := setI (r.put (syncAlloc h) (syncAdvance z N)) zs (syncHave s G)
  have initial := default_state_syncAlloc invariant.toDefaultStateJ
  have searched : DefaultStateJ H r zs (syncAdvance z N) (syncHave s G) :=
    initial.sync_resume_bad mode
      (good_syncSearch (good_syncAlloc invariant.good) N G)
      (platform_sync_resume_base invariant.platform)
      (by simpa only [H, syncAlloc_static] using
        static_sync_resume_base h r zs z s N G)
  have flags : (syncHave s G).flags = -1 ∨ (syncHave s G).flags = 0 := by
    simpa [syncHave] using invariant.defaultFlags
  have current : DefaultFlagJ
      (freeWin (syncOkHeap H r zs (syncAdvance z N) (syncHave s G))
        (syncBuf h)) r zs
      (syncOkStream (syncAdvance z N) (syncHave s G))
      (syncOkState zs (syncHave s G)) :=
    searched.sync_found_flag flags good
      (platform_sync_resume_base invariant.platform)
  have executed : (Call.inflateSync (some r)).execute default h =
      .ok ((Z_OK, default),
        freeWin (syncOkHeap H r zs (syncAdvance z N) (syncHave s G))
          (syncBuf h)) := by
    change inflateSync (some r) h = _ at run
    dsimp [H]
    simp only [Call.execute, heapCall, run]
  have operation : StreamOperation .inflate r (.inflateSync (some r)) := by
    simp [StreamOperation]
  exact ⟨_, run, current,
    StreamReachable.step reachable operation arguments executed⟩

/-- A first marker search with any represented public byte view has the
same complete default successor after restoring held bytes. -/
theorem inflateSync_first_byte_view_flag_success {h : Heap} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState} {bytes : List UInt8}
    (reachable : StreamReachable .inflate h r)
    (invariant : DefaultFlagJ h r zs z s) (allocator : DefAlloc z)
    (mode : s.mode ≠ SYNC) (progress : ¬ (z.avail_in = 0 ∧ s.bits < 8))
    (input : Bytes h z.next_in z.avail_in.toNat bytes)
    (arguments : StreamArguments h r (.inflateSync (some r))) :
    ∃ N G, N.toNat ≤ z.avail_in.toNat ∧
      (G = 4 → ∃ after,
        C.run (inflateSync (some r)) h = .ok (Z_OK, after) ∧
        DefaultFlagJ after r zs
          (syncOkStream (syncAdvance z N) (syncHave (syncFirstState s) G))
          (syncOkState zs (syncHave (syncFirstState s) G)) ∧
        StreamReachable .inflate after r) := by
  obtain ⟨N, G, used, _, _, _, success⟩ :=
    inflateSync_first_bytes invariant.good allocator.2 mode progress input
  refine ⟨N, G, used, ?_⟩
  intro found
  obtain ⟨after, run, shape, good⟩ := success found
  subst after
  let H := setI
    (r.put (syncFirstHeap (syncAlloc h) zs h.nextBlk s (syncJunk h))
      (syncAdvance z N)) zs (syncHave (syncFirstState s) G)
  have distinct := win_ne_buf invariant.good.fresh invariant.good.inv.win
  have firstGood : Good
      (syncFirstHeap (syncAlloc h) zs h.nextBlk s (syncJunk h))
      r zs z (syncFirstState s) :=
    good_firstState (good_syncAlloc invariant.good) (syncAlloc_bytes_buf h) distinct
  have searched : DefaultStateJ H r zs (syncAdvance z N)
      (syncHave (syncFirstState s) G) :=
    invariant.toDefaultStateJ.sync_first_bad
      (good_syncSearch firstGood N G)
      (platform_sync_first_base invariant.platform)
      (by simpa only [H] using static_sync_first_base h r zs z s N G)
  have flags : (syncHave (syncFirstState s) G).flags = -1 ∨
      (syncHave (syncFirstState s) G).flags = 0 := by
    simpa [syncHave, syncFirstState] using invariant.defaultFlags
  have current : DefaultFlagJ
      (freeWin (syncOkHeap H r zs (syncAdvance z N)
        (syncHave (syncFirstState s) G)) (syncBuf h)) r zs
      (syncOkStream (syncAdvance z N) (syncHave (syncFirstState s) G))
      (syncOkState zs (syncHave (syncFirstState s) G)) :=
    searched.sync_found_flag flags good
      (platform_sync_first_base invariant.platform)
  have executed : (Call.inflateSync (some r)).execute default h =
      .ok ((Z_OK, default),
        freeWin (syncOkHeap H r zs (syncAdvance z N)
          (syncHave (syncFirstState s) G)) (syncBuf h)) := by
    change inflateSync (some r) h = _ at run
    dsimp [H]
    simp only [Call.execute, heapCall, run]
  have operation : StreamOperation .inflate r (.inflateSync (some r)) := by
    simp [StreamOperation]
  exact ⟨_, run, current,
    StreamReachable.step reachable operation arguments executed⟩

/-- A continued unsuccessful search preserves the complete history relation
for any represented public byte view. -/
theorem inflateSync_resume_byte_view_flag_miss {h : Heap} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState} {bytes seen : List UInt8}
    (reachable : StreamReachable .inflate h r)
    (invariant : DefaultFlagJ h r zs z s) (allocator : DefAlloc z)
    (mode : s.mode = SYNC) (progress : ¬ (z.avail_in = 0 ∧ s.bits < 8))
    (input : Bytes h z.next_in z.avail_in.toNat bytes)
    (atSpec : SyncAt s.«have» seen)
    (arguments : StreamArguments h r (.inflateSync (some r))) :
    ∃ N G, N.toNat ≤ z.avail_in.toNat ∧
      (G ≠ 4 → ∃ after,
        C.run (inflateSync (some r)) h = .ok (Z_DATA_ERROR, after) ∧
        DefaultFlagJ after r zs (syncAdvance z N) (syncHave s G) ∧
        StreamReachable .inflate after r) := by
  obtain ⟨N, G, used, _, rest, missed, _⟩ :=
    inflateSync_resume_bytes invariant.good allocator.2 mode progress input atSpec
  refine ⟨N, G, used, ?_⟩
  intro notFound
  obtain ⟨after, run, shape, good⟩ := missed notFound
  subst after
  have platform := platform_sync_resume_bad (r := r) (zs := zs)
    (z := z) (s := s) (N := N) (G := G) invariant.platform
  have static := static_sync_resume_bad h r zs z s N G
  have state := invariant.toDefaultStateJ.sync_resume_bad mode good platform static
  have bound : (syncHave s G).mode = SYNC →
      (syncHave s G).«have».toNat ≤ 4 := by
    intro _
    have count : G.toNat ≤ 4 := Nat.le_of_lt (rest notFound).2.1
    simpa [syncHave] using count
  have flags : (syncHave s G).flags = -1 ∨ (syncHave s G).flags = 0 := by
    simpa [syncHave] using invariant.defaultFlags
  have executed : (Call.inflateSync (some r)).execute default h =
      .ok ((Z_DATA_ERROR, default),
        freeWin (setI (r.put (syncAlloc h) (syncAdvance z N)) zs
          (syncHave s G)) (syncBuf h)) := by
    change inflateSync (some r) h = _ at run
    simp only [Call.execute, heapCall, run]
  have operation : StreamOperation .inflate r (.inflateSync (some r)) := by
    simp [StreamOperation]
  exact ⟨_, run, ⟨⟨state, bound⟩, flags⟩,
    StreamReachable.step reachable operation arguments executed⟩

/-- A first unsuccessful search preserves the same relation after restoring
its held bytes, for any represented public byte view. -/
theorem inflateSync_first_byte_view_flag_miss {h : Heap} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState} {bytes : List UInt8}
    (reachable : StreamReachable .inflate h r)
    (invariant : DefaultFlagJ h r zs z s) (allocator : DefAlloc z)
    (mode : s.mode ≠ SYNC) (progress : ¬ (z.avail_in = 0 ∧ s.bits < 8))
    (input : Bytes h z.next_in z.avail_in.toNat bytes)
    (arguments : StreamArguments h r (.inflateSync (some r))) :
    ∃ N G, N.toNat ≤ z.avail_in.toNat ∧
      (G ≠ 4 → ∃ after,
        C.run (inflateSync (some r)) h = .ok (Z_DATA_ERROR, after) ∧
        DefaultFlagJ after r zs (syncAdvance z N)
          (syncHave (syncFirstState s) G) ∧
        StreamReachable .inflate after r) := by
  obtain ⟨N, G, used, _, rest, missed, _⟩ :=
    inflateSync_first_bytes invariant.good allocator.2 mode progress input
  refine ⟨N, G, used, ?_⟩
  intro notFound
  obtain ⟨after, run, shape, good⟩ := missed notFound
  subst after
  have platform := platform_sync_first_bad (r := r) (zs := zs)
    (z := z) (s := s) (N := N) (G := G) invariant.platform
  have static := static_sync_first_bad h r zs z s N G
  have state := invariant.toDefaultStateJ.sync_first_bad good platform static
  have bound : (syncHave (syncFirstState s) G).mode = SYNC →
      (syncHave (syncFirstState s) G).«have».toNat ≤ 4 := by
    intro _
    have count : G.toNat ≤ 4 := Nat.le_of_lt (rest notFound).2.1
    simpa [syncHave] using count
  have flags : (syncHave (syncFirstState s) G).flags = -1 ∨
      (syncHave (syncFirstState s) G).flags = 0 := by
    simpa [syncHave, syncFirstState] using invariant.defaultFlags
  have executed : (Call.inflateSync (some r)).execute default h =
      .ok ((Z_DATA_ERROR, default),
        freeWin
          (setI
            (r.put (syncFirstHeap (syncAlloc h) zs h.nextBlk s (syncJunk h))
              (syncAdvance z N)) zs (syncHave (syncFirstState s) G))
          (syncBuf h)) := by
    change inflateSync (some r) h = _ at run
    simp only [Call.execute, heapCall, run]
  have operation : StreamOperation .inflate r (.inflateSync (some r)) := by
    simp [StreamOperation]
  exact ⟨_, run, ⟨⟨state, bound⟩, flags⟩,
    StreamReachable.step reachable operation arguments executed⟩

/-- Every continued search over a represented byte view returns with the
complete default relation, whether or not it finds the marker. -/
theorem inflateSync_resume_byte_view_flag_total {h : Heap} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState} {bytes seen : List UInt8}
    (reachable : StreamReachable .inflate h r)
    (invariant : DefaultFlagJ h r zs z s) (allocator : DefAlloc z)
    (mode : s.mode = SYNC) (progress : ¬ (z.avail_in = 0 ∧ s.bits < 8))
    (input : Bytes h z.next_in z.avail_in.toNat bytes)
    (atSpec : SyncAt s.«have» seen)
    (arguments : StreamArguments h r (.inflateSync (some r))) :
    ∃ rc after stream state,
      C.run (inflateSync (some r)) h = .ok (rc, after) ∧
      DefaultFlagJ after r zs stream state ∧
      StreamReachable .inflate after r := by
  obtain ⟨N, G, _, _, rest, missed, success⟩ :=
    inflateSync_resume_bytes invariant.good allocator.2 mode progress input atSpec
  by_cases complete : G = 4
  · obtain ⟨after, run, shape, good⟩ := success complete
    subst after
    let H := setI (r.put (syncAlloc h) (syncAdvance z N)) zs (syncHave s G)
    have initial := default_state_syncAlloc invariant.toDefaultStateJ
    have searched : DefaultStateJ H r zs (syncAdvance z N) (syncHave s G) :=
      initial.sync_resume_bad mode
        (good_syncSearch (good_syncAlloc invariant.good) N G)
        (platform_sync_resume_base invariant.platform)
        (by simpa only [H, syncAlloc_static] using
          static_sync_resume_base h r zs z s N G)
    have flags : (syncHave s G).flags = -1 ∨ (syncHave s G).flags = 0 := by
      simpa [syncHave] using invariant.defaultFlags
    have current : DefaultFlagJ
        (freeWin (syncOkHeap H r zs (syncAdvance z N) (syncHave s G))
          (syncBuf h)) r zs
        (syncOkStream (syncAdvance z N) (syncHave s G))
        (syncOkState zs (syncHave s G)) :=
      searched.sync_found_flag flags good
        (platform_sync_resume_base invariant.platform)
    have executed : (Call.inflateSync (some r)).execute default h =
        .ok ((Z_OK, default),
          freeWin (syncOkHeap H r zs (syncAdvance z N) (syncHave s G))
            (syncBuf h)) := by
      change inflateSync (some r) h = _ at run
      dsimp [H]
      simp only [Call.execute, heapCall, run]
    have operation : StreamOperation .inflate r (.inflateSync (some r)) := by
      simp [StreamOperation]
    exact ⟨Z_OK, _, _, _, run, current,
      StreamReachable.step reachable operation arguments executed⟩
  · obtain ⟨after, run, shape, good⟩ := missed complete
    subst after
    have platform := platform_sync_resume_bad (r := r) (zs := zs)
      (z := z) (s := s) (N := N) (G := G) invariant.platform
    have static := static_sync_resume_bad h r zs z s N G
    have state := invariant.toDefaultStateJ.sync_resume_bad mode good platform static
    have bound : (syncHave s G).mode = SYNC →
        (syncHave s G).«have».toNat ≤ 4 := by
      intro _
      have count : G.toNat ≤ 4 := Nat.le_of_lt (rest complete).2.1
      simpa [syncHave] using count
    have flags : (syncHave s G).flags = -1 ∨ (syncHave s G).flags = 0 := by
      simpa [syncHave] using invariant.defaultFlags
    have executed : (Call.inflateSync (some r)).execute default h =
        .ok ((Z_DATA_ERROR, default),
          freeWin (setI (r.put (syncAlloc h) (syncAdvance z N)) zs
            (syncHave s G)) (syncBuf h)) := by
      change inflateSync (some r) h = _ at run
      simp only [Call.execute, heapCall, run]
    have operation : StreamOperation .inflate r (.inflateSync (some r)) := by
      simp [StreamOperation]
    exact ⟨Z_DATA_ERROR, _, _, _, run, ⟨⟨state, bound⟩, flags⟩,
      StreamReachable.step reachable operation arguments executed⟩

/-- Every first search over a represented byte view also returns with the
complete default relation. -/
theorem inflateSync_first_byte_view_flag_total {h : Heap} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState} {bytes : List UInt8}
    (reachable : StreamReachable .inflate h r)
    (invariant : DefaultFlagJ h r zs z s) (allocator : DefAlloc z)
    (mode : s.mode ≠ SYNC) (progress : ¬ (z.avail_in = 0 ∧ s.bits < 8))
    (input : Bytes h z.next_in z.avail_in.toNat bytes)
    (arguments : StreamArguments h r (.inflateSync (some r))) :
    ∃ rc after stream state,
      C.run (inflateSync (some r)) h = .ok (rc, after) ∧
      DefaultFlagJ after r zs stream state ∧
      StreamReachable .inflate after r := by
  obtain ⟨N, G, _, _, rest, missed, success⟩ :=
    inflateSync_first_bytes invariant.good allocator.2 mode progress input
  by_cases complete : G = 4
  · obtain ⟨after, run, shape, good⟩ := success complete
    subst after
    let H := setI
      (r.put (syncFirstHeap (syncAlloc h) zs h.nextBlk s (syncJunk h))
        (syncAdvance z N)) zs (syncHave (syncFirstState s) G)
    have distinct := win_ne_buf invariant.good.fresh invariant.good.inv.win
    have firstGood : Good
        (syncFirstHeap (syncAlloc h) zs h.nextBlk s (syncJunk h))
        r zs z (syncFirstState s) :=
      good_firstState (good_syncAlloc invariant.good) (syncAlloc_bytes_buf h)
        distinct
    have searched : DefaultStateJ H r zs (syncAdvance z N)
        (syncHave (syncFirstState s) G) :=
      invariant.toDefaultStateJ.sync_first_bad
        (good_syncSearch firstGood N G)
        (platform_sync_first_base invariant.platform)
        (by simpa only [H] using static_sync_first_base h r zs z s N G)
    have flags : (syncHave (syncFirstState s) G).flags = -1 ∨
        (syncHave (syncFirstState s) G).flags = 0 := by
      simpa [syncHave, syncFirstState] using invariant.defaultFlags
    have current : DefaultFlagJ
        (freeWin (syncOkHeap H r zs (syncAdvance z N)
          (syncHave (syncFirstState s) G)) (syncBuf h)) r zs
        (syncOkStream (syncAdvance z N) (syncHave (syncFirstState s) G))
        (syncOkState zs (syncHave (syncFirstState s) G)) :=
      searched.sync_found_flag flags good
        (platform_sync_first_base invariant.platform)
    have executed : (Call.inflateSync (some r)).execute default h =
        .ok ((Z_OK, default),
          freeWin (syncOkHeap H r zs (syncAdvance z N)
            (syncHave (syncFirstState s) G)) (syncBuf h)) := by
      change inflateSync (some r) h = _ at run
      dsimp [H]
      simp only [Call.execute, heapCall, run]
    have operation : StreamOperation .inflate r (.inflateSync (some r)) := by
      simp [StreamOperation]
    exact ⟨Z_OK, _, _, _, run, current,
      StreamReachable.step reachable operation arguments executed⟩
  · obtain ⟨after, run, shape, good⟩ := missed complete
    subst after
    have platform := platform_sync_first_bad (r := r) (zs := zs)
      (z := z) (s := s) (N := N) (G := G) invariant.platform
    have static := static_sync_first_bad h r zs z s N G
    have state := invariant.toDefaultStateJ.sync_first_bad good platform static
    have bound : (syncHave (syncFirstState s) G).mode = SYNC →
        (syncHave (syncFirstState s) G).«have».toNat ≤ 4 := by
      intro _
      have count : G.toNat ≤ 4 := Nat.le_of_lt (rest complete).2.1
      simpa [syncHave] using count
    have flags : (syncHave (syncFirstState s) G).flags = -1 ∨
        (syncHave (syncFirstState s) G).flags = 0 := by
      simpa [syncHave, syncFirstState] using invariant.defaultFlags
    have executed : (Call.inflateSync (some r)).execute default h =
        .ok ((Z_DATA_ERROR, default),
          freeWin
            (setI
              (r.put (syncFirstHeap (syncAlloc h) zs h.nextBlk s (syncJunk h))
                (syncAdvance z N)) zs (syncHave (syncFirstState s) G))
            (syncBuf h)) := by
      change inflateSync (some r) h = _ at run
      simp only [Call.execute, heapCall, run]
    have operation : StreamOperation .inflate r (.inflateSync (some r)) := by
      simp [StreamOperation]
    exact ⟨Z_DATA_ERROR, _, _, _, run, ⟨⟨state, bound⟩, flags⟩,
      StreamReachable.step reachable operation arguments executed⟩

/-- Every actual sync return over a represented public input view retains
the complete default history relation. -/
theorem inflateSync_byte_view_flag_history {h : Heap} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState} {bytes : List UInt8}
    (reachable : StreamReachable .inflate h r)
    (invariant : DefaultFlagJ h r zs z s) (allocator : DefAlloc z)
    (input : Bytes h z.next_in z.avail_in.toNat bytes)
    (arguments : StreamArguments h r (.inflateSync (some r))) :
    ∃ rc after stream state,
      C.run (inflateSync (some r)) h = .ok (rc, after) ∧
      DefaultFlagJ after r zs stream state ∧
      StreamReachable .inflate after r := by
  by_cases short : z.avail_in = 0 ∧ s.bits < 8
  · obtain ⟨run, current, next⟩ :=
      inflateSync_default_buf_flag_history reachable invariant short.1 short.2
        arguments
    exact ⟨Z_BUF_ERROR, tmpFreed h, z, s, run, current, next⟩
  · by_cases inSync : s.mode = SYNC
    · obtain ⟨seen, atSpec⟩ := invariant.toDefaultSyncJ.syncAt inSync
      exact inflateSync_resume_byte_view_flag_total reachable invariant
        allocator inSync short input atSpec arguments
    · exact inflateSync_first_byte_view_flag_total reachable invariant
        allocator inSync short input arguments

/-- The public caller range supplies the byte-view packet whenever its
input is non-null or empty. The null-positive case is separate. -/
theorem inflateSync_public_input_flag_history {h : Heap} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState}
    (reachable : StreamReachable .inflate h r)
    (invariant : DefaultFlagJ h r zs z s) (allocator : DefAlloc z)
    (valid : z.next_in ≠ .null ∨ z.avail_in = 0)
    (arguments : StreamArguments h r (.inflateSync (some r))) :
    ∃ rc after stream state,
      C.run (inflateSync (some r)) h = .ok (rc, after) ∧
      DefaultFlagJ after r zs stream state ∧
      StreamReachable .inflate after r := by
  rcases valid with nonnull | empty
  · have argumentCopy := arguments
    obtain ⟨given, get, range⟩ := argumentCopy
    have same : given = z :=
      Option.some.inj (get.symm.trans invariant.good.live.hz)
    subst given
    obtain ⟨bytes, input⟩ :=
      syncBytes_of_callerRange (len := z.avail_in) range nonnull
    exact inflateSync_byte_view_flag_history reachable invariant allocator
      input arguments
  · by_cases null : z.next_in = .null
    · have input : Bytes h z.next_in z.avail_in.toNat [] :=
        Or.inl ⟨null, by simp [empty], rfl⟩
      exact inflateSync_byte_view_flag_history reachable invariant allocator
        input arguments
    · have argumentCopy := arguments
      obtain ⟨given, get, range⟩ := argumentCopy
      have same : given = z :=
        Option.some.inj (get.symm.trans invariant.good.live.hz)
      subst given
      obtain ⟨bytes, input⟩ :=
        syncBytes_of_callerRange (len := z.avail_in) range null
      exact inflateSync_byte_view_flag_history reachable invariant allocator
        input arguments

/-- A resumed search with `have = 4` may legally succeed with null input and
a positive count because it reads no byte. The returned TYPE state retains J. -/
theorem inflateSync_resume_null_found_flag_history {h : Heap} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState}
    (reachable : StreamReachable .inflate h r)
    (invariant : DefaultFlagJ h r zs z s) (allocator : DefAlloc z)
    (mode : s.mode = SYNC) (positive : z.avail_in ≠ 0)
    (null : z.next_in = .null) (found : s.«have» = 4)
    (arguments : StreamArguments h r (.inflateSync (some r))) :
    ∃ after stream state,
      C.run (inflateSync (some r)) h = .ok (Z_OK, after) ∧
      DefaultFlagJ after r zs stream state ∧
      StreamReachable .inflate after r := by
  let H := setI (r.put (syncAlloc h) (syncAdvance z 0)) zs (syncHave s 4)
  have run := inflateSync_resume_null_found invariant.good allocator.2
    mode positive null found
  have searchGood : Good H r zs (syncAdvance z 0) (syncHave s 4) :=
    good_syncSearch (good_syncAlloc invariant.good) 0 4
  have distinct := win_ne_buf invariant.good.fresh invariant.good.inv.win
  have finalGood : Good
      (freeWin (syncOkHeap H r zs (syncAdvance z 0) (syncHave s 4))
        (syncBuf h)) r zs
      (syncOkStream (syncAdvance z 0) (syncHave s 4))
      (syncOkState zs (syncHave s 4)) :=
    good_freeBuf (syncDone_good searchGood).1
      (fun w window => distinct w
        (by simpa [syncHave] using syncOkState_window_ref window))
  have initial := default_state_syncAlloc invariant.toDefaultStateJ
  have searched : DefaultStateJ H r zs (syncAdvance z 0) (syncHave s 4) :=
    initial.sync_resume_bad mode searchGood
      (platform_sync_resume_base invariant.platform)
      (by simpa only [H, syncAlloc_static] using
        static_sync_resume_base h r zs z s 0 4)
  have flags : (syncHave s 4).flags = -1 ∨ (syncHave s 4).flags = 0 := by
    simpa [syncHave] using invariant.defaultFlags
  have current := searched.sync_found_flag flags finalGood
    (platform_sync_resume_base invariant.platform)
  have executed : (Call.inflateSync (some r)).execute default h =
      .ok ((Z_OK, default),
        freeWin (syncOkHeap H r zs (syncAdvance z 0) (syncHave s 4))
          (syncBuf h)) := by
    change inflateSync (some r) h = _ at run
    dsimp [H]
    simp only [Call.execute, heapCall, run]
  have operation : StreamOperation .inflate r (.inflateSync (some r)) := by
    simp [StreamOperation]
  exact ⟨_, _, _, run, current,
    StreamReachable.step reachable operation arguments executed⟩

/-- The first search can also succeed with null caller input when its held
bytes complete the marker; the returned TYPE state retains J. -/
theorem inflateSync_first_null_found_flag_history {h : Heap} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState}
    (reachable : StreamReachable .inflate h r)
    (invariant : DefaultFlagJ h r zs z s) (allocator : DefAlloc z)
    (mode : s.mode ≠ SYNC) (positive : z.avail_in ≠ 0)
    (null : z.next_in = .null)
    (found : (syncFirstState s).«have» = 4)
    (arguments : StreamArguments h r (.inflateSync (some r))) :
    ∃ after stream state,
      C.run (inflateSync (some r)) h = .ok (Z_OK, after) ∧
      DefaultFlagJ after r zs stream state ∧
      StreamReachable .inflate after r := by
  let H := setI
    (r.put (syncFirstHeap (syncAlloc h) zs h.nextBlk s (syncJunk h))
      (syncAdvance z 0)) zs (syncHave (syncFirstState s) 4)
  have run := inflateSync_first_null_found invariant.good allocator.2
    mode positive null found
  have distinct := win_ne_buf invariant.good.fresh invariant.good.inv.win
  have firstGood : Good
      (syncFirstHeap (syncAlloc h) zs h.nextBlk s (syncJunk h))
      r zs z (syncFirstState s) :=
    good_firstState (good_syncAlloc invariant.good) (syncAlloc_bytes_buf h)
      distinct
  have searchGood : Good H r zs (syncAdvance z 0)
      (syncHave (syncFirstState s) 4) :=
    good_syncSearch firstGood 0 4
  have finalGood : Good
      (freeWin (syncOkHeap H r zs (syncAdvance z 0)
        (syncHave (syncFirstState s) 4)) (syncBuf h)) r zs
      (syncOkStream (syncAdvance z 0) (syncHave (syncFirstState s) 4))
      (syncOkState zs (syncHave (syncFirstState s) 4)) :=
    good_freeBuf (syncDone_good searchGood).1
      (fun w window => distinct w
        (by simpa [syncHave, syncFirstState] using
          syncOkState_window_ref window))
  have searched : DefaultStateJ H r zs (syncAdvance z 0)
      (syncHave (syncFirstState s) 4) :=
    invariant.toDefaultStateJ.sync_first_bad searchGood
      (platform_sync_first_base invariant.platform)
      (by simpa only [H] using static_sync_first_base h r zs z s 0 4)
  have flags : (syncHave (syncFirstState s) 4).flags = -1 ∨
      (syncHave (syncFirstState s) 4).flags = 0 := by
    simpa [syncHave, syncFirstState] using invariant.defaultFlags
  have current := searched.sync_found_flag flags finalGood
    (platform_sync_first_base invariant.platform)
  have executed : (Call.inflateSync (some r)).execute default h =
      .ok ((Z_OK, default),
        freeWin (syncOkHeap H r zs (syncAdvance z 0)
          (syncHave (syncFirstState s) 4)) (syncBuf h)) := by
    change inflateSync (some r) h = _ at run
    dsimp [H]
    simp only [Call.execute, heapCall, run]
  have operation : StreamOperation .inflate r (.inflateSync (some r)) := by
    simp [StreamOperation]
  exact ⟨_, _, _, run, current,
    StreamReachable.step reachable operation arguments executed⟩

/-- A successful null-positive sync history must have found the marker
before reading caller input; the other executions fault and cannot be steps. -/
theorem inflateSync_null_positive_success_flag_history {h after : Heap}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {rc : Int32}
    (reachable : StreamReachable .inflate h r)
    (invariant : DefaultFlagJ h r zs z s) (allocator : DefAlloc z)
    (null : z.next_in = .null) (positive : z.avail_in ≠ 0)
    (arguments : StreamArguments h r (.inflateSync (some r)))
    (run : C.run (inflateSync (some r)) h = .ok (rc, after)) :
    ∃ stream state, DefaultFlagJ after r zs stream state ∧
      StreamReachable .inflate after r := by
  by_cases mode : s.mode = SYNC
  · obtain ⟨seen, atSpec⟩ := invariant.toDefaultSyncJ.syncAt mode
    rcases atSpec with scanning | ⟨found, _⟩
    · have small : s.«have» < 4 := by
        rw [UInt32.lt_iff_toNat_lt]
        exact scanning.1
      have fault := inflateSync_resume_null_positive_fault invariant.good
        mode positive null small
      rw [fault] at run
      cases run
    · obtain ⟨result, stream, state, run0, current, next⟩ :=
        inflateSync_resume_null_found_flag_history reachable invariant
          allocator mode positive null found arguments
      have same : after = result :=
        congrArg Prod.snd (Except.ok.inj (run.symm.trans run0))
      rw [same]
      exact ⟨stream, state, current, next⟩
  · have atSpec : SyncAt (syncFirstState s).«have» (syncRestore s) := by
      simpa [syncFirstState] using syncAt_restore s
    rcases atSpec with scanning | ⟨found, _⟩
    · have small : (syncFirstState s).«have» < 4 := by
        rw [UInt32.lt_iff_toNat_lt]
        exact scanning.1
      have fault := inflateSync_first_null_positive_fault invariant.good
        mode positive null small
      rw [fault] at run
      cases run
    · obtain ⟨result, stream, state, run0, current, next⟩ :=
        inflateSync_first_null_found_flag_history reachable invariant
          allocator mode positive null found arguments
      have same : after = result :=
        congrArg Prod.snd (Except.ok.inj (run.symm.trans run0))
      rw [same]
      exact ⟨stream, state, current, next⟩

/-- Every successful public `inflateSync` step from a default history
preserves the complete relation, including null-positive caller bindings. -/
theorem inflateSync_success_default_flag_history {h after : Heap}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {rc : Int32}
    (reachable : StreamReachable .inflate h r)
    (invariant : DefaultFlagJ h r zs z s) (allocator : DefAlloc z)
    (arguments : StreamArguments h r (.inflateSync (some r)))
    (run : C.run (inflateSync (some r)) h = .ok (rc, after)) :
    ∃ stream state, DefaultFlagJ after r zs stream state ∧
      StreamReachable .inflate after r := by
  by_cases valid : z.next_in ≠ .null ∨ z.avail_in = 0
  · obtain ⟨rc0, result, stream, state, run0, current, next⟩ :=
      inflateSync_public_input_flag_history reachable invariant allocator
        valid arguments
    have same : after = result :=
      congrArg Prod.snd (Except.ok.inj (run.symm.trans run0))
    rw [same]
    exact ⟨stream, state, current, next⟩
  · have null : z.next_in = .null := by
      by_cases equal : z.next_in = .null
      · exact equal
      · exact False.elim (valid (Or.inl equal))
    have positive : z.avail_in ≠ 0 := by
      intro empty
      exact valid (Or.inr empty)
    exact inflateSync_null_positive_success_flag_history reachable invariant
      allocator null positive arguments run

end Zlib.Inflate.Proofs
