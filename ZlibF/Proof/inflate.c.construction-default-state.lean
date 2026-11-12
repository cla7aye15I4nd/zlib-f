import ZlibF.Proof.«inflate.c.stored-default-state»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

theorem DefaultConfigFrame.trans {a b c : InflateState} (first : DefaultConfigFrame a b)
    (second : DefaultConfigFrame b c) : DefaultConfigFrame a c :=
  ⟨second.1.trans first.1, second.2.1.trans first.2.1,
    second.2.2.1.trans first.2.2.1, second.2.2.2.1.trans first.2.2.2.1,
    second.2.2.2.2.trans first.2.2.2.2⟩

/-- Concrete configuration retention upgrades a checked decoder result to
its full reset/header history relation. The completed-header fact is
produced at the active incoming mode, not assumed of a callee. -/
theorem DefaultStateJ.config_update {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z stream : ZStream} {s state : InflateState} (invariant : DefaultStateJ h r zs z s)
    (current : DefaultDecodeJ after r zs stream state) (frame : DefaultConfigFrame s state)
    (format : HeaderDone s) : DefaultStateJ after r zs stream state := by
  have nextFormat : HeaderDone state := by unfold HeaderDone at format ⊢; rw [frame.2.2.1, frame.2.2.2.1]; exact format
  exact ⟨current, invariant.requestedBits.congr frame.1 frame.2.2.2.2 frame.2.1,
    invariant.requestedWrap.congr frame.2.1 frame.2.2.1, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl nextFormat))))⟩

/-- All construction modes have entered a block after header parsing or raw recovery. -/
theorem DefaultStateJ.construction_format {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (invariant : DefaultStateJ h r zs z s)
    (mode : s.mode = TABLE ∨ s.mode = LENLENS ∨ s.mode = CODELENS) : HeaderDone s := by
  rcases invariant.phase with head | bad | mem | sync | format | pending
  · rcases mode with selected | selected | selected <;> rw [selected] at head <;> contradiction
  · rcases mode with selected | selected | selected <;> rw [selected] at bad <;> contradiction
  · rcases mode with selected | selected | selected <;> rw [selected] at mem <;> contradiction
  · rcases mode with selected | selected | selected <;> rw [selected] at sync <;> contradiction
  · exact format
  · exact absurd pending.1 (by rcases mode with selected | selected | selected <;> rw [selected] <;> decide)

/-- The whole actual code-length reading loop retains reset configuration
and header classification, including its BAD and partial-input exits. -/
theorem clRead_default_state_complete {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = CODELENS) :
    ∃ outcome regs after stream state used, used ≤ bs.length ∧
      runX (clRead c) l h = .ok ((outcome, regs), after) ∧ DefaultStateJ after r zs stream state ∧
      DefaultConfigFrame s state ∧ DispatchBuffers after r regs (bs.drop used) ∧ ByteViewSizes h after ∧
      regs.next = inputAdvance l.next used ∧ regs.have_.toNat + used = l.have_.toNat ∧
      regs.put = l.put ∧ regs.left = l.left ∧ regs.out_ = l.out_ ∧
      regs.bits.toNat ≤ max l.bits.toNat 21 ∧ regs.bits.toNat ≤ l.bits.toNat + 8 * used ∧
      (state.mode = CODELENS ∨ state.mode = BAD) ∧
      (outcome = .ok () → state.mode = BAD ∨ state.«have».toNat = state.nlen.toNat + state.ndist.toNat) := by
  obtain ⟨outcome, regs, after, stream, state, used, bound, run, current,
    packet, sizes, cursor, count, put, left, total, bits, budget, modes, complete⟩ :=
    clRead_default_J_complete E invariant.toDefaultDecodeJ buffers mode
  obtain ⟨otherOutcome, otherRegs, otherHeap, otherStream, otherState, _, _, otherRun,
    good, _, _, _, _, _, _, _, _, _, _, _, _, _, frame, _⟩ :=
    clRead_buffers E invariant.good invariant.pending invariant.lengths buffers mode
  rw [run] at otherRun
  cases otherRun
  have streamEq : otherStream = stream := Option.some.inj (good.live.hz.symm.trans current.good.live.hz)
  have stateEq : otherState = state := Option.some.inj (good.live.hs.symm.trans current.good.live.hs)
  subst otherStream otherState
  have config : DefaultConfigFrame s state := by rw [frame]; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  have format := invariant.construction_format (Or.inr (Or.inr mode))
  exact ⟨outcome, regs, after, stream, state, used, bound, run, invariant.config_update current config format,
    config, packet, sizes, cursor, count, put, left, total, bits, budget, modes, complete⟩

/-- The actual end-of-block check and both constructors retain the full
history relation and its exact configuration frame before the real LEN_. -/
theorem clTail_default_state {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (modes : s.mode = BAD ∨ s.mode = CODELENS)
    (done : s.mode = CODELENS → s.«have».toNat = s.nlen.toNat + s.ndist.toNat)
    (format : HeaderDone s) :
    (∃ ret after stream state,
      runX (clTail c) l h = .ok ((.ok (), { l with ret := ret }), after) ∧
      DefaultStateJ after r zs stream state ∧ DefaultConfigFrame s state ∧ state.mode = BAD ∧
      DispatchBuffers after r { l with ret := ret } bs ∧ ByteViewSizes h after ∧ after.static = h.static) ∨
    (∃ after state, DefaultStateJ after r zs z state ∧ DefaultConfigFrame s state ∧ state.mode = LEN_ ∧
      DispatchBuffers after r { l with ret := 0 } bs ∧ ByteViewSizes h after ∧ after.static = h.static ∧
      (runX (clTail c) l h = if c.flush = Z_TREES then .ok ((.error Ex.leave, { l with ret := 0 }), after)
        else runX (inflate_LEN_ c) { l with ret := 0 } after)) := by
  rcases clTail_buffers E invariant.good invariant.pending buffers modes invariant.lengths done with bad | ready
  · obtain ⟨ret, after, stream, state, run, current, mode, tables, pending, packet, sizes, static, update⟩ := bad
    have base := invariant.toDefaultDecodeJ.table_update current tables pending sizes static update (Or.inl mode)
    have config : DefaultConfigFrame s state := by rw [update.2.2]; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    exact Or.inl ⟨ret, after, stream, state, run,
      invariant.config_update base config format, config, mode, packet, sizes, static⟩
  · obtain ⟨after, state, current, mode, tables, pending, packet, sizes, static, run, update⟩ := ready
    have base := invariant.toDefaultDecodeJ.table_update current tables pending sizes static update (Or.inr mode)
    have config : DefaultConfigFrame s state := by rw [update.2.2]; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    exact Or.inr ⟨after, state, invariant.config_update base config format, config, mode, packet, sizes, static, run⟩

/-- The whole actual CODELENS chain retains the full default history fields
up to its concrete LEN_ continuation or an exit. -/
theorem inflate_CODELENS_default_state_boundary {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = CODELENS) :
    ∃ regs after stream state used, used ≤ bs.length ∧ DefaultStateJ after r zs stream state ∧
      DefaultConfigFrame s state ∧
      DispatchBuffers after r regs (bs.drop used) ∧ ByteViewSizes h after ∧
      regs.next = inputAdvance l.next used ∧ regs.have_.toNat + used = l.have_.toNat ∧
      regs.put = l.put ∧ regs.left = l.left ∧ regs.out_ = l.out_ ∧
      regs.bits.toNat ≤ max l.bits.toNat 21 ∧ regs.bits.toNat ≤ l.bits.toNat + 8 * used ∧
      ((∃ outcome, runX (inflate_CODELENS c) l h = .ok ((outcome, regs), after) ∧
          (outcome ≠ .ok () ∨ state.mode = BAD)) ∨
       (state.mode = LEN_ ∧ runX (inflate_CODELENS c) l h =
          if c.flush = Z_TREES then .ok ((.error Ex.leave, regs), after)
          else runX (inflate_LEN_ c) regs after)) := by
  obtain ⟨outcome, regs, after, stream, state, used, bound, read, nextJ,
    config, packet, sizes, cursor, count, put, left, total, bits, budget, modes, complete⟩ :=
    clRead_default_state_complete E invariant buffers mode
  cases outcome with
  | error exit =>
    refine ⟨regs, after, stream, state, used, bound, nextJ, config, packet, sizes, cursor, count,
      put, left, total, bits, budget, Or.inl ⟨.error exit, ?_, Or.inl ?_⟩⟩
    · rw [inflate_CODELENS_eq, runX_bind, read]
    · intro impossible
      cases impossible
  | ok unit =>
    cases unit
    have source : runX (inflate_CODELENS c) l h = runX (clTail c) regs after := by
      rw [inflate_CODELENS_eq, runX_bind, read]
    have current : Env c after r zs stream state := ⟨E.strm, E.st, nextJ.good.live.hz, nextJ.good.live.hs⟩
    have done : state.mode = CODELENS → state.«have».toNat = state.nlen.toNat + state.ndist.toNat := by
      intro code
      rcases complete rfl with bad | full
      · rw [code] at bad
        cases bad
      · exact full
    have format : HeaderDone state := by
      have before := invariant.construction_format (Or.inr (Or.inr mode))
      unfold HeaderDone at before ⊢
      rw [config.2.2.1, config.2.2.2.1]
      exact before
    rcases clTail_default_state current nextJ packet modes.symm done format with bad | ready
    · obtain ⟨ret, finalHeap, finalStream, finalState, run, finalJ, finalConfig, badMode, finalPacket, finalSizes, _⟩ := bad
      exact ⟨{ regs with ret := ret }, finalHeap, finalStream, finalState, used, bound, finalJ, config.trans finalConfig,
        finalPacket, sizes.trans finalSizes, cursor, count, put, left, total, bits, budget,
        Or.inl ⟨.ok (), source.trans run, Or.inr badMode⟩⟩
    · obtain ⟨finalHeap, finalState, finalJ, finalConfig, finalMode, finalPacket, finalSizes, _, run⟩ := ready
      exact ⟨{ regs with ret := 0 }, finalHeap, stream, finalState, used, bound, finalJ, config.trans finalConfig,
        finalPacket, sizes.trans finalSizes, cursor, count, put, left, total, bits, budget,
        Or.inr ⟨finalMode, source.trans run⟩⟩


/-- Both actual LENLENS loops and CODES retain reset/header fields at all
visible exits and before the real CODELENS continuation. -/
theorem inflate_LENLENS_default_state_entry {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = LENLENS) :
    ∃ regs after stream state used, used ≤ bs.length ∧ DefaultStateJ after r zs stream state ∧
      DefaultConfigFrame s state ∧
      DispatchBuffers after r regs (bs.drop used) ∧ ByteViewSizes h after ∧
      regs.next = inputAdvance l.next used ∧ regs.have_.toNat + used = l.have_.toNat ∧
      regs.put = l.put ∧ regs.left = l.left ∧ regs.out_ = l.out_ ∧
      regs.bits.toNat ≤ max l.bits.toNat 10 ∧ regs.bits.toNat ≤ l.bits.toNat + 8 * used ∧
      ((∃ outcome, runX (inflate_LENLENS c) l h = .ok ((outcome, regs), after) ∧
          (outcome = .error Ex.leave ∨ (outcome = .ok () ∧ state.mode = BAD))) ∨
       (state.mode = CODELENS ∧ runX (inflate_LENLENS c) l h = runX (inflate_CODELENS c) regs after)) := by
  have format := invariant.construction_format (Or.inr (Or.inl mode))
  obtain ⟨ncode, haveBound, nlen, ndist, prefixValues⟩ := invariant.headerLengths mode
  obtain ⟨regs, used, bound, inv, streamBits, shape, wait, full, cursor, bits, prefixExit, read⟩ :=
    inflate_LENLENS_table_cursor E.strm E.st E.hz E.hs invariant.good.inv.wf ncode haveBound prefixValues buffers.bits
  let m := min (s.ncode.toNat - s.«have».toNat) ((Zlib.Inflate.Proofs.stream l bs).length / 3)
  have mBound : m ≤ s.ncode.toNat - s.«have».toNat := Nat.min_le_left _ _
  have count : regs.have_.toNat + used = l.have_.toNat := by
    rw [inv.have_eq, buffers.bits.have_eq, List.length_drop]
    omega
  have put : regs.put = l.put := by rw [shape]
  have left : regs.left = l.left := by rw [shape]
  have total : regs.out_ = l.out_ := by rw [shape]
  have budget : regs.bits.toNat ≤ l.bits.toNat + 8 * used := by
    have shorter : (Zlib.Inflate.Proofs.stream regs (bs.drop used)).length ≤
        (Zlib.Inflate.Proofs.stream l bs).length := by rw [streamBits, List.length_drop]; omega
    rw [tcStream_length inv, tcStream_length buffers.bits, List.length_drop] at shorter
    omega
  by_cases short : m < s.ncode.toNat - s.«have».toNat
  · obtain ⟨_, _, _, run⟩ := wait short
    obtain ⟨exit2, regs2, heap2, state2, used2, bound2, read2, nextJ,
      packet, sizes, _, count2, _, _, _, _, _⟩ := ll1_default_J E invariant.toDefaultDecodeJ buffers mode
    rw [read] at read2
    cases read2
    have sameUse : used2 = used := by omega
    subst used2
    have config : DefaultConfigFrame s state2 := by
      have get := nextJ.good.live.hs
      rw [setI_istates_same] at get
      rw [← Option.some.inj get]
      simp only [DefaultConfigFrame, llSt, and_self, eq_self]
    have nextState := invariant.config_update nextJ config format
    exact ⟨regs, _, z, state2, used, bound, nextState, config, packet, sizes, cursor, count,
      put, left, total, bits, budget, Or.inl ⟨.error Ex.leave, run, Or.inl rfl⟩⟩
  · have complete : m = s.ncode.toNat - s.«have».toNat := by omega
    obtain ⟨ret, work, codes, workSize, codeSize, _, _, kinds, _, accepted, rejected⟩ := full complete
    let filled := llDone s (Zlib.Inflate.Proofs.stream l bs)
    have lensSize : filled.lens.size = 320 := by
      simp only [filled, llDone, lzSt, llSt, lensZero_size, lensRead_size]
      exact invariant.good.inv.wf.1
    rcases kinds with success | failure
    · obtain ⟨usedCodes, root, capacity, safe, run⟩ := accepted success
      let state := llOkSt zs filled usedCodes root work codes
      have frame : LengthTableFrame s state := by
        simp only [LengthTableFrame, state, llOkSt, llPre, filled, llDone, lzSt, llSt]
      have wf : state.WellFormed := ⟨lensSize, workSize, codeSize⟩
      have pointers : PtrInv zs state :=
        ⟨⟨usedCodes, rfl, by omega⟩, Or.inl ⟨0, 0, rfl, rfl, by decide, by decide⟩⟩
      have codeInv : CodeLengthInvariant zs state :=
        llOkSt_codeLengthInvariant zs filled usedCodes root work codes safe nlen ndist
      have bitInv : BitInv h { regs with ret := 0 } (bs.drop used) := ⟨inv.have_eq, inv.next, inv.hold_lt⟩
      obtain ⟨nextJ, packet, sizes⟩ := invariant.toDefaultDecodeJ.length_table_packet buffers frame
        (stream := z) (by rfl) wf pointers (Or.inr rfl) codeInv bitInv cursor count put left total
      rw [ZStreamRef.put_self E.hz] at nextJ packet sizes
      have config : DefaultConfigFrame s state := by rw [frame]; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
      have nextState := invariant.config_update nextJ config format
      exact ⟨{ regs with ret := 0 }, _, z, state, used, bound, nextState, config, packet, sizes,
        cursor, count, put, left, total, bits, budget, Or.inr ⟨rfl, run⟩⟩
    · obtain ⟨i, _, run⟩ := rejected failure
      let state := { llBadSt zs filled work codes with mode := BAD }
      let stream := { z with msg := .ref (.str i) 0 }
      have frame : LengthTableFrame s state := by
        simp only [LengthTableFrame, state, llBadSt, llPre, filled, llDone, lzSt, llSt]
      have wf : state.WellFormed := ⟨lensSize, workSize, codeSize⟩
      have pointers : PtrInv zs state :=
        ⟨⟨0, rfl, by decide⟩, Or.inl ⟨0, 0, rfl, rfl, by decide, by decide⟩⟩
      have codeInv : CodeLengthInvariant zs state := by
        intro active
        change BAD = CODELENS at active
        exact False.elim ((by decide : BAD ≠ CODELENS) active)
      have bitInv : BitInv h { regs with ret := -1 } (bs.drop used) := ⟨inv.have_eq, inv.next, inv.hold_lt⟩
      obtain ⟨nextJ, packet, sizes⟩ := invariant.toDefaultDecodeJ.length_table_packet buffers frame
        (stream := stream) (by rfl) wf pointers (Or.inl rfl) codeInv bitInv cursor count put left total
      have config : DefaultConfigFrame s state := by rw [frame]; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
      have nextState := invariant.config_update nextJ config format
      refine ⟨{ regs with ret := -1 }, _, stream, state, used, bound, nextState, config, packet, sizes,
        cursor, count, put, left, total, bits, budget, Or.inl ⟨.ok (), ?_, Or.inr ⟨rfl, rfl⟩⟩⟩
      simpa only [tcBadHeap, ZStreamRef.put_setI, setI_setI] using run



/-- Actual LENLENS and CODELENS compose on the same full default state
and exact configuration frame up to the real LEN_ continuation. -/
theorem inflate_LENLENS_default_state_boundary {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = LENLENS) :
    ∃ regs after stream state used, used ≤ bs.length ∧ DefaultStateJ after r zs stream state ∧
      DefaultConfigFrame s state ∧
      DispatchBuffers after r regs (bs.drop used) ∧ ByteViewSizes h after ∧
      regs.next = inputAdvance l.next used ∧ regs.have_.toNat + used = l.have_.toNat ∧
      regs.put = l.put ∧ regs.left = l.left ∧ regs.out_ = l.out_ ∧
      regs.bits.toNat ≤ max l.bits.toNat 21 ∧ regs.bits.toNat ≤ l.bits.toNat + 8 * used ∧
      ((∃ outcome, runX (inflate_LENLENS c) l h = .ok ((outcome, regs), after) ∧
          (outcome ≠ .ok () ∨ state.mode = BAD)) ∨
       (state.mode = LEN_ ∧ runX (inflate_LENLENS c) l h =
          if c.flush = Z_TREES then .ok ((.error Ex.leave, regs), after)
          else runX (inflate_LEN_ c) regs after)) := by
  obtain ⟨first, heap0, stream0, state0, used0, bound0, nextJ, config0, packet0, sizes0, cursor0, count0,
    put0, left0, total0, bits0, budget0, stopped | continued⟩ :=
    inflate_LENLENS_default_state_entry E invariant buffers mode
  · obtain ⟨outcome, run, why⟩ := stopped
    refine ⟨first, heap0, stream0, state0, used0, bound0, nextJ, config0, packet0, sizes0, cursor0, count0,
      put0, left0, total0, by omega, budget0, Or.inl ⟨outcome, run, ?_⟩⟩
    rcases why with wait | ⟨_, bad⟩
    · left
      intro impossible
      rw [wait] at impossible
      cases impossible
    · exact Or.inr bad
  · obtain ⟨codesMode, source⟩ := continued
    have E0 : Env c heap0 r zs stream0 state0 := ⟨E.strm, E.st, nextJ.good.live.hz, nextJ.good.live.hs⟩
    obtain ⟨regs, after, stream, state, used1, bound1, finalJ, config1, packet, sizes, cursor1, count1,
      put1, left1, total1, bits1, budget1, kinds⟩ :=
      inflate_CODELENS_default_state_boundary E0 nextJ packet0 codesMode
    have bound : used0 + used1 ≤ bs.length := by rw [List.length_drop] at bound1; omega
    have cursor : regs.next = inputAdvance l.next (used0 + used1) := by rw [cursor1, cursor0, inputAdvance_add]
    refine ⟨regs, after, stream, state, used0 + used1, bound, finalJ, config0.trans config1,
      ?_, sizes0.trans sizes, cursor, by omega, put1.trans put0, left1.trans left0, total1.trans total0,
      by omega, by omega, ?_⟩
    · simpa only [List.drop_drop] using packet
    · rcases kinds with stopped | continued
      · obtain ⟨outcome, run, why⟩ := stopped
        exact Or.inl ⟨outcome, source.trans run, why⟩
      · obtain ⟨mode, run⟩ := continued
        exact Or.inr ⟨mode, source.trans run⟩

/-- Actual TABLE establishes LENLENS on the full default state, preserving
reset configuration and the completed-header classification. -/
theorem inflate_TABLE_default_state_entry {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = TABLE) :
    ∃ regs after stream state used, used ≤ bs.length ∧ DefaultStateJ after r zs stream state ∧
      DefaultConfigFrame s state ∧
      DispatchBuffers after r regs (bs.drop used) ∧ ByteViewSizes h after ∧
      regs.next = inputAdvance l.next used ∧ regs.have_.toNat + used = l.have_.toNat ∧
      regs.put = l.put ∧ regs.left = l.left ∧ regs.out_ = l.out_ ∧
      regs.bits.toNat ≤ max l.bits.toNat 21 ∧ regs.bits.toNat ≤ l.bits.toNat + 8 * used ∧
      ((∃ outcome, runX (inflate_TABLE c) l h = .ok ((outcome, regs), after) ∧
          (outcome = .error Ex.leave ∨ (outcome = .ok () ∧ state.mode = BAD))) ∨
       (state.mode = LENLENS ∧ runX (inflate_TABLE c) l h = runX (inflate_LENLENS c) regs after)) := by
  have format := invariant.construction_format (Or.inl mode)
  obtain ⟨outcome, current, used, pull, bound, inv, _, wait, full⟩ :=
    inflate_TABLE_run E.strm E.st E.hz E.hs buffers.bits
  obtain ⟨outcome2, current2, used2, pull2, bound2, inv2, _, bitCount, shape, bitBound, _, _, _, kinds, cursor⟩ :=
    NEEDBITS_run_cursor buffers.bits 14 (by decide)
  rw [pull] at pull2
  cases pull2
  have sameUse : used2 = used := by
    have one := inv.have_eq
    have two := inv2.have_eq
    rw [List.length_drop] at one two
    omega
  subst used2
  change current.bits.toNat ≤ max l.bits.toNat 21 at bitBound
  have count : current.have_.toNat + used = l.have_.toNat := by
    rw [inv.have_eq, buffers.bits.have_eq, List.length_drop]
    omega
  have put : current.put = l.put := by rw [shape]
  have left : current.left = l.left := by rw [shape]
  have total : current.out_ = l.out_ := by rw [shape]
  rcases kinds with normal | leaves
  · obtain ⟨enough, dropInv, _, badRun, readyRun⟩ := full normal
    have dropCount : (tableRegs current).bits.toNat = current.bits.toNat - 14 := by
      change (current.bits - 14).toNat = _
      exact UInt32.toNat_sub_of_le _ _ (by apply UInt32.le_iff_toNat_le.mpr; exact enough)
    have bits : (tableRegs current).bits.toNat ≤ max l.bits.toNat 21 := by rw [dropCount]; omega
    have budget : (tableRegs current).bits.toNat ≤ l.bits.toNat + 8 * used := by rw [dropCount]; omega
    by_cases invalid : (tableCounts s current.hold).nlen > 286 ∨ (tableCounts s current.hold).ndist > 30
    · obtain ⟨i, _, run⟩ := badRun invalid
      let state := { tableCounts s current.hold with mode := BAD }
      let stream := { z with msg := .ref (.str i) 0 }
      have frame : TableCountsFrame s state := by rfl
      have lengths : LengthHeaderInvariant state := by
        intro active
        change BAD = LENLENS at active
        exact False.elim ((by decide : BAD ≠ LENLENS) active)
      have nextJ := invariant.toDefaultDecodeJ.counts_update frame (stream := stream) (by rfl) (Or.inl rfl) lengths
      obtain ⟨packet, sizes⟩ := buffers.metadata_advance invariant.good nextJ.good rfl dropInv
        cursor count put left total
      have config : DefaultConfigFrame s state := by rw [frame]; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
      have nextState := invariant.config_update nextJ config format
      refine ⟨tableRegs current, _, stream, state, used, bound, nextState, config, packet, sizes,
        cursor, count, put, left, total, bits, budget, Or.inl ⟨.ok (), ?_, Or.inr ⟨rfl, rfl⟩⟩⟩
      exact run
    · let state := { tableCounts s current.hold with «have» := 0, mode := LENLENS }
      have frame : TableCountsFrame s state := by rfl
      have lengths : LengthHeaderInvariant state := tableCounts_header_invariant s current.hold invalid
      have nextJ := invariant.toDefaultDecodeJ.counts_update frame (stream := z) (by rfl) (Or.inr rfl) lengths
      obtain ⟨packet, sizes⟩ := buffers.metadata_advance invariant.good nextJ.good rfl dropInv
        cursor count put left total
      rw [ZStreamRef.put_self E.hz] at nextJ packet sizes
      have config : DefaultConfigFrame s state := by rw [frame]; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
      have nextState := invariant.config_update nextJ config format
      exact ⟨tableRegs current, _, z, state, used, bound, nextState, config, packet, sizes,
        cursor, count, put, left, total, bits, budget, Or.inr ⟨rfl, readyRun invalid⟩⟩
  · obtain ⟨_, _, _, run⟩ := wait leaves
    have packet : DispatchBuffers h r current (bs.drop used) :=
      buffers.consume invariant.good invariant.good rfl (fun _ => rfl) (fun _ => rfl)
        (by rw [shape]; rfl) cursor bound inv
    exact ⟨current, h, z, s, used, bound, invariant, ⟨rfl, rfl, rfl, rfl, rfl⟩, packet, ByteViewSizes.refl h,
      cursor, count, put, left, total, bitBound, by omega, Or.inl ⟨.error Ex.leave, run, Or.inl rfl⟩⟩


/-- Actual TABLE composes both construction alphabets, retaining the full
default state relation and configuration frame up to the real LEN_. -/
theorem inflate_TABLE_default_state_boundary {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = TABLE) :
    ∃ regs after stream state used, used ≤ bs.length ∧ DefaultStateJ after r zs stream state ∧
      DefaultConfigFrame s state ∧
      DispatchBuffers after r regs (bs.drop used) ∧ ByteViewSizes h after ∧
      regs.next = inputAdvance l.next used ∧ regs.have_.toNat + used = l.have_.toNat ∧
      regs.put = l.put ∧ regs.left = l.left ∧ regs.out_ = l.out_ ∧
      regs.bits.toNat ≤ max l.bits.toNat 21 ∧ regs.bits.toNat ≤ l.bits.toNat + 8 * used ∧
      ((∃ outcome, runX (inflate_TABLE c) l h = .ok ((outcome, regs), after) ∧
          (outcome ≠ .ok () ∨ state.mode = BAD)) ∨
       (state.mode = LEN_ ∧ runX (inflate_TABLE c) l h =
          if c.flush = Z_TREES then .ok ((.error Ex.leave, regs), after)
          else runX (inflate_LEN_ c) regs after)) := by
  obtain ⟨first, heap0, stream0, state0, used0, bound0, nextJ, config0, packet0, sizes0, cursor0, count0,
    put0, left0, total0, bits0, budget0, stopped | continued⟩ :=
    inflate_TABLE_default_state_entry E invariant buffers mode
  · obtain ⟨outcome, run, why⟩ := stopped
    refine ⟨first, heap0, stream0, state0, used0, bound0, nextJ, config0, packet0, sizes0, cursor0, count0,
      put0, left0, total0, by omega, budget0, Or.inl ⟨outcome, run, ?_⟩⟩
    rcases why with wait | ⟨_, bad⟩
    · left
      intro impossible
      rw [wait] at impossible
      cases impossible
    · exact Or.inr bad
  · obtain ⟨codesMode, source⟩ := continued
    have E0 : Env c heap0 r zs stream0 state0 := ⟨E.strm, E.st, nextJ.good.live.hz, nextJ.good.live.hs⟩
    obtain ⟨regs, after, stream, state, used1, bound1, finalJ, config1, packet, sizes, cursor1, count1,
      put1, left1, total1, bits1, budget1, kinds⟩ :=
      inflate_LENLENS_default_state_boundary E0 nextJ packet0 codesMode
    have bound : used0 + used1 ≤ bs.length := by rw [List.length_drop] at bound1; omega
    have cursor : regs.next = inputAdvance l.next (used0 + used1) := by rw [cursor1, cursor0, inputAdvance_add]
    refine ⟨regs, after, stream, state, used0 + used1, bound, finalJ, config0.trans config1,
      ?_, sizes0.trans sizes, cursor, by omega, put1.trans put0, left1.trans left0, total1.trans total0,
      by omega, by omega, ?_⟩
    · simpa only [List.drop_drop] using packet
    · rcases kinds with stopped | continued
      · obtain ⟨outcome, run, why⟩ := stopped
        exact Or.inl ⟨outcome, source.trans run, why⟩
      · obtain ⟨mode, run⟩ := continued
        exact Or.inr ⟨mode, source.trans run⟩


/-- The actual construction switch retains the full default state and
configuration frame through its complete constructor chain. -/
theorem inflate_dispatch_construction_state_boundary {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = TABLE ∨ s.mode = LENLENS ∨ s.mode = CODELENS) :
    ∃ regs after stream state used, used ≤ bs.length ∧ DefaultStateJ after r zs stream state ∧
      DefaultConfigFrame s state ∧
      DispatchBuffers after r regs (bs.drop used) ∧ ByteViewSizes h after ∧
      regs.next = inputAdvance l.next used ∧ regs.have_.toNat + used = l.have_.toNat ∧
      regs.put = l.put ∧ regs.left = l.left ∧ regs.out_ = l.out_ ∧
      regs.bits.toNat ≤ max l.bits.toNat 21 ∧ regs.bits.toNat ≤ l.bits.toNat + 8 * used ∧
      ((∃ outcome, runX (inflate_dispatch c) l h = .ok ((outcome, regs), after) ∧
          (outcome ≠ .ok () ∨ state.mode = BAD)) ∨
       (state.mode = LEN_ ∧ runX (inflate_dispatch c) l h =
          if c.flush = Z_TREES then .ok ((.error Ex.leave, regs), after)
          else runX (inflate_LEN_ c) regs after)) := by
  rcases mode with table | lengths | codes
  · rw [inflate_dispatch_TABLE E l table]
    exact inflate_TABLE_default_state_boundary E invariant buffers table
  · rw [inflate_dispatch_LENLENS E l lengths]
    exact inflate_LENLENS_default_state_boundary E invariant buffers lengths
  · rw [inflate_dispatch_CODELENS E l codes]
    exact inflate_CODELENS_default_state_boundary E invariant buffers codes



/-- All actual dynamic construction cases execute their real LEN_
continuation for every flush. The complete default state, caller packet,
exact accounting and strict common rank hold together. The internal raw
fast interface remains explicit. -/
theorem inflate_dispatch_construction_default_state_rank {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = TABLE ∨ s.mode = LENLENS ∨ s.mode = CODELENS)
    (raw : RawFastIO l) (incoming : l.bits.toNat ≤ 39) :
    ∃ outcome regs after stream state used made, used ≤ bs.length ∧
      runX (inflate_dispatch c) l h = .ok ((outcome, regs), after) ∧ DefaultStateJ after r zs stream state ∧
      DispatchBuffers after r regs (bs.drop used) ∧ ByteViewSizes h after ∧
      regs.next = inputAdvance l.next used ∧ regs.have_.toNat + used = l.have_.toNat ∧
      regs.put = inputAdvance l.put made ∧ regs.left.toNat + made = l.left.toNat ∧ regs.bits.toNat ≤ 39 ∧
      (outcome = .error Ex.leave ∨ (outcome = .ok () ∧ dispatchRank regs state.mode < dispatchRank l s.mode)) := by
  obtain ⟨regs, after, stream, state, used, bound, nextJ, config, packet, sizes, cursor, count,
    put, left, total, bits, budget, stopped | continued⟩ :=
    inflate_dispatch_construction_state_boundary E invariant buffers mode
  · obtain ⟨outcome, run, why⟩ := stopped
    refine ⟨outcome, regs, after, stream, state, used, 0, bound, run, nextJ, packet, sizes,
      cursor, count, by rw [put, inputAdvance_zero], by rw [left]; omega, by omega, ?_⟩
    rcases inflate_dispatch_construction_outcomes E mode run with leaves | normal
    · exact Or.inl leaves
    · have bad : state.mode = BAD := why.resolve_left (fun impossible => impossible normal)
      refine Or.inr ⟨normal, ?_⟩
      apply dispatchRank_advance (l := l) (regs := regs) (used := used) (made := 0) count
      · rw [left]; omega
      · exact budget
      · right
        rw [bad]
        rcases mode with selected | selected | selected <;> rw [selected] <;> decide
  · obtain ⟨nextMode, source⟩ := continued
    by_cases trees : c.flush = Z_TREES
    · rw [if_pos trees] at source
      exact ⟨.error Ex.leave, regs, after, stream, state, used, 0, bound, source, nextJ, packet, sizes,
        cursor, count, by rw [put, inputAdvance_zero], by rw [left]; omega, by omega, Or.inl rfl⟩
    · rw [if_neg trees] at source
      have nextEnv : Env c after r zs stream state :=
        ⟨E.strm, E.st, nextJ.good.live.hz, nextJ.good.live.hs⟩
      have dataMode : DataTableMode state.mode := by rw [nextMode]; unfold DataTableMode; decide
      have nextRaw := raw.advance cursor (show regs.put = inputAdvance l.put 0 by rw [put, inputAdvance_zero])
      obtain ⟨outcome, finalRegs, finalHeap, finalStream, finalState, used2, made,
        bound2, run, finalJ, _, finalPacket, finalSizes, next, haveCount, output, leftCount, finalBits, progress⟩ :=
        inflate_dispatch_data_state_rank nextEnv nextJ packet dataMode (fun _ => nextRaw)
      have prefixRank : dispatchRank regs state.mode < dispatchRank l s.mode := by
        apply dispatchRank_advance (l := l) (regs := regs) (used := used) (made := 0) count
        · rw [left]; omega
        · exact budget
        · right
          rw [nextMode]
          rcases mode with selected | selected | selected <;> rw [selected] <;> decide
      have combined : used + used2 ≤ bs.length := by simp only [List.length_drop] at bound2; omega
      have finalRun : runX (inflate_dispatch c) l h = .ok ((outcome, finalRegs), finalHeap) :=
        source.trans ((inflate_dispatch_LEN_start nextEnv regs nextMode).symm.trans run)
      refine ⟨outcome, finalRegs, finalHeap, finalStream, finalState, used + used2, made, combined,
        finalRun, finalJ, ?_, sizes.trans finalSizes, ?_, ?_, ?_, ?_, by omega, ?_⟩
      · simpa only [List.drop_drop, Nat.add_comm] using finalPacket
      · rw [next, cursor, inputAdvance_add]
      · omega
      · rw [output, put]
      · rw [left] at leftCount
        exact leftCount
      · rcases progress with leaves | ⟨normal, decreases⟩
        · exact Or.inl leaves
        · exact Or.inr ⟨normal, Nat.lt_trans decreases prefixRank⟩

end Zlib.Inflate.Proofs
