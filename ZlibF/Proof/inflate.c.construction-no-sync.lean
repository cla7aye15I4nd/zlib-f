import ZlibF.Proof.«inflate.c.sync-flags-history»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Reading code lengths can stop only in CODELENS or BAD, while a completed
constructor enters LEN_. None of these boundaries enters SYNC. -/
theorem inflate_CODELENS_default_boundary_no_sync
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs)
    (mode : s.mode = CODELENS) :
    ∃ regs after stream state used,
      used ≤ bs.length ∧
      DefaultStateJ after r zs stream state ∧
      DefaultConfigFrame s state ∧
      state.mode ≠ SYNC ∧
      DispatchBuffers after r regs (bs.drop used) ∧
      ByteViewSizes h after ∧
      regs.next = inputAdvance l.next used ∧
      regs.have_.toNat + used = l.have_.toNat ∧
      regs.put = l.put ∧ regs.left = l.left ∧
      regs.out_ = l.out_ ∧
      regs.bits.toNat ≤ max l.bits.toNat 21 ∧
      regs.bits.toNat ≤ l.bits.toNat + 8 * used ∧
      ((∃ outcome,
          runX (inflate_CODELENS c) l h =
            .ok ((outcome, regs), after) ∧
          (outcome ≠ .ok () ∨ state.mode = BAD)) ∨
       (state.mode = LEN_ ∧
          runX (inflate_CODELENS c) l h =
            if c.flush = Z_TREES then
              .ok ((.error Ex.leave, regs), after)
            else runX (inflate_LEN_ c) regs after)) := by
  obtain ⟨outcome, regs, after, stream, state, used, bound,
    read, nextJ, config, packet, sizes, cursor, count, put, left,
    total, bits, budget, modes, complete⟩ :=
    clRead_default_state_complete E invariant buffers mode
  cases outcome with
  | error exit =>
    have notSync : state.mode ≠ SYNC := by
      rcases modes with code | bad
      · rw [code]
        decide
      · rw [bad]
        decide
    refine ⟨regs, after, stream, state, used, bound, nextJ,
      config, notSync, packet, sizes, cursor, count, put, left,
      total, bits, budget,
      Or.inl ⟨.error exit, ?_, Or.inl ?_⟩⟩
    · rw [inflate_CODELENS_eq, runX_bind, read]
    · intro impossible
      cases impossible
  | ok unit =>
    cases unit
    have source : runX (inflate_CODELENS c) l h =
        runX (clTail c) regs after := by
      rw [inflate_CODELENS_eq, runX_bind, read]
    have current : Env c after r zs stream state :=
      ⟨E.strm, E.st, nextJ.good.live.hz, nextJ.good.live.hs⟩
    have done : state.mode = CODELENS →
        state.«have».toNat = state.nlen.toNat +
          state.ndist.toNat := by
      intro code
      rcases complete rfl with bad | full
      · rw [code] at bad
        cases bad
      · exact full
    have format : state.wrap = 0 ∨ state.flags = 0 := by
      rw [config.2.2.1, config.2.2.2]
      exact invariant.construction_format
        (Or.inr (Or.inr mode))
    rcases clTail_default_state current nextJ packet modes.symm
        done format with bad | ready
    · obtain ⟨ret, finalHeap, finalStream, finalState, run,
        finalJ, finalConfig, badMode, finalPacket,
        finalSizes, _⟩ := bad
      have notSync : finalState.mode ≠ SYNC := by
        rw [badMode]
        decide
      exact ⟨{ regs with ret := ret }, finalHeap, finalStream,
        finalState, used, bound, finalJ,
        config.trans finalConfig, notSync, finalPacket,
        sizes.trans finalSizes, cursor, count, put, left,
        total, bits, budget,
        Or.inl ⟨.ok (), source.trans run,
          Or.inr badMode⟩⟩
    · obtain ⟨finalHeap, finalState, finalJ,
        finalConfig, finalMode, finalPacket,
        finalSizes, _, run⟩ := ready
      have notSync : finalState.mode ≠ SYNC := by
        rw [finalMode]
        decide
      exact ⟨{ regs with ret := 0 }, finalHeap, stream,
        finalState, used, bound, finalJ,
        config.trans finalConfig, notSync, finalPacket,
        sizes.trans finalSizes, cursor, count, put, left,
        total, bits, budget,
        Or.inr ⟨finalMode, source.trans run⟩⟩

theorem inflate_LENLENS_default_state_entry_no_sync {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = LENLENS) :
    ∃ regs after stream state used, used ≤ bs.length ∧ DefaultStateJ after r zs stream state ∧
      DefaultConfigFrame s state ∧ state.mode ≠ SYNC ∧
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
    have notSync : state2.mode ≠ SYNC := by
      have get := nextJ.good.live.hs
      rw [setI_istates_same] at get
      rw [← Option.some.inj get]
      change s.mode ≠ SYNC
      rw [mode]
      decide
    exact ⟨regs, _, z, state2, used, bound, nextState, config, notSync, packet, sizes, cursor, count,
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
      have config : DefaultConfigFrame s state := by rw [frame]; exact ⟨rfl, rfl, rfl, rfl⟩
      have nextState := invariant.config_update nextJ config format
      have notSync : state.mode ≠ SYNC := by
        change CODELENS ≠ SYNC
        decide
      exact ⟨{ regs with ret := 0 }, _, z, state, used, bound, nextState, config, notSync, packet, sizes,
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
      have config : DefaultConfigFrame s state := by rw [frame]; exact ⟨rfl, rfl, rfl, rfl⟩
      have nextState := invariant.config_update nextJ config format
      have notSync : state.mode ≠ SYNC := by
        change BAD ≠ SYNC
        decide
      refine ⟨{ regs with ret := -1 }, _, stream, state, used, bound, nextState, config, notSync, packet, sizes,
        cursor, count, put, left, total, bits, budget, Or.inl ⟨.ok (), ?_, Or.inr ⟨rfl, rfl⟩⟩⟩
      simpa only [tcBadHeap, ZStreamRef.put_setI, setI_setI] using run

/-- LENLENS first reads the code-length alphabet, then enters the checked
CODELENS subchain. Every visible intermediate state avoids SYNC. -/
theorem inflate_LENLENS_default_boundary_no_sync
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs)
    (mode : s.mode = LENLENS) :
    ∃ regs after stream state used,
      used ≤ bs.length ∧
      DefaultStateJ after r zs stream state ∧
      DefaultConfigFrame s state ∧ state.mode ≠ SYNC ∧
      DispatchBuffers after r regs (bs.drop used) ∧
      ByteViewSizes h after ∧
      regs.next = inputAdvance l.next used ∧
      regs.have_.toNat + used = l.have_.toNat ∧
      regs.put = l.put ∧ regs.left = l.left ∧
      regs.out_ = l.out_ ∧
      regs.bits.toNat ≤ max l.bits.toNat 21 ∧
      regs.bits.toNat ≤ l.bits.toNat + 8 * used ∧
      ((∃ outcome,
          runX (inflate_LENLENS c) l h =
            .ok ((outcome, regs), after) ∧
          (outcome ≠ .ok () ∨ state.mode = BAD)) ∨
       (state.mode = LEN_ ∧
          runX (inflate_LENLENS c) l h =
            if c.flush = Z_TREES then
              .ok ((.error Ex.leave, regs), after)
            else runX (inflate_LEN_ c) regs after)) := by
  obtain ⟨first, heap0, stream0, state0, used0, bound0,
    nextJ, config0, notSync0, packet0, sizes0, cursor0,
    count0, put0, left0, total0, bits0, budget0,
    stopped | continued⟩ :=
    inflate_LENLENS_default_state_entry_no_sync E invariant
      buffers mode
  · obtain ⟨outcome, run, why⟩ := stopped
    refine ⟨first, heap0, stream0, state0, used0, bound0,
      nextJ, config0, notSync0, packet0, sizes0, cursor0,
      count0, put0, left0, total0, by omega, budget0,
      Or.inl ⟨outcome, run, ?_⟩⟩
    rcases why with wait | ⟨_, bad⟩
    · left
      intro impossible
      rw [wait] at impossible
      cases impossible
    · exact Or.inr bad
  · obtain ⟨codesMode, source⟩ := continued
    have E0 : Env c heap0 r zs stream0 state0 :=
      ⟨E.strm, E.st, nextJ.good.live.hz,
        nextJ.good.live.hs⟩
    obtain ⟨regs, after, stream, state, used1, bound1,
      finalJ, config1, notSync, packet, sizes, cursor1,
      count1, put1, left1, total1, bits1, budget1,
      kinds⟩ :=
      inflate_CODELENS_default_boundary_no_sync E0 nextJ
        packet0 codesMode
    have bound : used0 + used1 ≤ bs.length := by
      rw [List.length_drop] at bound1
      omega
    have cursor : regs.next =
        inputAdvance l.next (used0 + used1) := by
      rw [cursor1, cursor0, inputAdvance_add]
    refine ⟨regs, after, stream, state, used0 + used1,
      bound, finalJ, config0.trans config1, notSync,
      ?_, sizes0.trans sizes, cursor, by omega,
      put1.trans put0, left1.trans left0,
      total1.trans total0, by omega, by omega, ?_⟩
    · simpa only [List.drop_drop] using packet
    · rcases kinds with stopped | continued
      · obtain ⟨outcome, run, why⟩ := stopped
        exact Or.inl ⟨outcome, source.trans run, why⟩
      · obtain ⟨selected, run⟩ := continued
        exact Or.inr ⟨selected, source.trans run⟩

theorem inflate_TABLE_default_state_entry_no_sync {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = TABLE) :
    ∃ regs after stream state used, used ≤ bs.length ∧ DefaultStateJ after r zs stream state ∧
      DefaultConfigFrame s state ∧ state.mode ≠ SYNC ∧
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
      have config : DefaultConfigFrame s state := by rw [frame]; exact ⟨rfl, rfl, rfl, rfl⟩
      have nextState := invariant.config_update nextJ config format
      have notSync : state.mode ≠ SYNC := by
        change BAD ≠ SYNC
        decide
      refine ⟨tableRegs current, _, stream, state, used, bound, nextState, config, notSync, packet, sizes,
        cursor, count, put, left, total, bits, budget, Or.inl ⟨.ok (), ?_, Or.inr ⟨rfl, rfl⟩⟩⟩
      exact run
    · let state := { tableCounts s current.hold with «have» := 0, mode := LENLENS }
      have frame : TableCountsFrame s state := by rfl
      have lengths : LengthHeaderInvariant state := tableCounts_header_invariant s current.hold invalid
      have nextJ := invariant.toDefaultDecodeJ.counts_update frame (stream := z) (by rfl) (Or.inr rfl) lengths
      obtain ⟨packet, sizes⟩ := buffers.metadata_advance invariant.good nextJ.good rfl dropInv
        cursor count put left total
      rw [ZStreamRef.put_self E.hz] at nextJ packet sizes
      have config : DefaultConfigFrame s state := by rw [frame]; exact ⟨rfl, rfl, rfl, rfl⟩
      have nextState := invariant.config_update nextJ config format
      have notSync : state.mode ≠ SYNC := by
        change LENLENS ≠ SYNC
        decide
      exact ⟨tableRegs current, _, z, state, used, bound, nextState, config, notSync, packet, sizes,
        cursor, count, put, left, total, bits, budget, Or.inr ⟨rfl, readyRun invalid⟩⟩
  · obtain ⟨_, _, _, run⟩ := wait leaves
    have packet : DispatchBuffers h r current (bs.drop used) :=
      buffers.consume invariant.good invariant.good rfl (fun _ => rfl) (fun _ => rfl)
        (by rw [shape]; rfl) cursor bound inv
    have notSync : s.mode ≠ SYNC := by
      rw [mode]
      decide
    exact ⟨current, h, z, s, used, bound, invariant, ⟨rfl, rfl, rfl, rfl⟩, notSync, packet, ByteViewSizes.refl h,
      cursor, count, put, left, total, bitBound, by omega, Or.inl ⟨.error Ex.leave, run, Or.inl rfl⟩⟩

theorem inflate_TABLE_default_boundary_no_sync {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = TABLE) :
    ∃ regs after stream state used, used ≤ bs.length ∧ DefaultStateJ after r zs stream state ∧
      DefaultConfigFrame s state ∧ state.mode ≠ SYNC ∧
      DispatchBuffers after r regs (bs.drop used) ∧ ByteViewSizes h after ∧
      regs.next = inputAdvance l.next used ∧ regs.have_.toNat + used = l.have_.toNat ∧
      regs.put = l.put ∧ regs.left = l.left ∧ regs.out_ = l.out_ ∧
      regs.bits.toNat ≤ max l.bits.toNat 21 ∧ regs.bits.toNat ≤ l.bits.toNat + 8 * used ∧
      ((∃ outcome, runX (inflate_TABLE c) l h = .ok ((outcome, regs), after) ∧
          (outcome ≠ .ok () ∨ state.mode = BAD)) ∨
       (state.mode = LEN_ ∧ runX (inflate_TABLE c) l h =
          if c.flush = Z_TREES then .ok ((.error Ex.leave, regs), after)
          else runX (inflate_LEN_ c) regs after)) := by
  obtain ⟨first, heap0, stream0, state0, used0, bound0, nextJ, config0, notSync0, packet0, sizes0, cursor0, count0,
    put0, left0, total0, bits0, budget0, stopped | continued⟩ :=
    inflate_TABLE_default_state_entry_no_sync E invariant buffers mode
  · obtain ⟨outcome, run, why⟩ := stopped
    refine ⟨first, heap0, stream0, state0, used0, bound0, nextJ, config0, notSync0, packet0, sizes0, cursor0, count0,
      put0, left0, total0, by omega, budget0, Or.inl ⟨outcome, run, ?_⟩⟩
    rcases why with wait | ⟨_, bad⟩
    · left
      intro impossible
      rw [wait] at impossible
      cases impossible
    · exact Or.inr bad
  · obtain ⟨codesMode, source⟩ := continued
    have E0 : Env c heap0 r zs stream0 state0 := ⟨E.strm, E.st, nextJ.good.live.hz, nextJ.good.live.hs⟩
    obtain ⟨regs, after, stream, state, used1, bound1, finalJ, config1, notSync, packet, sizes, cursor1, count1,
      put1, left1, total1, bits1, budget1, kinds⟩ :=
      inflate_LENLENS_default_boundary_no_sync E0 nextJ packet0 codesMode
    have bound : used0 + used1 ≤ bs.length := by rw [List.length_drop] at bound1; omega
    have cursor : regs.next = inputAdvance l.next (used0 + used1) := by rw [cursor1, cursor0, inputAdvance_add]
    refine ⟨regs, after, stream, state, used0 + used1, bound, finalJ, config0.trans config1, notSync,
      ?_, sizes0.trans sizes, cursor, by omega, put1.trans put0, left1.trans left0, total1.trans total0,
      by omega, by omega, ?_⟩
    · simpa only [List.drop_drop] using packet
    · rcases kinds with stopped | continued
      · obtain ⟨outcome, run, why⟩ := stopped
        exact Or.inl ⟨outcome, source.trans run, why⟩
      · obtain ⟨mode, run⟩ := continued
        exact Or.inr ⟨mode, source.trans run⟩

theorem inflate_dispatch_construction_boundary_no_sync {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = TABLE ∨ s.mode = LENLENS ∨ s.mode = CODELENS) :
    ∃ regs after stream state used, used ≤ bs.length ∧ DefaultStateJ after r zs stream state ∧
      DefaultConfigFrame s state ∧ state.mode ≠ SYNC ∧
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
    exact inflate_TABLE_default_boundary_no_sync E invariant buffers table
  · rw [inflate_dispatch_LENLENS E l lengths]
    exact inflate_LENLENS_default_boundary_no_sync E invariant buffers lengths
  · rw [inflate_dispatch_CODELENS E l codes]
    exact inflate_CODELENS_default_boundary_no_sync E invariant buffers codes

/-- The complete actual construction dispatch cannot enter SYNC. The
constructor boundary and its real LEN_ continuation are both checked. -/
theorem inflate_dispatch_CONSTRUCTION_not_sync
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL}
    {bs : List UInt8}
    (E : Env c h r zs z s)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs)
    (mode : s.mode = TABLE ∨ s.mode = LENLENS ∨
      s.mode = CODELENS)
    (raw : RawFastIO l) :
    ∃ outcome regs after stream state,
      runX (inflate_dispatch c) l h =
        .ok ((outcome, regs), after) ∧
      Good after r zs stream state ∧
      state.mode ≠ SYNC := by
  obtain ⟨regs, after, stream, state, used, bound,
    nextJ, config, notSync, packet, sizes, cursor,
    count, put, left, total, bits, budget,
    stopped | continued⟩ :=
    inflate_dispatch_construction_boundary_no_sync E invariant
      buffers mode
  · obtain ⟨outcome, run, why⟩ := stopped
    exact ⟨outcome, regs, after, stream, state, run,
      nextJ.good, notSync⟩
  · obtain ⟨nextMode, source⟩ := continued
    by_cases trees : c.flush = Z_TREES
    · rw [if_pos trees] at source
      exact ⟨.error Ex.leave, regs, after, stream, state,
        source, nextJ.good, notSync⟩
    · rw [if_neg trees] at source
      have nextEnv : Env c after r zs stream state :=
        ⟨E.strm, E.st, nextJ.good.live.hz,
          nextJ.good.live.hs⟩
      have dataMode : DataTableMode state.mode := by
        rw [nextMode]
        unfold DataTableMode
        decide
      have nextRaw := raw.advance cursor
        (show regs.put = inputAdvance l.put 0 by
          rw [put, inputAdvance_zero])
      obtain ⟨outcome, finalRegs, finalHeap, finalStream,
        finalState, used2, made, bound2, run, finalJ,
        modes, finalPacket, finalSizes, next, haveCount,
        output, leftCount, finalBits, progress⟩ :=
        inflate_dispatch_data_state_rank nextEnv nextJ packet
          dataMode (fun _ => nextRaw)
      have actual : runX (inflate_dispatch c) l h =
          .ok ((outcome, finalRegs), finalHeap) :=
        source.trans
          ((inflate_dispatch_LEN_start nextEnv regs nextMode).symm.trans
            run)
      have finalNotSync : finalState.mode ≠ SYNC := by
        rcases modes with
          (selected | selected | selected | selected | selected |
            selected | selected) | selected | selected <;>
          rw [selected] <;> decide
      exact ⟨outcome, finalRegs, finalHeap, finalStream,
        finalState, actual, finalJ.good, finalNotSync⟩

/-- Dynamic table construction preserves the complete default history
relation, including the flag and SYNC search bound. -/
theorem inflate_dispatch_CONSTRUCTION_default_flag
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL}
    {bs : List UInt8}
    (E : Env c h r zs z s)
    (invariant : DefaultFlagJ h r zs z s)
    (buffers : DispatchBuffers h r l bs)
    (mode : s.mode = TABLE ∨ s.mode = LENLENS ∨
      s.mode = CODELENS)
    (raw : RawFastIO l)
    (incoming : l.bits.toNat ≤ 39) :
    ∃ outcome regs after stream state,
      runX (inflate_dispatch c) l h =
        .ok ((outcome, regs), after) ∧
      DefaultFlagJ after r zs stream state := by
  obtain ⟨outcome, regs, after, stream, state, used, made,
    bound, run, finalJ, packet, sizes, next, count, put,
    left, bits, progress⟩ :=
    inflate_dispatch_construction_default_state_rank E
      invariant.toDefaultStateJ buffers mode raw incoming
  obtain ⟨otherOutcome, otherRegs, otherHeap, otherStream,
    otherState, otherRun, otherGood, flags⟩ :=
    inflate_dispatch_CONSTRUCTION_flags_two E invariant
      buffers mode raw
  rw [run] at otherRun
  cases otherRun
  have sameFlags : otherState = state :=
    Option.some.inj
      (otherGood.live.hs.symm.trans finalJ.good.live.hs)
  subst otherState
  obtain ⟨modeOutcome, modeRegs, modeHeap, modeStream,
    modeState, modeRun, modeGood, notSync⟩ :=
    inflate_dispatch_CONSTRUCTION_not_sync E
      invariant.toDefaultStateJ buffers mode raw
  rw [run] at modeRun
  cases modeRun
  have sameMode : modeState = state :=
    Option.some.inj
      (modeGood.live.hs.symm.trans finalJ.good.live.hs)
  subst modeState
  have search : state.mode = SYNC →
      state.«have».toNat ≤ 4 := by
    intro synced
    exact False.elim (notSync synced)
  exact ⟨outcome, regs, after, stream, state, run,
    ⟨⟨finalJ, search⟩, flags⟩⟩

end Zlib.Inflate.Proofs
