import ZlibF.Proof.«inflate.c.default-dispatch-normal-not-length»
namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

theorem inflate_LENLENS_default_state_entry_wait_modes {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
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
          (state.mode = LENLENS ∨ state.mode = BAD)) ∨
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
    have waitMode : state2.mode = LENLENS := by
      have get := nextJ.good.live.hs
      rw [setI_istates_same] at get
      rw [← Option.some.inj get]
      change s.mode = LENLENS
      exact mode
    exact ⟨regs, _, z, state2, used, bound, nextState, config, packet, sizes, cursor, count,
      put, left, total, bits, budget, Or.inl ⟨.error Ex.leave, run, Or.inl waitMode⟩⟩
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
      have config : DefaultConfigFrame s state := by rw [frame]; exact ⟨rfl, rfl, rfl, rfl⟩
      have nextState := invariant.config_update nextJ config format
      refine ⟨{ regs with ret := -1 }, _, stream, state, used, bound, nextState, config, packet, sizes,
        cursor, count, put, left, total, bits, budget, Or.inl ⟨.ok (), ?_, Or.inr rfl⟩⟩
      simpa only [tcBadHeap, ZStreamRef.put_setI, setI_setI] using run



theorem inflate_TABLE_default_state_entry_wait_modes {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
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
          (state.mode = TABLE ∨ state.mode = BAD)) ∨
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
      refine ⟨tableRegs current, _, stream, state, used, bound, nextState, config, packet, sizes,
        cursor, count, put, left, total, bits, budget, Or.inl ⟨.ok (), ?_, Or.inr rfl⟩⟩
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
      exact ⟨tableRegs current, _, z, state, used, bound, nextState, config, packet, sizes,
        cursor, count, put, left, total, bits, budget, Or.inr ⟨rfl, readyRun invalid⟩⟩
  · obtain ⟨_, _, _, run⟩ := wait leaves
    have packet : DispatchBuffers h r current (bs.drop used) :=
      buffers.consume invariant.good invariant.good rfl (fun _ => rfl) (fun _ => rfl)
        (by rw [shape]; rfl) cursor bound inv
    exact ⟨current, h, z, s, used, bound, invariant, ⟨rfl, rfl, rfl, rfl⟩, packet, ByteViewSizes.refl h,
      cursor, count, put, left, total, bitBound, by omega, Or.inl ⟨.error Ex.leave, run, Or.inl mode⟩⟩



/-- Every actual CODELENS return excludes LENGTH, including input waits. -/
theorem inflate_CODELENS_returning_not_length
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s returned : InflateState} {l regs : IL} {bs : List UInt8} {outcome : Except Ex Unit}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = CODELENS)
    (run : runX (inflate_CODELENS c) l h = .ok ((outcome, regs), after))
    (get : after.istates zs = some returned) : returned.mode ≠ LENGTH := by
  obtain ⟨readOutcome, readRegs, readHeap, readZ, readState, used, _, read, current,
    config, packet, _, _, _, _, _, _, _, _, modes, complete⟩ :=
    clRead_default_state_complete E invariant buffers mode
  cases readOutcome with
  | error exit =>
    have source : runX (inflate_CODELENS c) l h = .ok ((.error exit, readRegs), readHeap) := by
      rw [inflate_CODELENS_eq, runX_bind, read]
    have same := xrun_state_eq source run current.good.live.hs get
    rw [← same]
    rcases modes with selected | selected <;> rw [selected] <;> decide
  | ok unit =>
    cases unit
    have source : runX (inflate_CODELENS c) l h = runX (clTail c) readRegs readHeap := by
      rw [inflate_CODELENS_eq, runX_bind, read]
    have env : Env c readHeap r zs readZ readState :=
      ⟨E.strm, E.st, current.good.live.hz, current.good.live.hs⟩
    have done : readState.mode = CODELENS → readState.«have».toNat = readState.nlen.toNat + readState.ndist.toNat := by
      intro code
      rcases complete rfl with bad | full
      · rw [code] at bad
        cases bad
      · exact full
    have format : readState.wrap = 0 ∨ readState.flags = 0 := by
      rw [config.2.2.1, config.2.2.2]
      exact invariant.construction_format (Or.inr (Or.inr mode))
    rcases clTail_default_state env current packet modes.symm done format with bad | ready
    · obtain ⟨ret, heap, stream, state, tailRun, final, _, badMode, _⟩ := bad
      have same := xrun_state_eq (source.trans tailRun) run final.good.live.hs get
      rw [← same, badMode]
      decide
    · obtain ⟨heap, state, final, _, nextMode, nextPacket, _, _, tailRun⟩ := ready
      by_cases trees : c.flush = Z_TREES
      · rw [if_pos trees] at tailRun
        have same := xrun_state_eq (source.trans tailRun) run final.good.live.hs get
        rw [← same, nextMode]
        decide
      · rw [if_neg trees] at tailRun
        have nextEnv : Env c heap r zs readZ state :=
          ⟨E.strm, E.st, final.good.live.hz, final.good.live.hs⟩
        have data : DataTableMode state.mode := by rw [nextMode]; unfold DataTableMode; decide
        obtain ⟨finalOutcome, finalRegs, finalHeap, finalZ, finalState, used2, made, _, dataRun, finalJ,
          finalModes, _⟩ := inflate_dispatch_data_view_state_rank nextEnv final nextPacket data
        have actual := source.trans (tailRun.trans ((inflate_dispatch_LEN_start nextEnv _ nextMode).symm.trans dataRun))
        have same := xrun_state_eq actual run finalJ.good.live.hs get
        rw [← same]
        exact finalModes.not_length

/-- Every actual LENLENS return excludes LENGTH, including alphabet waits. -/
theorem inflate_LENLENS_returning_not_length
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s returned : InflateState} {l regs : IL} {bs : List UInt8} {outcome : Except Ex Unit}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = LENLENS)
    (run : runX (inflate_LENLENS c) l h = .ok ((outcome, regs), after))
    (get : after.istates zs = some returned) : returned.mode ≠ LENGTH := by
  obtain ⟨first, heap, stream, state, used, _, current, _, packet, _, _, _, _, _, _, _, _, parts⟩ :=
    inflate_LENLENS_default_state_entry_wait_modes E invariant buffers mode
  rcases parts with stopped | continued
  · obtain ⟨exit, source, modes⟩ := stopped
    have same := xrun_state_eq source run current.good.live.hs get
    rw [← same]
    rcases modes with selected | selected <;> rw [selected] <;> decide
  · obtain ⟨codeMode, source⟩ := continued
    exact inflate_CODELENS_returning_not_length
      ⟨E.strm, E.st, current.good.live.hz, current.good.live.hs⟩ current packet codeMode
      (source.symm.trans run) get

/-- Every actual TABLE return excludes LENGTH, including count waits. -/
theorem inflate_TABLE_returning_not_length
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s returned : InflateState} {l regs : IL} {bs : List UInt8} {outcome : Except Ex Unit}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = TABLE)
    (run : runX (inflate_TABLE c) l h = .ok ((outcome, regs), after))
    (get : after.istates zs = some returned) : returned.mode ≠ LENGTH := by
  obtain ⟨first, heap, stream, state, used, _, current, _, packet, _, _, _, _, _, _, _, _, parts⟩ :=
    inflate_TABLE_default_state_entry_wait_modes E invariant buffers mode
  rcases parts with stopped | continued
  · obtain ⟨exit, source, modes⟩ := stopped
    have same := xrun_state_eq source run current.good.live.hs get
    rw [← same]
    rcases modes with selected | selected <;> rw [selected] <;> decide
  · obtain ⟨codeMode, source⟩ := continued
    exact inflate_LENLENS_returning_not_length
      ⟨E.strm, E.st, current.good.live.hz, current.good.live.hs⟩ current packet codeMode
      (source.symm.trans run) get

/-- Any returning outcome of actual construction dispatch excludes LENGTH.
The stopped modes are derived from actual count/alphabet/read source programs. -/
theorem inflate_dispatch_construction_result_not_length
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s returned : InflateState} {l regs : IL} {bs : List UInt8} {result : Except Ex Unit}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = TABLE ∨ s.mode = LENLENS ∨ s.mode = CODELENS)
    (run : runX (inflate_dispatch c) l h = .ok ((result, regs), after))
    (get : after.istates zs = some returned) : returned.mode ≠ LENGTH := by
  rcases mode with table | lens | code
  · exact inflate_TABLE_returning_not_length E invariant buffers table
      ((inflate_dispatch_TABLE E l table).symm.trans run) get
  · exact inflate_LENLENS_returning_not_length E invariant buffers lens
      ((inflate_dispatch_LENLENS E l lens).symm.trans run) get
  · exact inflate_CODELENS_returning_not_length E invariant buffers code
      ((inflate_dispatch_CODELENS E l code).symm.trans run) get

#print axioms inflate_LENLENS_default_state_entry_wait_modes
#print axioms inflate_TABLE_default_state_entry_wait_modes
#print axioms inflate_CODELENS_returning_not_length
#print axioms inflate_LENLENS_returning_not_length
#print axioms inflate_TABLE_returning_not_length
#print axioms inflate_dispatch_construction_result_not_length
end Zlib.Inflate.Proofs
