import ZlibF.Proof.«inflate.c.construction-default-state»
import ZlibF.Proof.«inflate.c.normal-mode-base»
import ZlibF.Proof.«inflate.c.fast-view-dispatch-rank»

namespace Zlib.Inflate.Proofs.ConstructionMode
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs
set_option autoImplicit false

/-- Data exits cannot return to dictionary metadata parsing. -/
theorem data_exit_above_dict {mode : UInt32} (allowed : DataExitMode mode) : DICT < mode := by
  rcases allowed with data | rfl | rfl
  · rcases data with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  all_goals decide

/-- The real LEN_ continuation has only payload/control/error successor modes. -/
theorem LEN_start_above_dict
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s returned : InflateState} {l regs : IL} {bs : List UInt8} {outcome : Except Ex Unit}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = LEN_)
    (actual : runX (inflate_LEN_ c) l h = .ok ((outcome, regs), after))
    (get : after.istates zs = some returned) : DICT < returned.mode := by
  have data : DataTableMode s.mode := by rw [mode]; unfold DataTableMode; decide
  obtain ⟨outcome0, regs0, heap0, stream0, state, used, made, bound, run, final,
    modes, packet, sizes, cursor, count, put, left, bits, exits⟩ :=
    inflate_dispatch_data_view_state_rank E invariant buffers data
  have source := (inflate_dispatch_LEN_start E l mode).symm.trans run
  have same := xrun_state_eq source actual final.good.live.hs get
  rw [← same]
  exact data_exit_above_dict modes

/-- Real table refusals end at BAD; successful construction either leaves
at LEN_ under TREES or executes its already proved payload continuation. -/
theorem clTail_above_dict
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s returned : InflateState} {l regs : IL} {bs : List UInt8} {outcome : Except Ex Unit}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (modes : s.mode = BAD ∨ s.mode = CODELENS)
    (done : s.mode = CODELENS → s.«have».toNat = s.nlen.toNat + s.ndist.toNat)
    (format : s.wrap = 0 ∨ s.flags = 0)
    (actual : runX (clTail c) l h = .ok ((outcome, regs), after))
    (get : after.istates zs = some returned) : DICT < returned.mode := by
  rcases clTail_default_state E invariant buffers modes done format with bad | ready
  · obtain ⟨ret, heap0, stream0, state, run, final, _frame, mode, _packet, _sizes, _static⟩ := bad
    have same := xrun_state_eq run actual final.good.live.hs get
    rw [← same, mode]
    decide
  · obtain ⟨heap0, state, final, _frame, mode, packet, _sizes, _static, source⟩ := ready
    by_cases trees : c.flush = Z_TREES
    · rw [if_pos trees] at source
      have same := xrun_state_eq source actual final.good.live.hs get
      rw [← same, mode]
      decide
    · rw [if_neg trees] at source
      have nextEnv : Env c heap0 r zs z state := ⟨E.strm, E.st, final.good.live.hz, final.good.live.hs⟩
      exact LEN_start_above_dict nextEnv final packet mode (source.symm.trans actual) get

/-- Every completed real CODELENS branch stays beyond DICT, including
input exhaustion, malformed repeats, malformed tables and payload exits. -/
theorem CODELENS_above_dict
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s returned : InflateState} {l regs : IL} {bs : List UInt8} {outcome : Except Ex Unit}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = CODELENS)
    (actual : runX (inflate_CODELENS c) l h = .ok ((outcome, regs), after))
    (get : after.istates zs = some returned) : DICT < returned.mode := by
  obtain ⟨decision, readRegs, readHeap, stream0, readState, used, _bound, read, nextJ,
    config, packet, _sizes, _cursor, _count, _put, _left, _total, _bits, _budget, modes, complete⟩ :=
    clRead_default_state_complete E invariant buffers mode
  cases decision with
  | error exit =>
    have source : runX (inflate_CODELENS c) l h = .ok ((.error exit, readRegs), readHeap) := by
      rw [inflate_CODELENS_eq, runX_bind, read]
    have same := xrun_state_eq source actual nextJ.good.live.hs get
    rw [← same]
    rcases modes with selected | selected <;> rw [selected] <;> decide
  | ok unit =>
    cases unit
    have source : runX (inflate_CODELENS c) l h = runX (clTail c) readRegs readHeap := by
      rw [inflate_CODELENS_eq, runX_bind, read]
    have current : Env c readHeap r zs stream0 readState := ⟨E.strm, E.st, nextJ.good.live.hz, nextJ.good.live.hs⟩
    have done : readState.mode = CODELENS → readState.«have».toNat = readState.nlen.toNat + readState.ndist.toNat := by
      intro code
      rcases complete rfl with bad | full
      · rw [code] at bad
        contradiction
      · exact full
    have format : readState.wrap = 0 ∨ readState.flags = 0 := by
      rw [config.2.2.1, config.2.2.2]
      exact invariant.construction_format (Or.inr (Or.inr mode))
    exact clTail_above_dict current nextJ packet modes.symm done format (source.symm.trans actual) get

theorem lenlens_entry_modes {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
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
          ((outcome = .error Ex.leave ∧ state.mode = LENLENS) ∨ (outcome = .ok () ∧ state.mode = BAD))) ∨
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
    have currentMode : state2.mode = LENLENS := by
      have get := nextJ.good.live.hs
      rw [setI_istates_same] at get
      rw [← Option.some.inj get]
      exact mode
    have nextState := invariant.config_update nextJ config format
    exact ⟨regs, _, z, state2, used, bound, nextState, config, packet, sizes, cursor, count,
      put, left, total, bits, budget, Or.inl ⟨.error Ex.leave, run, Or.inl ⟨rfl, currentMode⟩⟩⟩
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
        cursor, count, put, left, total, bits, budget, Or.inl ⟨.ok (), ?_, Or.inr ⟨rfl, rfl⟩⟩⟩
      simpa only [tcBadHeap, ZStreamRef.put_setI, setI_setI] using run




theorem table_entry_modes {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
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
          ((outcome = .error Ex.leave ∧ state.mode = TABLE) ∨ (outcome = .ok () ∧ state.mode = BAD))) ∨
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
      exact ⟨tableRegs current, _, z, state, used, bound, nextState, config, packet, sizes,
        cursor, count, put, left, total, bits, budget, Or.inr ⟨rfl, readyRun invalid⟩⟩
  · obtain ⟨_, _, _, run⟩ := wait leaves
    have packet : DispatchBuffers h r current (bs.drop used) :=
      buffers.consume invariant.good invariant.good rfl (fun _ => rfl) (fun _ => rfl)
        (by rw [shape]; rfl) cursor bound inv
    exact ⟨current, h, z, s, used, bound, invariant, ⟨rfl, rfl, rfl, rfl⟩, packet, ByteViewSizes.refl h,
      cursor, count, put, left, total, bitBound, by omega, Or.inl ⟨.error Ex.leave, run, Or.inl ⟨rfl, mode⟩⟩⟩



#print axioms data_exit_above_dict
#print axioms LEN_start_above_dict
#print axioms clTail_above_dict
#print axioms CODELENS_above_dict
#print axioms lenlens_entry_modes
#print axioms table_entry_modes

/-- The full actual LENLENS dispatch body cannot return to the dictionary
header, including partial alphabet reads and rejected CODES construction. -/
theorem LENLENS_above_dict
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s returned : InflateState} {l regs : IL} {bs : List UInt8} {outcome : Except Ex Unit}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = LENLENS)
    (actual : runX (inflate_LENLENS c) l h = .ok ((outcome, regs), after))
    (get : after.istates zs = some returned) : DICT < returned.mode := by
  obtain ⟨prefixRegs, prefixHeap, prefixZ, prefixState, used, _bound, current, _config,
    packet, _sizes, _cursor, _count, _put, _left, _total, _bits, _budget, parts⟩ :=
    lenlens_entry_modes E invariant buffers mode
  rcases parts with stopped | continued
  · obtain ⟨outcome0, source, why⟩ := stopped
    have same := xrun_state_eq source actual current.good.live.hs get
    rw [← same]
    rcases why with ⟨_wait, selected⟩ | ⟨_normal, selected⟩ <;> rw [selected] <;> decide
  · obtain ⟨nextMode, source⟩ := continued
    have nextEnv : Env c prefixHeap r zs prefixZ prefixState :=
      ⟨E.strm, E.st, current.good.live.hz, current.good.live.hs⟩
    exact CODELENS_above_dict nextEnv current packet nextMode (source.symm.trans actual) get

/-- The actual TABLE header, alphabet loops and payload continuation
have only successor modes strictly beyond the dictionary header. -/
theorem TABLE_above_dict
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s returned : InflateState} {l regs : IL} {bs : List UInt8} {outcome : Except Ex Unit}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = TABLE)
    (actual : runX (inflate_TABLE c) l h = .ok ((outcome, regs), after))
    (get : after.istates zs = some returned) : DICT < returned.mode := by
  obtain ⟨prefixRegs, prefixHeap, prefixZ, prefixState, used, _bound, current, _config,
    packet, _sizes, _cursor, _count, _put, _left, _total, _bits, _budget, parts⟩ :=
    table_entry_modes E invariant buffers mode
  rcases parts with stopped | continued
  · obtain ⟨outcome0, source, why⟩ := stopped
    have same := xrun_state_eq source actual current.good.live.hs get
    rw [← same]
    rcases why with ⟨_wait, selected⟩ | ⟨_normal, selected⟩ <;> rw [selected] <;> decide
  · obtain ⟨nextMode, source⟩ := continued
    have nextEnv : Env c prefixHeap r zs prefixZ prefixState :=
      ⟨E.strm, E.st, current.good.live.hz, current.good.live.hs⟩
    exact LENLENS_above_dict nextEnv current packet nextMode (source.symm.trans actual) get

/-- Every complete actual dispatch entered in construction stays strictly
beyond DICT on every ordinary outcome. No valid-format assumption or
promised callee mode invariant is used. -/
theorem dispatch_above_dict
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s returned : InflateState} {l regs : IL} {bs : List UInt8} {outcome : Except Ex Unit}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = TABLE ∨ s.mode = LENLENS ∨ s.mode = CODELENS)
    (actual : runX (inflate_dispatch c) l h = .ok ((outcome, regs), after))
    (get : after.istates zs = some returned) : DICT < returned.mode := by
  rcases mode with table | lengths | codes
  · exact TABLE_above_dict E invariant buffers table ((inflate_dispatch_TABLE E l table).symm.trans actual) get
  · exact LENLENS_above_dict E invariant buffers lengths ((inflate_dispatch_LENLENS E l lengths).symm.trans actual) get
  · exact CODELENS_above_dict E invariant buffers codes ((inflate_dispatch_CODELENS E l codes).symm.trans actual) get

#print axioms LENLENS_above_dict
#print axioms TABLE_above_dict
#print axioms dispatch_above_dict

end Zlib.Inflate.Proofs.ConstructionMode
