import ZlibF.Proof.«inflate.c.lenlens-code-length-cursor»
import ZlibF.Proof.«inflate.c.origin-fields-construction-headers»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

set_option maxHeartbeats 400000 in
/-- The actual length-alphabet prefix retains the semantic table-state
component on input exhaustion and refusal, and establishes it from the
real constructor on CODELENS entry. -/
theorem inflate_LENLENS_code_length_entry {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultOriginState h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = LENLENS) :
    ∃ regs after stream state used, used ≤ bs.length ∧ DefaultCodeLengthState after r zs stream state ∧
      DefaultConfigFrame s state ∧ RecordFrame r (some (.tab zs)) h after ∧
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
    inflate_LENLENS_code_length_cursor E.strm E.st E.hz E.hs invariant.good.inv.wf ncode haveBound prefixValues buffers.bits
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
      packet, sizes, _, count2, _, _, _, _, _⟩ := ll1_default_J E invariant.toDefaultStateJ.toDefaultDecodeJ buffers mode
    rw [read] at read2
    cases read2
    have sameUse : used2 = used := by omega
    subst used2
    have config : DefaultConfigFrame s state2 := by
      have get := nextJ.good.live.hs
      rw [setI_istates_same] at get
      rw [← Option.some.inj get]
      simp only [DefaultConfigFrame, llSt, and_self, eq_self]
    have nextState := invariant.toDefaultStateJ.config_update nextJ config format
    have fields : originStateFields state2 = originStateFields s := by
      have get := nextJ.good.live.hs
      rw [setI_istates_same] at get
      rw [← Option.some.inj get]
      rfl
    have nextOrigin := invariant.of_fields nextState (congrArg Prod.fst fields)
      (congrArg (fun value => value.2.1) fields) (congrArg (fun value => value.2.2) fields)
    have inactive : state2.mode ≠ CODELENS := by
      have get := nextJ.good.live.hs
      rw [setI_istates_same] at get
      rw [← Option.some.inj get]
      change s.mode ≠ CODELENS
      rw [mode]
      decide
    have nextMeaning := nextOrigin.code_length_inactive inactive
    exact ⟨regs, _, z, state2, used, bound, nextMeaning, config, RecordFrame.setI r zs E.hs _, packet, sizes, cursor, count,
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
        llOkSt_codeLengthInvariant zs filled usedCodes root work codes safe.safe nlen ndist
      have bitInv : BitInv h { regs with ret := 0 } (bs.drop used) := ⟨inv.have_eq, inv.next, inv.hold_lt⟩
      obtain ⟨nextJ, packet, sizes⟩ := invariant.toDefaultStateJ.toDefaultDecodeJ.length_table_packet buffers frame
        (stream := z) (by rfl) wf pointers (Or.inr rfl) codeInv bitInv cursor count put left total
      rw [ZStreamRef.put_self E.hz] at nextJ packet sizes
      have config : DefaultConfigFrame s state := by rw [frame]; exact ⟨rfl, rfl, rfl, rfl⟩
      have nextState := invariant.toDefaultStateJ.config_update nextJ config format
      have nextOrigin : DefaultOriginState _ r zs _ state :=
        ⟨nextState, invariant.flagsOrigin, Or.inl rfl⟩
      have nextMeaning : DefaultCodeLengthState _ r zs _ state :=
        ⟨nextOrigin, fun _ => ⟨_, safe⟩⟩
      exact ⟨{ regs with ret := 0 }, _, z, state, used, bound, nextMeaning, config, RecordFrame.setI r zs E.hs _, packet, sizes,
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
      obtain ⟨nextJ, packet, sizes⟩ := invariant.toDefaultStateJ.toDefaultDecodeJ.length_table_packet buffers frame
        (stream := stream) (by rfl) wf pointers (Or.inl rfl) codeInv bitInv cursor count put left total
      have config : DefaultConfigFrame s state := by rw [frame]; exact ⟨rfl, rfl, rfl, rfl⟩
      have nextState := invariant.toDefaultStateJ.config_update nextJ config format
      have nextOrigin : DefaultOriginState _ r zs _ state :=
        ⟨nextState, invariant.flagsOrigin, Or.inl rfl⟩
      have nextMeaning := nextOrigin.code_length_inactive (by change BAD ≠ CODELENS; decide)
      refine ⟨{ regs with ret := -1 }, _, stream, state, used, bound, nextMeaning, config, RecordFrame.stream_state E.hz E.hs stream state, packet, sizes,
        cursor, count, put, left, total, bits, budget, Or.inl ⟨.ok (), ?_, Or.inr ⟨rfl, rfl⟩⟩⟩
      simpa only [tcBadHeap, ZStreamRef.put_setI, setI_setI] using run


#print axioms inflate_LENLENS_code_length_entry
end Zlib.Inflate.Proofs
