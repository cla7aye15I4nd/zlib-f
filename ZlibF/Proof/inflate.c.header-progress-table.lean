import ZlibF.Proof.«inflate.c.header-progress»
import ZlibF.Proof.«inflate.c.origin-fields-construction-headers»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Actual TABLE execution establishes the initialized phase word at the
LENLENS source cut. Waiting and invalid-count exits remain included.
The initial index is the actual remaining held word, with have zero.
It is derived at the call, not supplied by the caller. -/
theorem inflate_TABLE_header_progress_entry {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultOriginState h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = TABLE) :
    ∃ regs after stream state used, used ≤ bs.length ∧ DefaultOriginState after r zs stream state ∧
      DefaultConfigFrame s state ∧ RecordFrame r (some (.tab zs)) h after ∧
      DispatchBuffers after r regs (bs.drop used) ∧ ByteViewSizes h after ∧
      regs.next = inputAdvance l.next used ∧ regs.have_.toNat + used = l.have_.toNat ∧
      regs.put = l.put ∧ regs.left = l.left ∧ regs.out_ = l.out_ ∧
      regs.bits.toNat ≤ max l.bits.toNat 21 ∧ regs.bits.toNat ≤ l.bits.toNat + 8 * used ∧
      ((∃ outcome, runX (inflate_TABLE c) l h = .ok ((outcome, regs), after) ∧
          (outcome = .error Ex.leave ∨ (outcome = .ok () ∧ state.mode = BAD))) ∨
       (state.mode = LENLENS ∧ state.«have» = 0 ∧
        LenlensProgress state regs.hold regs.bits (natBits regs.bits.toNat regs.hold.toNat) ∧
        runX (inflate_TABLE c) l h = runX (inflate_LENLENS c) regs after)) := by
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
      have nextJ := invariant.toDefaultStateJ.toDefaultDecodeJ.counts_update frame (stream := stream) (by rfl) (Or.inl rfl) lengths
      obtain ⟨packet, sizes⟩ := buffers.metadata_advance invariant.good nextJ.good rfl dropInv
        cursor count put left total
      have config : DefaultConfigFrame s state := by rw [frame]; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
      have nextState := invariant.toDefaultStateJ.config_update nextJ config format
      have nextOrigin := invariant.of_fields nextState rfl rfl rfl
      refine ⟨tableRegs current, _, stream, state, used, bound, nextOrigin, config, RecordFrame.stream_state E.hz E.hs stream state, packet, sizes,
        cursor, count, put, left, total, bits, budget, Or.inl ⟨.ok (), ?_, Or.inr ⟨rfl, rfl⟩⟩⟩
      exact run
    · let state := { tableCounts s current.hold with «have» := 0, mode := LENLENS }
      have frame : TableCountsFrame s state := by rfl
      have lengths : LengthHeaderInvariant state := tableCounts_header_invariant s current.hold invalid
      have nextJ := invariant.toDefaultStateJ.toDefaultDecodeJ.counts_update frame (stream := z) (by rfl) (Or.inr rfl) lengths
      obtain ⟨packet, sizes⟩ := buffers.metadata_advance invariant.good nextJ.good rfl dropInv
        cursor count put left total
      rw [ZStreamRef.put_self E.hz] at nextJ packet sizes
      have config : DefaultConfigFrame s state := by rw [frame]; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
      have nextState := invariant.toDefaultStateJ.config_update nextJ config format
      have nextOrigin := invariant.of_fields nextState rfl rfl rfl
      exact ⟨tableRegs current, _, z, state, used, bound, nextOrigin, config, RecordFrame.setI r zs E.hs state, packet, sizes,
        cursor, count, put, left, total, bits, budget, Or.inr ⟨rfl, rfl, LenlensProgress.initial rfl _ _, readyRun invalid⟩⟩
  · obtain ⟨_, _, _, run⟩ := wait leaves
    have packet : DispatchBuffers h r current (bs.drop used) :=
      buffers.consume invariant.good invariant.good rfl (fun _ => rfl) (fun _ => rfl)
        (by rw [shape]; rfl) cursor bound inv
    exact ⟨current, h, z, s, used, bound, invariant, ⟨rfl, rfl, rfl, rfl, rfl⟩, RecordFrame.refl r _ h, packet, ByteViewSizes.refl h,
      cursor, count, put, left, total, bitBound, by omega, Or.inl ⟨.error Ex.leave, run, Or.inl rfl⟩⟩

#print axioms inflate_TABLE_header_progress_entry
end Zlib.Inflate.Proofs
