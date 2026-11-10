import ZlibF.Proof.«inflate.c.return-lenlens»
import ZlibF.Proof.«inflate.c.table-mode»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Actual TABLE parsing establishes the precise LENLENS entry clause.
Invalid counts take BAD before the continuation; partial input retains J.
The fourteen source bits and exact input cursor are accounted on one run. -/
theorem inflate_TABLE_return_entry {allowed : Int32 → Prop} {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (incoming : allowed l.ret) (E : Env c h r zs z s) (invariant : DefaultDecodeJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = TABLE) :
    ∃ regs after stream state used, used ≤ bs.length ∧ DefaultDecodeJ after r zs stream state ∧
      DispatchBuffers after r regs (bs.drop used) ∧ ByteViewSizes h after ∧
      regs.next = inputAdvance l.next used ∧ regs.have_.toNat + used = l.have_.toNat ∧
      regs.put = l.put ∧ regs.left = l.left ∧ regs.out_ = l.out_ ∧
      regs.bits.toNat ≤ max l.bits.toNat 21 ∧ regs.bits.toNat ≤ l.bits.toNat + 8 * used ∧
      ((∃ outcome, runX (inflate_TABLE c) l h = .ok ((outcome, regs), after) ∧
          (outcome = .error Ex.leave ∨ (outcome = .ok () ∧ state.mode = BAD)) ∧
          ReturnPhase allowed outcome regs state) ∨
       (state.mode = LENLENS ∧ allowed regs.ret ∧ runX (inflate_TABLE c) l h = runX (inflate_LENLENS c) regs after)) := by
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
  have ret : current.ret = l.ret := by rw [shape]
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
      have nextJ := invariant.counts_update frame (stream := stream) (by rfl) (Or.inl rfl) lengths
      obtain ⟨packet, sizes⟩ := buffers.metadata_advance invariant.good nextJ.good rfl dropInv
        cursor count put left total
      refine ⟨tableRegs current, _, stream, state, used, bound, nextJ, packet, sizes,
        cursor, count, put, left, total, bits, budget, Or.inl ⟨.ok (), ?_, Or.inr ⟨rfl, rfl⟩, Or.inr ⟨rfl, rfl⟩⟩⟩
      exact run
    · let state := { tableCounts s current.hold with «have» := 0, mode := LENLENS }
      have frame : TableCountsFrame s state := by rfl
      have lengths : LengthHeaderInvariant state := tableCounts_header_invariant s current.hold invalid
      have nextJ := invariant.counts_update frame (stream := z) (by rfl) (Or.inr rfl) lengths
      obtain ⟨packet, sizes⟩ := buffers.metadata_advance invariant.good nextJ.good rfl dropInv
        cursor count put left total
      rw [ZStreamRef.put_self E.hz] at nextJ packet sizes
      exact ⟨tableRegs current, _, z, state, used, bound, nextJ, packet, sizes,
        cursor, count, put, left, total, bits, budget, Or.inr ⟨rfl, (by change allowed current.ret; rw [ret]; exact incoming), readyRun invalid⟩⟩
  · obtain ⟨_, _, _, run⟩ := wait leaves
    have packet : DispatchBuffers h r current (bs.drop used) :=
      buffers.consume invariant.good invariant.good rfl (fun _ => rfl) (fun _ => rfl)
        (by rw [shape]; rfl) cursor bound inv
    exact ⟨current, h, z, s, used, bound, invariant, packet, ByteViewSizes.refl h,
      cursor, count, put, left, total, bitBound, by omega, Or.inl ⟨.error Ex.leave, run, Or.inl rfl, Or.inl (by rw [ret]; exact incoming)⟩⟩

/-- TABLE either leaves with an admitted register, stops normally in
BAD, or executes the actual LENLENS continuation with an admitted code. -/
theorem inflate_TABLE_return_phase
    {allowed : Int32 → Prop} {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s state : InflateState} {l regs : IL} {bs : List UInt8}
    {outcome : Except Ex Unit}
    (zero : allowed 0) (E : Env c h r zs z s) (invariant : DefaultDecodeJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = TABLE) (incoming : allowed l.ret)
    (run : runX (inflate_TABLE c) l h = .ok ((outcome, regs), after))
    (getAfter : after.istates zs = some state) : ReturnPhase allowed outcome regs state := by
  obtain ⟨first, heap, stream, current, used, bound, final, packet, sizes, next, count,
    put, left, total, bits, budget, stopped | continued⟩ :=
    inflate_TABLE_return_entry incoming E invariant buffers mode
  · obtain ⟨decision, source, why, phase⟩ := stopped
    have same := Except.ok.inj (source.symm.trans run)
    have regsEq : first = regs := congrArg (fun pair => pair.1.2) same
    have heapEq : heap = after := congrArg Prod.snd same
    have decisionEq : decision = outcome := congrArg (fun pair => pair.1.1) same
    have currentGet : after.istates zs = some current := by rw [← heapEq]; exact final.good.live.hs
    have stateEq : current = state := Option.some.inj (currentGet.symm.trans getAfter)
    simpa only [regsEq, decisionEq, stateEq] using phase
  · obtain ⟨mode, code, source⟩ := continued
    have env : Env c heap r zs stream current := ⟨E.strm, E.st, final.good.live.hz, final.good.live.hs⟩
    exact inflate_LENLENS_return_phase zero env final packet mode code (source.symm.trans run) getAfter

end Zlib.Inflate.Proofs
