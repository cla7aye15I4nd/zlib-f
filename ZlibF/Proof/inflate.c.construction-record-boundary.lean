import ZlibF.Proof.«inflate.c.construction-record-headers»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Compose both actual alphabet headers and constructors on the same
initialized state, retaining the private frame before real LEN_. -/
theorem inflate_LENLENS_default_record_boundary {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = LENLENS) :
    ∃ regs after stream state used, used ≤ bs.length ∧ DefaultStateJ after r zs stream state ∧
      DefaultConfigFrame s state ∧ RecordFrame r (some (.tab zs)) h after ∧
      DispatchBuffers after r regs (bs.drop used) ∧ ByteViewSizes h after ∧
      regs.next = inputAdvance l.next used ∧ regs.have_.toNat + used = l.have_.toNat ∧
      regs.put = l.put ∧ regs.left = l.left ∧ regs.out_ = l.out_ ∧
      regs.bits.toNat ≤ max l.bits.toNat 21 ∧ regs.bits.toNat ≤ l.bits.toNat + 8 * used ∧
      ((∃ outcome, runX (inflate_LENLENS c) l h = .ok ((outcome, regs), after) ∧
          (outcome ≠ .ok () ∨ state.mode = BAD)) ∨
       (state.mode = LEN_ ∧ runX (inflate_LENLENS c) l h =
          if c.flush = Z_TREES then .ok ((.error Ex.leave, regs), after)
          else runX (inflate_LEN_ c) regs after)) := by
  obtain ⟨first, heap0, stream0, state0, used0, bound0, nextJ, config0, frame0, packet0, sizes0, cursor0, count0,
    put0, left0, total0, bits0, budget0, stopped | continued⟩ :=
    inflate_LENLENS_default_record_entry E invariant buffers mode
  · obtain ⟨outcome, run, why⟩ := stopped
    refine ⟨first, heap0, stream0, state0, used0, bound0, nextJ, config0, frame0, packet0, sizes0, cursor0, count0,
      put0, left0, total0, by omega, budget0, Or.inl ⟨outcome, run, ?_⟩⟩
    rcases why with wait | ⟨_, bad⟩
    · left
      intro impossible
      rw [wait] at impossible
      cases impossible
    · exact Or.inr bad
  · obtain ⟨codesMode, source⟩ := continued
    have E0 : Env c heap0 r zs stream0 state0 := ⟨E.strm, E.st, nextJ.good.live.hz, nextJ.good.live.hs⟩
    obtain ⟨regs, after, stream, state, used1, bound1, finalJ, config1, frame1, packet, sizes, cursor1, count1,
      put1, left1, total1, bits1, budget1, kinds⟩ :=
      inflate_CODELENS_default_record_boundary E0 nextJ packet0 codesMode
    have bound : used0 + used1 ≤ bs.length := by rw [List.length_drop] at bound1; omega
    have cursor : regs.next = inputAdvance l.next (used0 + used1) := by rw [cursor1, cursor0, inputAdvance_add]
    refine ⟨regs, after, stream, state, used0 + used1, bound, finalJ, config0.trans config1, frame0.trans frame1,
      ?_, sizes0.trans sizes, cursor, by omega, put1.trans put0, left1.trans left0, total1.trans total0,
      by omega, by omega, ?_⟩
    · simpa only [List.drop_drop] using packet
    · rcases kinds with stopped | continued
      · obtain ⟨outcome, run, why⟩ := stopped
        exact Or.inl ⟨outcome, source.trans run, why⟩
      · obtain ⟨mode, run⟩ := continued
        exact Or.inr ⟨mode, source.trans run⟩

/-- Compose TABLE and both real table alphabets without changing caller byte views. -/
theorem inflate_TABLE_default_record_boundary {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = TABLE) :
    ∃ regs after stream state used, used ≤ bs.length ∧ DefaultStateJ after r zs stream state ∧
      DefaultConfigFrame s state ∧ RecordFrame r (some (.tab zs)) h after ∧
      DispatchBuffers after r regs (bs.drop used) ∧ ByteViewSizes h after ∧
      regs.next = inputAdvance l.next used ∧ regs.have_.toNat + used = l.have_.toNat ∧
      regs.put = l.put ∧ regs.left = l.left ∧ regs.out_ = l.out_ ∧
      regs.bits.toNat ≤ max l.bits.toNat 21 ∧ regs.bits.toNat ≤ l.bits.toNat + 8 * used ∧
      ((∃ outcome, runX (inflate_TABLE c) l h = .ok ((outcome, regs), after) ∧
          (outcome ≠ .ok () ∨ state.mode = BAD)) ∨
       (state.mode = LEN_ ∧ runX (inflate_TABLE c) l h =
          if c.flush = Z_TREES then .ok ((.error Ex.leave, regs), after)
          else runX (inflate_LEN_ c) regs after)) := by
  obtain ⟨first, heap0, stream0, state0, used0, bound0, nextJ, config0, frame0, packet0, sizes0, cursor0, count0,
    put0, left0, total0, bits0, budget0, stopped | continued⟩ :=
    inflate_TABLE_default_record_entry E invariant buffers mode
  · obtain ⟨outcome, run, why⟩ := stopped
    refine ⟨first, heap0, stream0, state0, used0, bound0, nextJ, config0, frame0, packet0, sizes0, cursor0, count0,
      put0, left0, total0, by omega, budget0, Or.inl ⟨outcome, run, ?_⟩⟩
    rcases why with wait | ⟨_, bad⟩
    · left
      intro impossible
      rw [wait] at impossible
      cases impossible
    · exact Or.inr bad
  · obtain ⟨codesMode, source⟩ := continued
    have E0 : Env c heap0 r zs stream0 state0 := ⟨E.strm, E.st, nextJ.good.live.hz, nextJ.good.live.hs⟩
    obtain ⟨regs, after, stream, state, used1, bound1, finalJ, config1, frame1, packet, sizes, cursor1, count1,
      put1, left1, total1, bits1, budget1, kinds⟩ :=
      inflate_LENLENS_default_record_boundary E0 nextJ packet0 codesMode
    have bound : used0 + used1 ≤ bs.length := by rw [List.length_drop] at bound1; omega
    have cursor : regs.next = inputAdvance l.next (used0 + used1) := by rw [cursor1, cursor0, inputAdvance_add]
    refine ⟨regs, after, stream, state, used0 + used1, bound, finalJ, config0.trans config1, frame0.trans frame1,
      ?_, sizes0.trans sizes, cursor, by omega, put1.trans put0, left1.trans left0, total1.trans total0,
      by omega, by omega, ?_⟩
    · simpa only [List.drop_drop] using packet
    · rcases kinds with stopped | continued
      · obtain ⟨outcome, run, why⟩ := stopped
        exact Or.inl ⟨outcome, source.trans run, why⟩
      · obtain ⟨mode, run⟩ := continued
        exact Or.inr ⟨mode, source.trans run⟩

/-- The actual construction dispatch retains the frame through its complete prefix. -/
theorem inflate_dispatch_construction_record_boundary {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = TABLE ∨ s.mode = LENLENS ∨ s.mode = CODELENS) :
    ∃ regs after stream state used, used ≤ bs.length ∧ DefaultStateJ after r zs stream state ∧
      DefaultConfigFrame s state ∧ RecordFrame r (some (.tab zs)) h after ∧
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
    exact inflate_TABLE_default_record_boundary E invariant buffers table
  · rw [inflate_dispatch_LENLENS E l lengths]
    exact inflate_LENLENS_default_record_boundary E invariant buffers lengths
  · rw [inflate_dispatch_CODELENS E l codes]
    exact inflate_CODELENS_default_record_boundary E invariant buffers codes

end Zlib.Inflate.Proofs
