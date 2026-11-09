import ZlibF.Proof.«inflate.c.local-block-type»
import ZlibF.Proof.«inflate.c.local-stored»
import ZlibF.Proof.«inflate.c.control-rank»

/-! Actual decoder execution with local allocation uniqueness. -/
namespace Zlib.Inflate.Local
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Inffast.Spec ZlibF.Spec.Public
set_option autoImplicit false
set_option maxRecDepth 8192

theorem inflate_TYPEDO_rank {c : Ctx} {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (good : LocalGood h cutoff r zs z s) (pending : DataPendingInvariant s)
    (buffers : DispatchBuffers h r l bs) (globals : LibraryGlobals h)
    (mode : s.mode = TYPE ∨ s.mode = TYPEDO) (incoming : l.bits.toNat ≤ 39) :
    ∃ outcome regs after stream state used, used ≤ bs.length ∧
      runX (inflate_TYPEDO c) l h = .ok ((outcome, regs), after) ∧
      LocalGood after cutoff r zs stream state ∧ DataTableInvariant after state ∧ DataPendingInvariant state ∧
      DispatchBuffers after r regs (bs.drop used) ∧ ByteViewSizes h after ∧
      regs.next = inputAdvance l.next used ∧ regs.have_.toNat + used = l.have_.toNat ∧
      regs.put = l.put ∧ regs.left = l.left ∧ regs.bits.toNat ≤ 39 ∧ after.static = h.static ∧
      BlockHeaderFrame s state ∧ HeaderStreamFrame z stream ∧
      (outcome = .error Ex.leave ∨ (outcome = .ok () ∧ dispatchRank regs state.mode < dispatchRank l s.mode)) := by
  by_cases last : s.last = 0
  · obtain ⟨outcome, regs, after, stream, state, used, consumed, bound, run, current, tables,
      nextPending, packet, sizes, next, count, put, left, bitCount, bitBound, static, stateFrame,
      streamFrame, kinds, progress⟩ := inflate_TYPEDO_boundary E good pending buffers globals mode
    refine ⟨outcome, regs, after, stream, state, used, bound, run, current, tables, nextPending,
      packet, sizes, next, count, put, left, by omega, static, stateFrame, streamFrame, ?_⟩
    rcases kinds with normal | wait
    · have consumedEq : consumed = 3 := progress last normal
      have strict : dispatchMass regs < dispatchMass l := by
        unfold dispatchMass
        rw [left]
        rw [consumedEq] at bitCount
        omega
      exact Or.inr ⟨normal, dispatchRank_mass_strict strict⟩
    · exact Or.inl wait
  · obtain ⟨run, current, tables, nextPending, packet, sizes, bitBound, static, frame⟩ :=
      inflate_TYPEDO_last_boundary E good pending buffers last
    have credit : dispatchCredit CHECK < dispatchCredit s.mode := by
      rcases mode with mode | mode <;> rw [mode] <;> decide
    have decreases : dispatchRank (bytebits l) CHECK < dispatchRank l s.mode := by
      apply dispatchRank_advance (used := 0) (made := 0) (by rfl) (by rfl)
      · simpa only [Nat.mul_zero, Nat.add_zero] using bitBound
      · exact Or.inr credit
    exact ⟨.ok (), bytebits l, setI h zs { s with mode := CHECK }, z, { s with mode := CHECK },
      0, by omega, run, current, tables, nextPending, by simpa only [List.drop_zero] using packet,
      sizes, (inputAdvance_zero l.next).symm, by rfl, rfl, rfl, by omega, static,
      frame, by rfl, Or.inr ⟨rfl, decreases⟩⟩

theorem inflate_TYPE_rank {c : Ctx} {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (good : LocalGood h cutoff r zs z s) (pending : DataPendingInvariant s)
    (buffers : DispatchBuffers h r l bs) (globals : LibraryGlobals h)
    (mode : s.mode = TYPE) (incoming : l.bits.toNat ≤ 39) :
    ∃ outcome regs after stream state used, used ≤ bs.length ∧
      runX (inflate_TYPE c) l h = .ok ((outcome, regs), after) ∧
      LocalGood after cutoff r zs stream state ∧ DataTableInvariant after state ∧ DataPendingInvariant state ∧
      DispatchBuffers after r regs (bs.drop used) ∧ ByteViewSizes h after ∧
      regs.next = inputAdvance l.next used ∧ regs.have_.toNat + used = l.have_.toNat ∧
      regs.put = l.put ∧ regs.left = l.left ∧ regs.bits.toNat ≤ 39 ∧ after.static = h.static ∧
      BlockHeaderFrame s state ∧ HeaderStreamFrame z stream ∧
      (outcome = .error Ex.leave ∨ (outcome = .ok () ∧ dispatchRank regs state.mode < dispatchRank l s.mode)) := by
  by_cases flush : c.flush = Z_BLOCK ∨ c.flush = Z_TREES
  · exact ⟨.error Ex.leave, l, h, z, s, 0, by omega, inflate_TYPE_leave c l h flush, good,
      dataTableInvariant_inactive (by rw [mode]; unfold DataTableMode; decide), pending,
      by simpa only [List.drop_zero] using buffers, ByteViewSizes.refl h,
      (inputAdvance_zero l.next).symm, by rfl, rfl, rfl, incoming, rfl, by rfl, by rfl, Or.inl rfl⟩
  · have go : c.flush ≠ Z_BLOCK ∧ c.flush ≠ Z_TREES :=
      ⟨fun equal => flush (Or.inl equal), fun equal => flush (Or.inr equal)⟩
    rw [inflate_TYPE_go c l h go]
    exact inflate_TYPEDO_rank E good pending buffers globals (Or.inl mode) incoming

theorem inflate_dispatch_type_rank {c : Ctx} {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (good : LocalGood h cutoff r zs z s) (pending : DataPendingInvariant s)
    (buffers : DispatchBuffers h r l bs) (globals : LibraryGlobals h)
    (mode : s.mode = TYPE ∨ s.mode = TYPEDO) (incoming : l.bits.toNat ≤ 39) :
    ∃ outcome regs after stream state used, used ≤ bs.length ∧
      runX (inflate_dispatch c) l h = .ok ((outcome, regs), after) ∧
      LocalGood after cutoff r zs stream state ∧ DataTableInvariant after state ∧ DataPendingInvariant state ∧
      DispatchBuffers after r regs (bs.drop used) ∧ ByteViewSizes h after ∧
      regs.next = inputAdvance l.next used ∧ regs.have_.toNat + used = l.have_.toNat ∧
      regs.put = l.put ∧ regs.left = l.left ∧ regs.bits.toNat ≤ 39 ∧ after.static = h.static ∧
      BlockHeaderFrame s state ∧ HeaderStreamFrame z stream ∧
      (outcome = .error Ex.leave ∨ (outcome = .ok () ∧ dispatchRank regs state.mode < dispatchRank l s.mode)) := by
  rw [inflate_dispatch_block_type E l mode]
  rcases mode with type | typedo
  · rw [if_pos type]
    exact inflate_TYPE_rank E good pending buffers globals type incoming
  · have notType : s.mode ≠ TYPE := by rw [typedo]; decide
    rw [if_neg notType]
    exact inflate_TYPEDO_rank E good pending buffers globals (Or.inr typedo) incoming

theorem inflate_HEAD_zlib_window_rank {c : Ctx} {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (good : LocalGood h cutoff r zs z s) (pending : DataPendingInvariant s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = HEAD) (wrap : s.wrap = 1 ∨ s.wrap = 5)
    (header : s.head = none) (wbits : s.wbits = 15) (incoming : l.bits.toNat ≤ 39) :
    ∃ outcome regs after stream state used, used ≤ bs.length ∧
      runX (inflate_HEAD c) l h = .ok ((outcome, regs), after) ∧
      LocalGood after cutoff r zs stream state ∧ DataTableInvariant after state ∧ DataPendingInvariant state ∧
      DispatchBuffers after r regs (bs.drop used) ∧ ByteViewSizes h after ∧
      regs.next = inputAdvance l.next used ∧ regs.have_.toNat + used = l.have_.toNat ∧
      regs.put = l.put ∧ regs.left = l.left ∧ regs.bits.toNat ≤ 39 ∧ after.static = h.static ∧
      HeaderStateFrame s state ∧ HeaderStreamFrame z stream ∧
      (outcome = .error Ex.leave ∨ (outcome = .ok () ∧ dispatchRank regs state.mode < dispatchRank l s.mode)) := by
  obtain ⟨outcome, regs, after, stream, state, used, bound, run, current, tables, nextPending,
    packet, sizes, next, count, put, left, bits, static, kinds, stateFrame, streamFrame, budget⟩ :=
    inflate_HEAD_zlib_window_boundary_budget E good pending buffers mode wrap header wbits
  refine ⟨outcome, regs, after, stream, state, used, bound, run, current, tables, nextPending,
    packet, sizes, next, count, put, left, by omega, static, stateFrame, streamFrame, ?_⟩
  rcases kinds with ⟨wait, _⟩ | ⟨normal, nextMode⟩
  · exact Or.inl wait
  · have credit : dispatchCredit state.mode < dispatchCredit s.mode := by
      rw [mode]
      rcases nextMode with nextMode | nextMode | nextMode <;> rw [nextMode] <;> decide
    have outputCount : regs.left.toNat + 0 = l.left.toNat := by rw [left]; rfl
    exact Or.inr ⟨normal, dispatchRank_advance count outputCount budget (Or.inr credit)⟩

theorem inflate_STORED_rank {c : Ctx} {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (good : LocalGood h cutoff r zs z s) (pending : DataPendingInvariant s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = STORED) (incoming : l.bits.toNat ≤ 39) :
    ∃ (outcome : Except Ex Unit) (regs : IL) (after : Heap) (stream : ZStream)
      (state : InflateState) (used made : Nat), used ≤ bs.length ∧
      runX (inflate_STORED c) l h = .ok ((outcome, regs), after) ∧
      LocalGood after cutoff r zs stream state ∧ DataTableInvariant after state ∧ DataPendingInvariant state ∧
      DispatchBuffers after r regs (bs.drop used) ∧ ByteViewSizes h after ∧ DecodeStateFrame s state ∧
      regs.next = inputAdvance l.next used ∧ regs.have_.toNat + used = l.have_.toNat ∧
      regs.put = inputAdvance l.put made ∧ regs.left.toNat + made = l.left.toNat ∧
      regs.bits.toNat ≤ 39 ∧ (outcome = .error Ex.leave ∨ (outcome = .ok () ∧ dispatchRank regs state.mode < dispatchRank l s.mode)) ∧ after.static = h.static ∧ Shape h after := by
  obtain ⟨outcome, regs, after, stream, state, used, made, bound, run, current, tables,
    nextPending, packet, sizes, frame, next, count, put, left, bits, kinds, static, shape, budget, modes⟩ :=
    inflate_STORED_boundary_budget_modes E good pending buffers mode incoming
  refine ⟨outcome, regs, after, stream, state, used, made, bound, run, current, tables,
    nextPending, packet, sizes, frame, next, count, put, left, bits, ?_, static, shape⟩
  rcases kinds with normal | wait
  · have credit : dispatchCredit state.mode < dispatchCredit s.mode := by
      rw [mode]
      rcases modes normal with nextMode | nextMode | nextMode <;> rw [nextMode] <;> decide
    exact Or.inr ⟨normal, dispatchRank_advance count left budget (Or.inr credit)⟩
  · exact Or.inl wait

theorem inflate_COPY_rank {c : Ctx} {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (good : LocalGood h cutoff r zs z s) (pending : DataPendingInvariant s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = COPY) (incoming : l.bits.toNat ≤ 39) :
    ∃ (outcome : Except Ex Unit) (regs : IL) (after : Heap) (stream : ZStream)
      (state : InflateState) (used made : Nat), used ≤ bs.length ∧
      runX (inflate_COPY c) l h = .ok ((outcome, regs), after) ∧
      LocalGood after cutoff r zs stream state ∧ DataTableInvariant after state ∧ DataPendingInvariant state ∧
      DispatchBuffers after r regs (bs.drop used) ∧ ByteViewSizes h after ∧ DecodeStateFrame s state ∧
      regs.next = inputAdvance l.next used ∧ regs.have_.toNat + used = l.have_.toNat ∧
      regs.put = inputAdvance l.put made ∧ regs.left.toNat + made = l.left.toNat ∧
      regs.bits.toNat ≤ 39 ∧ (outcome = .error Ex.leave ∨ (outcome = .ok () ∧ dispatchRank regs state.mode < dispatchRank l s.mode)) ∧ after.static = h.static ∧ Shape h after := by
  obtain ⟨outcome, regs, after, state, made, bound, run, current, tables, nextPending,
    packet, sizes, frame, next, count, put, left, bits, _, kinds, static, shape⟩ :=
    inflate_COPY_boundary_frame E good pending buffers mode
  have budget : regs.bits.toNat ≤ l.bits.toNat + 8 * made := by rw [bits]; omega
  refine ⟨outcome, regs, after, z, state, made, made, bound, run, current, tables, nextPending,
    packet, sizes, frame, next, count, put, left, by rw [bits]; exact incoming, ?_, static, shape⟩
  rcases kinds with wait | done | copied
  · exact Or.inl wait.1
  · have credit : dispatchCredit state.mode < dispatchCredit s.mode := by
      rw [done.2.2, mode]
      decide
    exact Or.inr ⟨done.1, dispatchRank_advance count left budget (Or.inr credit)⟩
  · exact Or.inr ⟨copied.1, dispatchRank_advance count left budget (Or.inl copied.2.1)⟩

theorem inflate_COPY_start_rank {c : Ctx} {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (good : LocalGood h cutoff r zs z s) (pending : DataPendingInvariant s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = COPY_) (incoming : l.bits.toNat ≤ 39) :
    ∃ (outcome : Except Ex Unit) (regs : IL) (after : Heap) (stream : ZStream)
      (state : InflateState) (used made : Nat), used ≤ bs.length ∧
      runX (inflate_COPY_ c) l h = .ok ((outcome, regs), after) ∧
      LocalGood after cutoff r zs stream state ∧ DataTableInvariant after state ∧ DataPendingInvariant state ∧
      DispatchBuffers after r regs (bs.drop used) ∧ ByteViewSizes h after ∧ DecodeStateFrame s state ∧
      regs.next = inputAdvance l.next used ∧ regs.have_.toNat + used = l.have_.toNat ∧
      regs.put = inputAdvance l.put made ∧ regs.left.toNat + made = l.left.toNat ∧
      regs.bits.toNat ≤ 39 ∧ (outcome = .error Ex.leave ∨ (outcome = .ok () ∧ dispatchRank regs state.mode < dispatchRank l s.mode)) ∧ after.static = h.static ∧ Shape h after := by
  obtain ⟨outcome, regs, after, state, made, bound, run, current, tables, nextPending,
    packet, sizes, frame, next, count, put, left, bits, _, kinds, static, shape⟩ :=
    inflate_COPY_start_boundary_frame E good pending buffers mode
  have budget : regs.bits.toNat ≤ l.bits.toNat + 8 * made := by rw [bits]; omega
  refine ⟨outcome, regs, after, z, state, made, made, bound, run, current, tables, nextPending,
    packet, sizes, frame, next, count, put, left, by rw [bits]; exact incoming, ?_, static, shape⟩
  rcases kinds with wait | done | copied
  · exact Or.inl wait.1
  · have credit : dispatchCredit state.mode < dispatchCredit s.mode := by
      rw [done.2.2, mode]
      decide
    exact Or.inr ⟨done.1, dispatchRank_advance count left budget (Or.inr credit)⟩
  · exact Or.inr ⟨copied.1, dispatchRank_advance count left budget (Or.inl copied.2.1)⟩

theorem inflate_dispatch_stored_rank {c : Ctx} {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (good : LocalGood h cutoff r zs z s) (pending : DataPendingInvariant s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = STORED ∨ s.mode = COPY_ ∨ s.mode = COPY) (incoming : l.bits.toNat ≤ 39) :
    ∃ (outcome : Except Ex Unit) (regs : IL) (after : Heap) (stream : ZStream)
      (state : InflateState) (used made : Nat), used ≤ bs.length ∧
      runX (inflate_dispatch c) l h = .ok ((outcome, regs), after) ∧
      LocalGood after cutoff r zs stream state ∧ DataTableInvariant after state ∧ DataPendingInvariant state ∧
      DispatchBuffers after r regs (bs.drop used) ∧ ByteViewSizes h after ∧ DecodeStateFrame s state ∧
      regs.next = inputAdvance l.next used ∧ regs.have_.toNat + used = l.have_.toNat ∧
      regs.put = inputAdvance l.put made ∧ regs.left.toNat + made = l.left.toNat ∧
      regs.bits.toNat ≤ 39 ∧ (outcome = .error Ex.leave ∨ (outcome = .ok () ∧ dispatchRank regs state.mode < dispatchRank l s.mode)) ∧ after.static = h.static ∧ Shape h after := by
  rcases mode with stored | start | copy
  · rw [inflate_dispatch_STORED E l stored]
    exact inflate_STORED_rank E good pending buffers stored incoming
  · rw [inflate_dispatch_COPY_start E l start]
    exact inflate_COPY_start_rank E good pending buffers start incoming
  · rw [inflate_dispatch_COPY E l copy]
    exact inflate_COPY_rank E good pending buffers copy incoming

#print axioms inflate_TYPEDO_rank
#print axioms inflate_TYPE_rank
#print axioms inflate_dispatch_type_rank
#print axioms inflate_HEAD_zlib_window_rank
#print axioms inflate_STORED_rank
#print axioms inflate_COPY_rank
#print axioms inflate_COPY_start_rank
#print axioms inflate_dispatch_stored_rank
end Zlib.Inflate.Local
