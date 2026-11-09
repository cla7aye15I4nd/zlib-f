import ZlibF.Proof.«inflate.c.local-control-rank»
import ZlibF.Proof.«inflate.c.local-data-invariant»
import ZlibF.Proof.«inflate.c.control-default»

/-! Actual decoder execution with local allocation uniqueness. -/
namespace Zlib.Inflate.Local
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Inffast.Spec ZlibF.Spec.Public
set_option autoImplicit false
set_option maxRecDepth 8192

theorem LocalDecodeJ.block_update {h after : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z stream : ZStream} {s state : InflateState} (invariant : LocalDecodeJ h cutoff r zs z s)
    (current : LocalGood after cutoff r zs stream state) (tables : DataTableInvariant after state)
    (pending : DataPendingInvariant state) (frame : BlockHeaderFrame s state)
    (modes : BlockControlMode state.mode) (format : s.wrap = 0 ∨ s.flags = 0)
    (sizes : ByteViewSizes h after) (static : after.static = h.static) :
    LocalDecodeJ after cutoff r zs stream state := by
  have bounds : state.mode ≠ CODELENS ∧ state.mode ≠ LENLENS ∧ DICTID ≤ state.mode ∧ state.mode ≤ SYNC := by
    rcases modes with selected | selected | selected | selected | selected | selected | selected <;>
      rw [selected] <;> decide
  refine ⟨current, tables, pending, ?_, ?_, ?_, ?_, ?_, ?_, Or.inr ⟨bounds.2.2.1, bounds.2.2.2⟩,
    ?_, ?_, sizes.platform invariant.platform⟩
  · intro active
    exact False.elim (bounds.1 active)
  · intro active
    exact False.elim (bounds.2.1 active)
  · rw [frame]
    exact invariant.held
  · rw [frame]
    exact invariant.window
  · rw [frame]
    exact invariant.wrapper
  · rw [frame]
    exact invariant.header
  · intro _
    rw [frame]
    exact format
  · change after.static = _
    rw [static]
    exact invariant.globals

theorem typedoTail_default_J {c : Ctx} {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : LocalDecodeJ h cutoff r zs z s)
    (buffers : DispatchBuffers h r l bs) (full : 2 ≤ l.bits.toNat)
    (format : s.wrap = 0 ∨ s.flags = 0) :
    ∃ outcome after stream state,
      let regs := { l with hold := l.hold >>> (2 : UInt32).toUInt64, bits := l.bits - 2 }
      runX (typedoTail c) l h = .ok ((outcome, regs), after) ∧
      LocalDecodeJ after cutoff r zs stream state ∧ BlockControlMode state.mode := by
  obtain ⟨outcome, after, stream, state, run, current, tables, pending, _, sizes, static, frame, _, kinds⟩ :=
    typedoTail_boundary E invariant.good invariant.pending buffers invariant.globals full
  have modes : BlockControlMode state.mode := by
    rcases kinds with ⟨_, stored | table | lengthMode | bad⟩ | ⟨_, lengthMode, _⟩
    · exact Or.inr (Or.inr (Or.inl stored))
    · exact Or.inr (Or.inr (Or.inr (Or.inl table)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl lengthMode))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr bad)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl lengthMode))))
  exact ⟨outcome, after, stream, state, run,
    invariant.block_update current tables pending frame modes format sizes static, modes⟩

theorem inflate_TYPEDO_default_J {c : Ctx} {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : LocalDecodeJ h cutoff r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = TYPE ∨ s.mode = TYPEDO)
    (format : s.wrap = 0 ∨ s.flags = 0) :
    ∃ outcome regs after stream state,
      runX (inflate_TYPEDO c) l h = .ok ((outcome, regs), after) ∧
      LocalDecodeJ after cutoff r zs stream state ∧ BlockControlMode state.mode := by
  have beforeMode : BlockControlMode s.mode := mode.elim Or.inl (fun selected => Or.inr (Or.inl selected))
  by_cases last : s.last = 0
  · obtain ⟨outcome, current, used, pull, usedBound, bitInv, _, _, shape,
      _, _, full, _, kinds, cursor⟩ := NEEDBITS_run_cursor buffers.bits 3 (by decide)
    have symbolShape : SymbolRegShape l current := by rw [shape]; rfl
    have packet := dispatch_consume_local buffers invariant.good invariant.good rfl (fun _ => rfl) (fun _ => rfl)
      symbolShape cursor usedBound bitInv
    rcases kinds with normal | wait
    · rw [normal] at pull
      have enough : 3 ≤ current.bits.toNat := full normal
      let middle := { s with last := u2i (current.hold.toUInt32 &&& ((1 : UInt32) <<< 1 - 1)) }
      let first := { current with hold := current.hold >>> (1 : UInt32).toUInt64, bits := current.bits - 1 }
      let heap1 := setI h zs middle
      obtain ⟨firstBits, _, firstCount⟩ := DROPBITS_inv bitInv 1 (by change 1 ≤ current.bits.toNat; omega) (by decide)
      change (current.bits - 1).toNat = current.bits.toNat - 1 at firstCount
      obtain ⟨good1, packet1, sizes1⟩ := block_header_packet invariant.good packet
        (state := middle) (regs := first) (by rfl) (Or.inl ⟨rfl, rfl⟩) invariant.good.live.mode firstBits (by rfl)
      have pending1 : DataPendingInvariant middle := by
        apply dataPendingInvariant_idle (s := middle) invariant.pending.sane
        rcases mode with selected | selected <;>
          change s.mode ≠ LENEXT ∧ s.mode ≠ DIST ∧ s.mode ≠ DISTEXT ∧ s.mode ≠ MATCH <;> rw [selected] <;> decide
      have inactive : ¬ DataTableMode middle.mode := by
        rcases mode with selected | selected <;> change ¬ DataTableMode s.mode <;> rw [selected] <;> unfold DataTableMode <;> decide
      have currentJ := invariant.block_update good1 (dataTableInvariant_inactive inactive) pending1
        (by rfl) beforeMode format sizes1 rfl
      have E1 : Env c heap1 r zs z middle := ⟨E.strm, E.st, good1.live.hz, good1.live.hs⟩
      have enough1 : 2 ≤ first.bits.toNat := by change 2 ≤ (current.bits - 1).toNat; rw [firstCount]; omega
      obtain ⟨exit, after, stream, state, run, final, modes⟩ :=
        typedoTail_default_J E1 currentJ packet1 enough1 format
      exact ⟨exit, _, after, stream, state, (inflate_TYPEDO_head E l current last pull).trans run, final, modes⟩
    · have run := inflate_TYPEDO_wait E l current last Ex.leave (by rwa [wait] at pull)
      exact ⟨.error Ex.leave, current, h, z, s, run, invariant, beforeMode⟩
  · obtain ⟨run, current, tables, pending, _, sizes, _, static, frame⟩ :=
      inflate_TYPEDO_last_boundary E invariant.good invariant.pending buffers last
    have modes : BlockControlMode ({ s with mode := CHECK } : InflateState).mode :=
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    exact ⟨.ok (), bytebits l, _, z, _, run,
      invariant.block_update current tables pending frame modes format sizes static, modes⟩

theorem inflate_TYPE_default_J {c : Ctx} {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : LocalDecodeJ h cutoff r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = TYPE)
    (format : s.wrap = 0 ∨ s.flags = 0) :
    ∃ outcome regs after stream state,
      runX (inflate_TYPE c) l h = .ok ((outcome, regs), after) ∧
      LocalDecodeJ after cutoff r zs stream state ∧ BlockControlMode state.mode := by
  by_cases flush : c.flush = Z_BLOCK ∨ c.flush = Z_TREES
  · exact ⟨.error Ex.leave, l, h, z, s, inflate_TYPE_leave c l h flush, invariant, Or.inl mode⟩
  · rw [inflate_TYPE_go c l h ⟨fun equal => flush (Or.inl equal), fun equal => flush (Or.inr equal)⟩]
    exact inflate_TYPEDO_default_J E invariant buffers (Or.inl mode) format

theorem inflate_dispatch_type_J {c : Ctx} {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : LocalDecodeJ h cutoff r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = TYPE ∨ s.mode = TYPEDO)
    (format : s.wrap = 0 ∨ s.flags = 0) :
    ∃ outcome regs after stream state,
      runX (inflate_dispatch c) l h = .ok ((outcome, regs), after) ∧
      LocalDecodeJ after cutoff r zs stream state ∧ BlockControlMode state.mode := by
  rw [inflate_dispatch_block_type E l mode]
  rcases mode with selected | selected
  · rw [if_pos selected]
    exact inflate_TYPE_default_J E invariant buffers selected format
  · rw [if_neg (by rw [selected]; decide : s.mode ≠ TYPE)]
    exact inflate_TYPEDO_default_J E invariant buffers (Or.inr selected) format

theorem inflate_dispatch_type_J_rank {c : Ctx} {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : LocalDecodeJ h cutoff r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = TYPE ∨ s.mode = TYPEDO)
    (format : s.wrap = 0 ∨ s.flags = 0) (incoming : l.bits.toNat ≤ 39) :
    ∃ outcome regs after stream state used, used ≤ bs.length ∧
      runX (inflate_dispatch c) l h = .ok ((outcome, regs), after) ∧
      LocalDecodeJ after cutoff r zs stream state ∧ BlockControlMode state.mode ∧
      DispatchBuffers after r regs (bs.drop used) ∧ ByteViewSizes h after ∧
      regs.next = inputAdvance l.next used ∧ regs.have_.toNat + used = l.have_.toNat ∧
      regs.put = l.put ∧ regs.left = l.left ∧ regs.bits.toNat ≤ 39 ∧ after.static = h.static ∧
      BlockHeaderFrame s state ∧ HeaderStreamFrame z stream ∧
      (outcome = .error Ex.leave ∨ (outcome = .ok () ∧ dispatchRank regs state.mode < dispatchRank l s.mode)) := by
  obtain ⟨outcome, regs, after, stream, state, run, current, modes⟩ :=
    inflate_dispatch_type_J E invariant buffers mode format
  obtain ⟨otherOutcome, otherRegs, otherHeap, otherStream, otherState, used, bound, otherRun,
    good, _, _, packet, sizes, next, count, put, left, bits, static, frame, streamFrame, progress⟩ :=
    inflate_dispatch_type_rank E invariant.good invariant.pending buffers invariant.globals mode incoming
  rw [run] at otherRun
  cases otherRun
  have streamEq : otherStream = stream := Option.some.inj (good.live.hz.symm.trans current.good.live.hz)
  have stateEq : otherState = state := Option.some.inj (good.live.hs.symm.trans current.good.live.hs)
  subst otherStream otherState
  exact ⟨outcome, regs, after, stream, state, used, bound, run, current, modes,
    packet, sizes, next, count, put, left, bits, static, frame, streamFrame, progress⟩

#print axioms LocalDecodeJ.block_update
#print axioms typedoTail_default_J
#print axioms inflate_TYPEDO_default_J
#print axioms inflate_TYPE_default_J
#print axioms inflate_dispatch_type_J
#print axioms inflate_dispatch_type_J_rank
end Zlib.Inflate.Local
