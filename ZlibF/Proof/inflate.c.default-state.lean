import ZlibF.Proof.«inflate.c.default-foundation»
import ZlibF.Proof.«inflate.c.control-default»
import ZlibF.Proof.«inflate.c.default-history»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- At a block-header boundary the history fields discharge the actual
CHECK continuation's wrapper/flag premise. -/
theorem DefaultStateJ.block_format {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (invariant : DefaultStateJ h r zs z s)
    (mode : s.mode = TYPE ∨ s.mode = TYPEDO) : s.wrap = 0 ∨ s.flags = 0 := by
  rcases invariant.phase with head | bad | mem | sync | format
  · rcases mode with selected | selected <;> rw [selected] at head <;> contradiction
  · rcases mode with selected | selected <;> rw [selected] at bad <;> contradiction
  · rcases mode with selected | selected <;> rw [selected] at mem <;> contradiction
  · rcases mode with selected | selected <;> rw [selected] at sync <;> contradiction
  · exact format

/-- Caller buffer replacement preserves the exact default history fields. -/
theorem rebuffer_default_state {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (invariant : DefaultStateJ h r zs z s)
    (edit : Rebuffer h after r) (platform : ZlibF.PlatformMemory.ByteObjectsFit after) :
    ∃ stream, DefaultStateJ after r zs stream s := by
  obtain ⟨stream, current⟩ := rebuffer_default_J invariant.toDefaultDecodeJ edit platform
  exact ⟨stream, ⟨current, invariant.requestedBits, invariant.requestedWrap, invariant.phase⟩⟩

/-- A validation toggle retains the requested default configuration. -/
theorem validateState_default_requested {s : InflateState} (requested : s.reqwrap = 1 ∨ s.reqwrap = 5)
    (check : Int32) : (validateState check s).reqwrap = 1 ∨ (validateState check s).reqwrap = 5 := by
  rcases requested with requested | requested <;> by_cases zero : check = 0
  all_goals simp [validateState, requested, zero]
  all_goals decide

/-- The actual validation call preserves the reset and completed-header
fields as well as every decoder invariant clause. -/
theorem inflateValidate_default_state {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (invariant : DefaultStateJ h r zs z s) (check : Int32) :
    ∃ after state, C.run (inflateValidate (some r) check) h = .ok (Z_OK, after) ∧
      after = setI h zs state ∧ state = validateState check s ∧ DefaultStateJ after r zs z state := by
  obtain ⟨after, state, run, heapEq, stateEq, current⟩ :=
    inflateValidate_default_J invariant.toDefaultDecodeJ check
  have requestedBits : state.reqbits = 15 := by rw [stateEq]; exact invariant.requestedBits
  have requestedWrap : state.reqwrap = 1 ∨ state.reqwrap = 5 := by
    rw [stateEq]; exact validateState_default_requested invariant.requestedWrap check
  have phase : state.mode = HEAD ∨ state.mode = BAD ∨ state.mode = MEM ∨ state.mode = SYNC ∨ state.wrap = 0 ∨ state.flags = 0 := by
    rw [stateEq]
    rcases invariant.phase with head | bad | mem | sync | raw | flags
    · exact Or.inl head
    · exact Or.inr (Or.inl bad)
    · exact Or.inr (Or.inr (Or.inl mem))
    · exact Or.inr (Or.inr (Or.inr (Or.inl sync)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (validateState_raw_wrap raw check)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr flags))))
  exact ⟨after, state, run, heapEq, stateEq, ⟨current, requestedBits, requestedWrap, phase⟩⟩

/-- The actual block switch preserves the complete default state relation,
with its format premise derived from the incoming relation rather than
required independently of reachable history. -/
theorem inflate_dispatch_type_state_rank {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = TYPE ∨ s.mode = TYPEDO)
    (incoming : l.bits.toNat ≤ 39) :
    ∃ outcome regs after stream state used, used ≤ bs.length ∧
      runX (inflate_dispatch c) l h = .ok ((outcome, regs), after) ∧
      DefaultStateJ after r zs stream state ∧ BlockControlMode state.mode ∧
      DispatchBuffers after r regs (bs.drop used) ∧ ByteViewSizes h after ∧
      regs.next = inputAdvance l.next used ∧ regs.have_.toNat + used = l.have_.toNat ∧
      regs.put = l.put ∧ regs.left = l.left ∧ regs.bits.toNat ≤ 39 ∧ after.static = h.static ∧
      BlockHeaderFrame s state ∧ HeaderStreamFrame z stream ∧
      (outcome = .error Ex.leave ∨ (outcome = .ok () ∧ dispatchRank regs state.mode < dispatchRank l s.mode)) := by
  have format := invariant.block_format mode
  obtain ⟨outcome, regs, after, stream, state, used, bound, run, current, modes,
    packet, sizes, next, count, put, left, bits, static, frame, streamFrame, progress⟩ :=
    inflate_dispatch_type_J_rank E invariant.toDefaultDecodeJ buffers mode format incoming
  have finalFormat : state.wrap = 0 ∨ state.flags = 0 := by rw [frame]; exact format
  have final : DefaultStateJ after r zs stream state := ⟨current,
    by rw [frame]; exact invariant.requestedBits,
    by rw [frame]; exact invariant.requestedWrap,
    Or.inr (Or.inr (Or.inr (Or.inr finalFormat)))⟩
  exact ⟨outcome, regs, after, stream, state, used, bound, run, final, modes,
    packet, sizes, next, count, put, left, bits, static, frame, streamFrame, progress⟩

/-- An active data mode has already entered raw recovery or completed its
zlib header; this follows from the incoming history relation. -/
theorem DefaultStateJ.data_format {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (invariant : DefaultStateJ h r zs z s)
    (mode : DataTableMode s.mode) : s.wrap = 0 ∨ s.flags = 0 := by
  rcases invariant.phase with head | bad | mem | sync | format
  · rcases mode with selected | selected | selected | selected | selected | selected | selected <;>
      rw [selected] at head <;> contradiction
  · rcases mode with selected | selected | selected | selected | selected | selected | selected <;>
      rw [selected] at bad <;> contradiction
  · rcases mode with selected | selected | selected | selected | selected | selected | selected <;>
      rw [selected] at mem <;> contradiction
  · rcases mode with selected | selected | selected | selected | selected | selected | selected <;>
      rw [selected] at sync <;> contradiction
  · exact format

/-- All actual data modes simultaneously preserve decoder safety, the
reset/header history fields, exact caller buffer counts and the bounded
strict dispatch rank. The internal raw fast interface remains explicit. -/
theorem inflate_dispatch_data_state_rank {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : DataTableMode s.mode)
    (raw : (s.mode = LEN_ ∨ s.mode = LEN) ∧ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true → RawFastIO l) :
    ∃ outcome regs after stream state used made,
      used ≤ bs.length ∧ runX (inflate_dispatch c) l h = .ok ((outcome, regs), after) ∧
      DefaultStateJ after r zs stream state ∧ DataExitMode state.mode ∧
      DispatchBuffers after r regs (bs.drop used) ∧ ByteViewSizes h after ∧
      regs.next = inputAdvance l.next used ∧ regs.have_.toNat + used = l.have_.toNat ∧
      regs.put = inputAdvance l.put made ∧ regs.left.toNat + made = l.left.toNat ∧
      regs.bits.toNat ≤ max l.bits.toNat 22 ∧
      (outcome = .error Ex.leave ∨ (outcome = .ok () ∧ dispatchRank regs state.mode < dispatchRank l s.mode)) := by
  obtain ⟨outcome, regs, after, stream, state, used, made, bound, run, current, modes,
    packet, sizes, next, count, put, left, bits, progress⟩ :=
    inflate_dispatch_data_J_rank E invariant.toDefaultDecodeJ buffers mode raw
  obtain ⟨otherOutcome, otherRegs, otherHeap, otherStream, otherState, otherRun, good, config⟩ :=
    inflate_dispatch_data_configuration E invariant.toDefaultDecodeJ buffers mode raw
  rw [run] at otherRun
  cases otherRun
  have streamEq : otherStream = stream := Option.some.inj (good.live.hz.symm.trans current.good.live.hz)
  have stateEq : otherState = state := Option.some.inj (good.live.hs.symm.trans current.good.live.hs)
  subst otherStream otherState
  obtain ⟨requestedBits, requestedWrap, wrap, flags⟩ := config
  have finalFormat : state.wrap = 0 ∨ state.flags = 0 := by rw [wrap, flags]; exact invariant.data_format mode
  have final : DefaultStateJ after r zs stream state := ⟨current,
    requestedBits.trans invariant.requestedBits,
    by rw [requestedWrap]; exact invariant.requestedWrap,
    Or.inr (Or.inr (Or.inr (Or.inr finalFormat)))⟩
  exact ⟨outcome, regs, after, stream, state, used, made, bound, run, final, modes,
    packet, sizes, next, count, put, left, bits, progress⟩

end Zlib.Inflate.Proofs
