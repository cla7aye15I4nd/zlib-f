import ZlibF.Proof.«inflate.c.default-view-construction-rank»
import ZlibF.Proof.«inflate.c.dispatch-default-state»
import ZlibF.Proof.«inflate.c.head-gzip-state»
import ZlibF.Proof.«inflate.c.memory-meta-frame-run»
import ZlibF.Proof.«inflate.c.mode-floor»
import ZlibF.Proof.«inflate.c.construction-mode-observer»
import ZlibF.Proof.«inflate.c.check-default-accounting»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Every actual default decoder mode retains its initialized state and
full caller buffer packet. Every normal iteration strictly decreases the
bounded outer rank. All public separated caller byte views are admitted. -/
theorem inflate_dispatch_default_view_state_rank {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (local_ : HeaderLocal c h r s l) (incoming : l.bits.toNat ≤ 39) :
    ∃ outcome regs after stream state used made, used ≤ bs.length ∧
      runX (inflate_dispatch c) l h = .ok ((outcome, regs), after) ∧
      DefaultStateJ after r zs stream state ∧
      (∃ rest, rest.length = bs.length - used ∧ DispatchBuffers after r regs rest) ∧
      ByteViewSizes h after ∧ regs.next = inputAdvance l.next used ∧
      regs.have_.toNat + used = l.have_.toNat ∧ regs.put = inputAdvance l.put made ∧
      regs.left.toNat + made = l.left.toNat ∧ regs.bits.toNat ≤ 39 ∧
      HeaderLocal c after r state regs ∧
      (outcome = .ok () → dispatchRank regs state.mode < dispatchRank l s.mode) := by
  have exact {after : Heap} {regs : IL} {used : Nat} (packet : DispatchBuffers after r regs (bs.drop used)) :
      ∃ rest, rest.length = bs.length - used ∧ DispatchBuffers after r regs rest :=
    ⟨bs.drop used, List.length_drop .., packet⟩
  have above (state : InflateState) (after : Heap) (regs : IL) (floor : DICTID ≤ state.mode) :
      HeaderLocal c after r state regs := by
    intro _ high
    rw [UInt32.le_iff_toNat_le] at floor high
    change 16189 ≤ state.mode.toNat at floor
    change state.mode.toNat ≤ 16188 at high
    omega
  have floorOfDict {mode : UInt32} (above : DICT < mode) : DICTID ≤ mode := by
    rw [UInt32.lt_iff_toNat_lt] at above
    rw [UInt32.le_iff_toNat_le]
    change 16190 < mode.toNat at above
    change 16189 ≤ mode.toNat
    omega
  have headerLow {mode : UInt32} (low : FLAGS ≤ mode) : HEAD ≤ mode := by
    rw [UInt32.le_iff_toNat_le] at low ⊢
    change 16181 ≤ mode.toNat at low
    change 16180 ≤ mode.toNat
    omega
  rcases defaultMode_cases invariant.modes with head | dictionary | type | stored | construction | data | trailer | terminal | gzipHeader
  · by_cases gzip : GzipAllowed s.wrap
    · obtain ⟨outcome, regs, after, stream, state, used, bound, run, final, packet, sizes,
        next, count, put, left, _, bits, _, _, _, _, _, _, _, _, _, carry, progress⟩ :=
        inflate_dispatch_HEAD_gzip_state_rank E invariant buffers head gzip
          (local_ (by rw [head]; decide) (by rw [head]; decide)) incoming
      exact ⟨outcome, regs, after, stream, state, used, 0, bound, run, final, packet, sizes,
        next, count, by rw [put, inputAdvance_zero], by rw [left]; omega, bits, carry,
        dispatch_normal_rank progress⟩
    · obtain ⟨outcome, regs, after, stream, state, used, bound, run, final, packet, sizes,
        next, count, put, left, bits, _, stateFrame, _, progress⟩ :=
        inflate_dispatch_HEAD_state_rank E invariant buffers head gzip incoming
      have none : s.head = none := Classical.byContradiction fun attached =>
        gzip (invariant.header (Or.inl attached))
      have readonly : ∀ ref : BRef, Space.ro after ref = Space.ro h ref := by
        have metaFrame := memoryMetaFrameX_inflate_dispatch r c E.strm l h outcome regs after run
        have roEq : after.ro = h.ro := congrArg Prod.fst metaFrame
        intro ref
        cases ref <;> simp [Space.ro, roEq]
      refine ⟨outcome, regs, after, stream, state, used, 0, bound, run, final, exact packet, sizes,
        next, count, by rw [put, inputAdvance_zero], by rw [left]; omega, bits, ?_, dispatch_normal_rank progress⟩
      intro _ low high
      have headEq : state.head = s.head := by rw [stateFrame]
      exact GzipDispatchLocal.of_none ((local_ (by rw [head]; decide) (by rw [head]; decide)).hbuf.transfer
        sizes readonly) (headEq.trans none)
  · obtain ⟨outcome, regs, after, stream, state, used, bound, run, final, packet, sizes,
      next, count, put, left, bits, _, progress⟩ :=
      inflate_dispatch_dictionary_state_rank E invariant buffers dictionary incoming
    refine ⟨outcome, regs, after, stream, state, used, 0, bound, run, final, exact packet, sizes,
      next, count, by rw [put, inputAdvance_zero], by rw [left]; omega, bits,
      above state after regs
        (inflate_dispatch_dictionary_mode_floor E invariant buffers dictionary incoming run final.good.live.hs), ?_⟩
    intro normal
    rcases progress with needed | leave | completed
    · cases needed.symm.trans normal
    · cases leave.symm.trans normal
    · exact completed.2
  · obtain ⟨outcome, regs, after, stream, state, used, bound, run, final, control, packet, sizes,
      next, count, put, left, bits, _, _, _, progress⟩ :=
      inflate_dispatch_type_state_rank E invariant buffers type incoming
    exact ⟨outcome, regs, after, stream, state, used, 0, bound, run, final, exact packet, sizes,
      next, count, by rw [put, inputAdvance_zero], by rw [left]; omega, bits, above state after regs (blockControlMode_floor control), dispatch_normal_rank progress⟩
  · obtain ⟨outcome, regs, after, stream, state, used, made, bound, run, final, exitMode, packet, sizes,
      _, next, count, put, left, bits, progress, _, _⟩ :=
      inflate_dispatch_stored_state_rank E invariant buffers stored incoming
    exact ⟨outcome, regs, after, stream, state, used, made, bound, run, final, exact packet, sizes,
      next, count, put, left, bits, above state after regs (by rcases exitMode with m | m | m | m | m <;> rw [m] <;> decide), dispatch_normal_rank progress⟩
  · obtain ⟨outcome, regs, after, stream, state, used, made, bound, run, final, packet, sizes,
      next, count, put, left, bits, progress⟩ :=
      inflate_dispatch_construction_view_state_rank E invariant buffers construction incoming
    exact ⟨outcome, regs, after, stream, state, used, made, bound, run, final, exact packet, sizes,
      next, count, put, left, bits, above state after regs (floorOfDict (ConstructionMode.dispatch_above_dict E invariant buffers construction run
        final.good.live.hs)), dispatch_normal_rank progress⟩
  · obtain ⟨outcome, regs, after, stream, state, used, made, bound, run, final, exitMode, packet, sizes,
      next, count, put, left, bits, progress⟩ :=
      inflate_dispatch_data_view_state_rank E invariant buffers data
    exact ⟨outcome, regs, after, stream, state, used, made, bound, run, final, exact packet, sizes,
      next, count, put, left, by omega, above state after regs (floorOfDict (ConstructionMode.data_exit_above_dict exitMode)), dispatch_normal_rank progress⟩
  · rcases trailer with check | length
    · obtain ⟨outcome, regs, after, stream, state, used, bound, run, final, packet, sizes,
        next, count, put, left, bits, _, progress, _, _, _, _, _, observed⟩ :=
        inflate_CHECK_default_state_accounting_rank E invariant buffers check incoming
      obtain ⟨_, checkModes, _, _⟩ := observed
      exact ⟨outcome, regs, after, stream, state, used, 0, bound,
        (inflate_dispatch_CHECK E l check).trans run, final, exact packet, sizes,
        next, count, by rw [put, inputAdvance_zero], by rw [left]; omega, bits, above state after regs (by rcases checkModes with m | m | m | m <;> rw [m] <;> decide), dispatch_normal_rank progress⟩
    · obtain ⟨outcome, regs, after, stream, state, used, bound, run, final, packet, sizes,
        next, count, put, left, bits, _, progress, ⟨_, _, _, _, _, lengthModes, _⟩⟩ :=
        inflate_LENGTH_state_rank E invariant buffers length incoming
      exact ⟨outcome, regs, after, stream, state, used, 0, bound,
        (inflate_dispatch_LENGTH E l length).trans run, final, exact packet, sizes,
        next, count, by rw [put, inputAdvance_zero], by rw [left]; omega, bits, above state after regs (by rcases lengthModes with m | m | m <;> rw [m] <;> decide), dispatch_normal_rank progress⟩
  · obtain ⟨run, _, packet, bits, _⟩ := inflate_dispatch_terminal_state E invariant buffers terminal
    have fields : (terminalRegs s.mode l).next = l.next ∧ (terminalRegs s.mode l).have_ = l.have_ ∧
        (terminalRegs s.mode l).put = l.put ∧ (terminalRegs s.mode l).left = l.left := by
      unfold terminalRegs
      split
      · exact ⟨rfl, rfl, rfl, rfl⟩
      · split <;> exact ⟨rfl, rfl, rfl, rfl⟩
    refine ⟨terminalExit s.mode, terminalRegs s.mode l, h, z, s, 0, 0, by omega, run, invariant,
      ⟨bs, by simp, packet⟩, ByteViewSizes.refl h,
      by rw [fields.1, inputAdvance_zero], by rw [fields.2.1]; omega,
      by rw [fields.2.2.1, inputAdvance_zero], by rw [fields.2.2.2]; omega, by rw [bits]; exact incoming,
      above s h (terminalRegs s.mode l)
        (by rcases terminal with m | m | m | m <;> rw [m] <;> decide), ?_⟩
    intro normal
    rcases terminal with selected | selected | selected | selected <;>
      rw [selected] at normal <;> simp [terminalExit, DONE, BAD, MEM, SYNC] at normal
  · obtain ⟨outcome, regs, after, stream, state, used, bound, run, final, packet, sizes, next, count, put, left,
      _, bits, _, _, _, _, _, _, carry, progress⟩ :=
      inflate_dispatch_gzip_header_state_rank E invariant buffers gzipHeader
        (local_ (headerLow gzipHeader.1) gzipHeader.2.1) incoming
    exact ⟨outcome, regs, after, stream, state, used, 0, bound, run, final, packet, sizes, next, count,
      by rw [put, inputAdvance_zero], by rw [left]; omega, bits, carry, dispatch_normal_rank progress⟩

#print axioms inflate_dispatch_default_view_state_rank
end Zlib.Inflate.Proofs
