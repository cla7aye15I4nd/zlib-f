import ZlibF.Proof.«inflate.c.origin-fields-construction»
import ZlibF.Proof.«inflate.c.default-view-dispatch-rank»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Upgrade the matching real J result by observing every actual default
source mode. The old safety result is composed here, not assumed as an
additional public caller contract. -/
theorem inflate_dispatch_default_origin_state {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z stream : ZStream} {s state : InflateState} {l regs : IL} {bs : List UInt8} {outcome : Except Ex Unit}
    (E : Env c h r zs z s) (before : DefaultOriginState h r zs z s)
    (buffers : DispatchBuffers h r l bs)
    (actual : runX (inflate_dispatch c) l h = .ok ((outcome, regs), after))
    (current : DefaultStateJ after r zs stream state) : DefaultOriginState after r zs stream state := by
  rcases defaultMode_cases before.modes with head | dictionary | blockType | stored | construction | data | trailer | terminal | gzipHeader
  · obtain ⟨observed, get, flags, lengths, distances, wrap⟩ :=
      inflate_dispatch_HEAD_origin_record E before.toDefaultStateJ buffers head actual
    have same : observed = state := Option.some.inj (get.symm.trans current.good.live.hs)
    subst observed
    exact before.of_header_fields current flags lengths distances wrap
  · obtain ⟨observed, get, flags, pointers⟩ :=
      inflate_dispatch_dictionary_origin_record E before.toDefaultStateJ buffers dictionary actual
    have same : observed = state := Option.some.inj (get.symm.trans current.good.live.hs)
    subst observed
    exact before.of_pointer_alternatives current flags pointers
  · obtain ⟨observed, get, flags, pointers⟩ :=
      inflate_dispatch_type_origin_record E buffers blockType actual
    have same : observed = state := Option.some.inj (get.symm.trans current.good.live.hs)
    subst observed
    exact before.of_pointer_alternatives current flags pointers
  · exact before.of_field_frame current (inflate_dispatch_stored_origin_fields E stored actual)
  · obtain ⟨flags, pointers⟩ :=
      inflate_dispatch_construction_origin_fields E before buffers construction actual current.good.live.hs
    have wrap : state.wrap = s.wrap := by
      obtain ⟨regs2, after2, stream2, state2, used2, bound2, J2, config, packet2, sizes2, next2, count2,
        put2, left2, out2, bits2, mass2, ending⟩ :=
        inflate_dispatch_construction_state_boundary E before.toDefaultStateJ buffers construction
      rcases ending with ⟨outcome2, run2, _⟩ | ⟨_, cut⟩
      · have same := Except.ok.inj (run2.symm.trans actual)
        cases same
        have equal : state2 = state := Option.some.inj (J2.good.live.hs.symm.trans current.good.live.hs)
        rw [← equal]
        exact config.2.2.1
      · rw [cut] at actual
        split at actual
        · cases actual
          have equal : state2 = state := Option.some.inj (J2.good.live.hs.symm.trans current.good.live.hs)
          rw [← equal]
          exact config.2.2.1
        · have frame := originFieldFrameX_inflate_LEN_ r c E.strm _ _ _ _ _ actual
          exact (frame.state_wrap J2.good.live.hs current.good.live.hs).trans config.2.2.1
    exact ⟨current, before.flagsOrigin.same flags wrap, pointers⟩
  · exact before.of_field_frame current (inflate_dispatch_data_origin_fields E data actual)
  · exact before.of_field_frame current (inflate_dispatch_trailer_origin_fields E trailer actual)
  · exact before.of_field_frame current (inflate_dispatch_terminal_origin_fields E terminal actual)
  · sorry

/-- Every real default dispatch returns without a fault, preserves the
stronger history state and the exact caller packet, and decreases the
existing bounded rank on normal continuation. -/
theorem inflate_dispatch_default_origin_state_rank {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (before : DefaultOriginState h r zs z s)
    (buffers : DispatchBuffers h r l bs) (local_ : HeaderLocal c h r s l) (incoming : l.bits.toNat ≤ 39) :
    ∃ outcome regs after stream state used made, used ≤ bs.length ∧
      runX (inflate_dispatch c) l h = .ok ((outcome, regs), after) ∧
      DefaultOriginState after r zs stream state ∧
      (∃ rest, rest.length = bs.length - used ∧ DispatchBuffers after r regs rest) ∧
      HeaderLocal c after r state regs ∧
      ByteViewSizes h after ∧ regs.next = inputAdvance l.next used ∧
      regs.have_.toNat + used = l.have_.toNat ∧ regs.put = inputAdvance l.put made ∧
      regs.left.toNat + made = l.left.toNat ∧ regs.bits.toNat ≤ 39 ∧
      (outcome = .ok () → dispatchRank regs state.mode < dispatchRank l s.mode) := by
  obtain ⟨outcome, regs, after, stream, state, used, made, bound, actual, current,
    packet, sizes, next, count, put, left, bits, finalLocal, progress⟩ :=
    inflate_dispatch_default_view_state_rank E before.toDefaultStateJ buffers local_ incoming
  exact ⟨outcome, regs, after, stream, state, used, made, bound, actual,
    inflate_dispatch_default_origin_state E before buffers actual current,
    packet, finalLocal, sizes, next, count, put, left, bits, progress⟩

#print axioms inflate_dispatch_default_origin_state_rank
end Zlib.Inflate.Proofs
