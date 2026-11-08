import ZlibF.Proof.«inflate.c.origin-fields-construction-headers»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Compose the actual length-reading loop and constructor tail. No
origin fact is assumed of either callee or of the returned record. -/
theorem inflate_CODELENS_origin_fields {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s state : InflateState} {l regs : IL} {bs : List UInt8} {outcome : Except Ex Unit}
    (E : Env c h r zs z s) (before : DefaultOriginState h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = CODELENS)
    (actual : runX (inflate_CODELENS c) l h = .ok ((outcome, regs), after))
    (get : after.istates zs = some state) : state.flags = s.flags ∧ CopyTableOrigin zs state := by
  obtain ⟨decision, currentRegs, middle, stream, currentState, used, _, read, current,
    config, packet, _, _, _, _, _, _, _, _, modes, complete⟩ :=
    clRead_default_state_complete E before.toDefaultStateJ buffers mode
  have fields := originFieldFrameX_clRead r c E.strm _ _ _ _ _ read
  have origins := before.of_field_frame current fields
  cases decision with
  | error exit =>
    have source : runX (inflate_CODELENS c) l h = .ok ((.error exit, currentRegs), middle) := by
      rw [inflate_CODELENS_eq, runX_bind, read]
    have same : after = middle := congrArg Prod.snd (Except.ok.inj (actual.symm.trans source))
    have equal : state = currentState := by
      rw [same, current.good.live.hs] at get
      exact (Option.some.inj get).symm
    subst state
    exact ⟨config.2.2.2, origins.tableOrigin⟩
  | ok value =>
    cases value
    have cut : runX (inflate_CODELENS c) l h = runX (clTail c) currentRegs middle := by
      rw [inflate_CODELENS_eq, runX_bind, read]
    rw [cut] at actual
    have env : Env c middle r zs stream currentState :=
      ⟨E.strm, E.st, current.good.live.hz, current.good.live.hs⟩
    have done : currentState.mode = CODELENS →
        currentState.«have».toNat = currentState.nlen.toNat + currentState.ndist.toNat := by
      intro selected
      rcases complete rfl with bad | full
      · rw [selected] at bad
        cases bad
      · exact full
    obtain ⟨flags, pointers⟩ := clTail_origin_fields env origins modes.symm done actual get
    exact ⟨flags.trans config.2.2.2, pointers⟩

/-- The real LENLENS prefix either stops with its established origins or
enters the already checked actual CODELENS continuation. -/
theorem inflate_LENLENS_origin_fields {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s state : InflateState} {l regs : IL} {bs : List UInt8} {outcome : Except Ex Unit}
    (E : Env c h r zs z s) (before : DefaultOriginState h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = LENLENS)
    (actual : runX (inflate_LENLENS c) l h = .ok ((outcome, regs), after))
    (get : after.istates zs = some state) : state.flags = s.flags ∧ CopyTableOrigin zs state := by
  obtain ⟨first, middle, stream, currentState, used, _, current, config, _, packet,
    _, _, _, _, _, _, _, _, stopped | continued⟩ := inflate_LENLENS_origin_entry E before buffers mode
  · obtain ⟨exit, source, _⟩ := stopped
    have same : after = middle := congrArg Prod.snd (Except.ok.inj (actual.symm.trans source))
    have equal : state = currentState := by
      rw [same, current.good.live.hs] at get
      exact (Option.some.inj get).symm
    subst state
    exact ⟨config.2.2.2, current.tableOrigin⟩
  · obtain ⟨selected, cut⟩ := continued
    rw [cut] at actual
    have env : Env c middle r zs stream currentState :=
      ⟨E.strm, E.st, current.good.live.hz, current.good.live.hs⟩
    obtain ⟨flags, pointers⟩ := inflate_CODELENS_origin_fields env current packet selected actual get
    exact ⟨flags.trans config.2.2.2, pointers⟩

/-- TABLE's actual waits and count refusals retain the old origins. Its
accepted counts enter the real length-alphabet and constructor sequence. -/
theorem inflate_TABLE_origin_fields {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s state : InflateState} {l regs : IL} {bs : List UInt8} {outcome : Except Ex Unit}
    (E : Env c h r zs z s) (before : DefaultOriginState h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = TABLE)
    (actual : runX (inflate_TABLE c) l h = .ok ((outcome, regs), after))
    (get : after.istates zs = some state) : state.flags = s.flags ∧ CopyTableOrigin zs state := by
  obtain ⟨first, middle, stream, currentState, used, _, current, config, _, packet,
    _, _, _, _, _, _, _, _, stopped | continued⟩ := inflate_TABLE_origin_entry E before buffers mode
  · obtain ⟨exit, source, _⟩ := stopped
    have same : after = middle := congrArg Prod.snd (Except.ok.inj (actual.symm.trans source))
    have equal : state = currentState := by
      rw [same, current.good.live.hs] at get
      exact (Option.some.inj get).symm
    subst state
    exact ⟨config.2.2.2, current.tableOrigin⟩
  · obtain ⟨selected, cut⟩ := continued
    rw [cut] at actual
    have env : Env c middle r zs stream currentState :=
      ⟨E.strm, E.st, current.good.live.hz, current.good.live.hs⟩
    obtain ⟨flags, pointers⟩ := inflate_LENLENS_origin_fields env current packet selected actual get
    exact ⟨flags.trans config.2.2.2, pointers⟩

/-- Every actual dynamic construction mode preserves both internal
history facts, including waits, malformed alphabets and real data decoding. -/
theorem inflate_dispatch_construction_origin_fields {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s state : InflateState} {l regs : IL} {bs : List UInt8} {outcome : Except Ex Unit}
    (E : Env c h r zs z s) (before : DefaultOriginState h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = TABLE ∨ s.mode = LENLENS ∨ s.mode = CODELENS)
    (actual : runX (inflate_dispatch c) l h = .ok ((outcome, regs), after))
    (get : after.istates zs = some state) : state.flags = s.flags ∧ CopyTableOrigin zs state := by
  rcases mode with table | lengths | codes
  · rw [inflate_dispatch_TABLE E l table] at actual
    exact inflate_TABLE_origin_fields E before buffers table actual get
  · rw [inflate_dispatch_LENLENS E l lengths] at actual
    exact inflate_LENLENS_origin_fields E before buffers lengths actual get
  · rw [inflate_dispatch_CODELENS E l codes] at actual
    exact inflate_CODELENS_origin_fields E before buffers codes actual get

#print axioms inflate_dispatch_construction_origin_fields
end Zlib.Inflate.Proofs
