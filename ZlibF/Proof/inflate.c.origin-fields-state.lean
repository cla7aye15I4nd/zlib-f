import ZlibF.Proof.«inflate.c.origin-fields-data-modes»
import ZlibF.Proof.«inflate.c.fast-view-dispatch-state»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Recover concrete state-field equality from the successful-run observer
and the actual decoder records on the two heaps. -/
theorem OriginFieldFrame.state_fields {h after : Heap} {r : ZStreamRef} {owner : InflateStatePtr}
    {zs : Nat} {s state : InflateState} (frame : OriginFieldFrame r owner h after)
    (beforeGet : h.istates zs = some s) (afterGet : after.istates zs = some state) :
    state.flags = s.flags ∧ state.lencode = s.lencode ∧ state.distcode = s.distcode := by
  have observed := congrFun frame zs
  change (after.istates zs).map originStateFields = (h.istates zs).map originStateFields at observed
  rw [beforeGet, afterGet] at observed
  have fields : originStateFields state = originStateFields s := Option.some.inj observed
  exact ⟨congrArg Prod.fst fields, congrArg (fun value => value.2.1) fields,
    congrArg (fun value => value.2.2.1) fields⟩

/-- The same observer keeps the wrapper. -/
theorem OriginFieldFrame.state_wrap {h after : Heap} {r : ZStreamRef} {owner : InflateStatePtr}
    {zs : Nat} {s state : InflateState} (frame : OriginFieldFrame r owner h after)
    (beforeGet : h.istates zs = some s) (afterGet : after.istates zs = some state) :
    state.wrap = s.wrap := by
  have observed := congrFun frame zs
  change (after.istates zs).map originStateFields = (h.istates zs).map originStateFields at observed
  rw [beforeGet, afterGet] at observed
  have fields : originStateFields state = originStateFields s := Option.some.inj observed
  exact congrArg (fun value => value.2.2.2) fields

/-- A real source frame transports both origin clauses to an already
checked state on the same actual returned heap. -/
theorem DefaultOriginState.of_field_frame {h after : Heap} {r : ZStreamRef} {owner : InflateStatePtr}
    {zs : Nat} {z stream : ZStream} {s state : InflateState}
    (before : DefaultOriginState h r zs z s) (current : DefaultStateJ after r zs stream state)
    (frame : OriginFieldFrame r owner h after) : DefaultOriginState after r zs stream state := by
  obtain ⟨flags, lengths, distances⟩ := frame.state_fields before.good.live.hs current.good.live.hs
  exact before.of_fields current flags lengths distances (frame.state_wrap before.good.live.hs current.good.live.hs)

/-- Actual slow and fast data dispatch retain all three source fields.
Fast-path buffer restrictions are not assumed: this observes the same
translated execution already produced by the general-view safety proof. -/
theorem inflate_dispatch_data_origin_fields {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l regs : IL} {outcome : Except Ex Unit}
    (E : Env c h r zs z s) (mode : DataTableMode s.mode)
    (actual : runX (inflate_dispatch c) l h = .ok ((outcome, regs), after)) :
    OriginFieldFrame r c.st h after := by
  rcases mode with selected | selected | selected | selected | selected | selected | selected
  · rw [inflate_dispatch_LEN_start E l selected] at actual
    exact originFieldFrameX_inflate_LEN_ r c E.strm l h outcome regs after actual
  · rw [inflate_dispatch_LEN E l selected] at actual
    exact originFieldFrameX_inflate_LEN r c E.strm l h outcome regs after actual
  · rw [inflate_dispatch_LENEXT E l selected] at actual
    exact originFieldFrameX_inflate_LENEXT r c E.strm l h outcome regs after actual
  · rw [inflate_dispatch_DIST E l selected] at actual
    exact originFieldFrameX_inflate_DIST r c E.strm l h outcome regs after actual
  · rw [inflate_dispatch_DISTEXT E l selected] at actual
    exact originFieldFrameX_inflate_DISTEXT r c E.strm l h outcome regs after actual
  · rw [inflate_dispatch_MATCH E l selected] at actual
    exact originFieldFrameX_inflate_MATCH r c E.strm l h outcome regs after actual
  · rw [inflate_dispatch_LIT E l selected] at actual
    exact originFieldFrameX_inflate_LIT r c E.strm l h outcome regs after actual

/-- Stored-block header and copy paths retain flags and installed pointers. -/
theorem inflate_dispatch_stored_origin_fields {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l regs : IL} {outcome : Except Ex Unit}
    (E : Env c h r zs z s) (mode : s.mode = STORED ∨ s.mode = COPY_ ∨ s.mode = COPY)
    (actual : runX (inflate_dispatch c) l h = .ok ((outcome, regs), after)) :
    OriginFieldFrame r c.st h after := by
  rcases mode with selected | selected | selected
  · rw [inflate_dispatch_STORED E l selected] at actual
    exact originFieldFrameX_inflate_STORED r c E.strm l h outcome regs after actual
  · rw [inflate_dispatch_COPY_start E l selected] at actual
    exact originFieldFrameX_inflate_COPY_ r c E.strm l h outcome regs after actual
  · rw [inflate_dispatch_COPY E l selected] at actual
    exact originFieldFrameX_inflate_COPY r c E.strm l h outcome regs after actual

/-- Both checksum-trailer branches retain the default source origins. -/
theorem inflate_dispatch_trailer_origin_fields {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l regs : IL} {outcome : Except Ex Unit}
    (E : Env c h r zs z s) (mode : s.mode = CHECK ∨ s.mode = LENGTH)
    (actual : runX (inflate_dispatch c) l h = .ok ((outcome, regs), after)) :
    OriginFieldFrame r c.st h after := by
  rcases mode with selected | selected
  · rw [inflate_dispatch_CHECK E l selected] at actual
    exact originFieldFrameX_inflate_CHECK r c E.strm l h outcome regs after actual
  · rw [inflate_dispatch_LENGTH E l selected] at actual
    exact originFieldFrameX_inflate_LENGTH r c E.strm l h outcome regs after actual

/-- Terminal/error modes return on the original heap. -/
theorem inflate_dispatch_terminal_origin_fields {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l regs : IL} {outcome : Except Ex Unit}
    (E : Env c h r zs z s) (mode : TerminalMode s.mode)
    (actual : runX (inflate_dispatch c) l h = .ok ((outcome, regs), after)) :
    OriginFieldFrame r c.st h after := by
  have same : h = after := congrArg Prod.snd
    (Except.ok.inj ((inflate_dispatch_terminal_run E l mode).symm.trans actual))
  rw [← same]
  exact OriginFieldFrame.refl r c.st h

/-- Actual data decoding establishes the stronger state without a new
caller invariant or callee specification assumption. -/
theorem inflate_dispatch_data_origin_state_run {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (before : DefaultOriginState h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : DataTableMode s.mode) :
    ∃ outcome regs after stream state,
      runX (inflate_dispatch c) l h = .ok ((outcome, regs), after) ∧
      DefaultOriginState after r zs stream state := by
  obtain ⟨outcome, regs, after, stream, state, actual, current⟩ :=
    inflate_dispatch_data_view_state_run E before.toDefaultStateJ buffers mode
  exact ⟨outcome, regs, after, stream, state, actual,
    before.of_field_frame current (inflate_dispatch_data_origin_fields E mode actual)⟩

#print axioms inflate_dispatch_data_origin_state_run
#print axioms inflate_dispatch_stored_origin_fields
#print axioms inflate_dispatch_trailer_origin_fields
#print axioms inflate_dispatch_terminal_origin_fields
end Zlib.Inflate.Proofs
