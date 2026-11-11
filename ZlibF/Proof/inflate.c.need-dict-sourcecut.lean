import ZlibF.Proof.«inflate.c.check-default-accounting»
import ZlibF.Proof.«inflate.c.construction-mode-observer»
import ZlibF.Proof.«inflate.c.output-base-run»
import ZlibF.Proof.«inflate.c.output-credit-shape»
import ZlibF.Proof.«inflate.c.return-mode-run»

namespace Zlib.Inflate.Proofs.ActiveSourceCut
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The actual CHECK source can wait at CHECK, reject into BAD, or finish
at DONE. It cannot re-enter a mode capable of a later back reference. -/
theorem check_inactive
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s returned : InflateState} {l regs : IL} {bs : List UInt8}
    {outcome : Except Ex Unit}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = CHECK) (incoming : l.bits.toNat ≤ 39)
    (run : runX (inflate_CHECK c) l h = .ok ((outcome, regs), after))
    (get : after.istates zs = some returned) : ¬ returned.mode < CHECK := by
  obtain ⟨_, _, _, _, state2, _, _, source, final, _, _, _, _, _, _, _, _, _, _, _, _, _, _, observed⟩ :=
    inflate_CHECK_default_state_accounting_rank E invariant buffers mode incoming
  obtain ⟨_, modes, _, _⟩ := observed
  have same := xrun_state_eq source run final.good.live.hs get
  rw [← same]
  rcases modes with m | m | m | m <;> rw [m] <;> decide
/-- No actual dispatch can return from trailer/error modes to an active
payload mode. The switch guard and source callee executions establish it. -/
theorem dispatch_active_origin
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s returned : InflateState} {l regs : IL} {bs : List UInt8}
    {outcome : Except Ex Unit}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs)
    (run : runX (inflate_dispatch c) l h = .ok ((outcome, regs), after))
    (get : after.istates zs = some returned) (active : returned.mode < CHECK)
    (incoming : l.bits.toNat ≤ 39) :
    s.mode < CHECK := by
  by_cases beforeActive : s.mode < CHECK
  · exact beforeActive
  · have kinds : s.mode = CHECK ∨ s.mode = LENGTH ∨ TerminalMode s.mode := by
      have upper := invariant.good.live.mode.2
      change s.mode.toNat ≤ 16211 at upper
      change ¬ s.mode.toNat < 16206 at beforeActive
      unfold TerminalMode
      simp only [← UInt32.toNat_inj]
      change s.mode.toNat = 16206 ∨ s.mode.toNat = 16207 ∨
        s.mode.toNat = 16208 ∨ s.mode.toNat = 16209 ∨
        s.mode.toNat = 16210 ∨ s.mode.toNat = 16211
      omega
    rcases kinds with check | length | terminal
    · have actual := (inflate_dispatch_CHECK E l check).symm.trans run
      exact False.elim (check_inactive E invariant buffers check incoming actual get active)
    · obtain ⟨_, _, _, _, state2, _, _, source2, final2, _, _, _, _, _, _, _, _, _, ⟨_, _, _, _, _, modes2, _⟩⟩ :=
        inflate_LENGTH_state_rank E invariant buffers length incoming
      have source := (inflate_dispatch_LENGTH E l length).trans source2
      have same := xrun_state_eq source run final2.good.live.hs get
      rw [← same] at active
      rcases modes2 with m | m | m <;> rw [m] at active <;> exact absurd active (by decide)
    · have source := inflate_dispatch_terminal_run E l terminal
      have same := xrun_state_eq source run E.hs get
      rw [← same] at active
      rcases terminal with mode | mode | mode | mode
      all_goals rw [mode] at active; exact False.elim (by revert active; decide)

#print axioms check_inactive
#print axioms dispatch_active_origin

theorem entry_exact {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : StreamBuffers h r) (nonnull : z.next_out ≠ .null)
    (inputValid : z.next_in = .null → z.avail_in = 0) :
    ∃ after state bs,
      runX (inflate_run c) IL.init h =
        runX (xwhile (pure true) (inflate_dispatch c)) (dispatchRegs z state) after ∧
      DefaultStateJ after r zs z state ∧ Env c after r zs z state ∧
      DispatchBuffers after r (dispatchRegs z state) bs ∧
      (dispatchRegs z state).bits.toNat ≤ 39 ∧ ByteViewSizes h after ∧ DecodeStateFrame s state ∧
      after = setI h zs state ∧
      state = (if s.mode = TYPE then {s with mode := TYPEDO} else s) := by
  let good := invariant.good
  let tables := invariant.tables
  let pending := invariant.pending
  let hold := invariant.held
  obtain ⟨after, state, run, finalGood, env, output, sizes, frame, heapEq, stateEq⟩ :=
    inflate_run_output_entry_frame_state E good buffers nonnull
  have currentBuffers : StreamBuffers after r := by
    obtain ⟨stream, streamGet, input, out, separate⟩ := buffers
    have eq : stream = z := Option.some.inj (streamGet.symm.trans good.live.hz)
    subst stream
    refine ⟨z, finalGood.live.hz, ?_, ?_, separate⟩
    · apply callerRange_transport good finalGood (by rw [frame]) _ _ input
      · intro ref
        rw [heapEq, byte_view_get_setI]
      · intro ref
        rw [heapEq, byte_view_ro_setI]
    · apply callerRange_transport good finalGood (by rw [frame]) _ _ out
      · intro ref
        rw [heapEq, byte_view_get_setI]
      · intro ref
        rw [heapEq, byte_view_ro_setI]
  obtain ⟨bs, inv, separate⟩ := dispatchRegs_input (s := state) finalGood.live.hz currentBuffers inputValid
    (by rw [frame]; exact hold)
  have input : CallerRange after r z.next_in z.avail_in.toNat false := by
    obtain ⟨stream, get, input, _⟩ := currentBuffers
    have eq : stream = z := Option.some.inj (get.symm.trans finalGood.live.hz)
    subst stream
    exact input
  have finalTables : DataTableInvariant after state := by
    by_cases type : s.mode = TYPE
    · intro active
      rw [stateEq, if_pos type] at active
      change DataTableMode TYPEDO at active
      rcases active with eq | eq | eq | eq | eq | eq | eq <;> contradiction
    · have sameState : state = s := by rw [stateEq, if_neg type]
      have sameHeap : after = h := by rw [heapEq, sameState]; simp [setI, upd_self _ _ _ good.live.hs]
      rwa [sameHeap, sameState]
  have finalPending : DataPendingInvariant state := by
    by_cases type : s.mode = TYPE
    · apply dataPendingInvariant_idle (by rw [frame]; exact pending.sane)
      rw [stateEq, if_pos type]
      change TYPEDO ≠ LENEXT ∧ TYPEDO ≠ DIST ∧ TYPEDO ≠ DISTEXT ∧ TYPEDO ≠ MATCH
      decide
    · rw [stateEq, if_neg type]
      exact pending
  have finalJ : DefaultStateJ after r zs z state := by
    by_cases type : s.mode = TYPE
    · have blockFrame : BlockHeaderFrame s state := by rw [stateEq, if_pos type]; rfl
      have modes : BlockControlMode state.mode := by
        rw [stateEq, if_pos type]
        exact Or.inr (Or.inl rfl)
      have format := invariant.block_format (Or.inl type)
      have base := invariant.toDefaultDecodeJ.block_update finalGood finalTables finalPending blockFrame modes format sizes
        (by rw [heapEq]; rfl)
      exact invariant.config_update base frame.default_config format
    · have sameState : state = s := by rw [stateEq, if_neg type]
      have sameHeap : after = h := by rw [heapEq, sameState]; simp [setI, upd_self _ _ _ good.live.hs]
      rwa [sameHeap, sameState]
  exact ⟨after, state, bs, run, finalJ, env, ⟨input, output, separate, inv⟩,
    finalGood.inv.bits, sizes, frame, heapEq, stateEq⟩

#print axioms entry_exact

/-- An actual active return has never crossed CHECK. Its output base is
the original caller capacity, and its incoming state was active too. -/
theorem run_active_base
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s returned : InflateState} {regs : IL} {exit : Ex}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : StreamBuffers h r) (nonnull : z.next_out ≠ .null)
    (inputValid : z.next_in = .null → z.avail_in = 0)
    (local_ : HeaderLocal c h r s (dispatchRegs z s))
    (run : runX (inflate_run c) IL.init h = .ok ((.error exit, regs), after))
    (get : after.istates zs = some returned) (active : returned.mode < CHECK) :
    s.mode < CHECK ∧ regs.out_ = z.avail_out := by
  obtain ⟨entryHeap, entryState, bs, cut, current, _env, packet, bits,
    entrySizes, entryFrame, entryHeapEq, stateEq⟩ := entry_exact E invariant buffers nonnull inputValid
  have entryLocal := inflate_run_entry_local invariant current entrySizes entryFrame entryHeapEq stateEq local_
  let P := fun (l : IL) (heap : Heap) =>
    ∃ stream state input, DefaultStateJ heap r zs stream state ∧ HeaderLocal c heap r state l ∧
      DispatchBuffers heap r l input ∧ l.bits.toNat ≤ 39 ∧
      (state.mode < CHECK → s.mode < CHECK ∧ l.out_ = z.avail_out)
  let Q := fun (_exit : Ex) (l : IL) (heap : Heap) =>
    ∃ state, heap.istates zs = some state ∧
      (state.mode < CHECK → s.mode < CHECK ∧ l.out_ = z.avail_out)
  have initial : P (dispatchRegs z entryState) entryHeap := by
    refine ⟨z, entryState, bs, current, entryLocal, packet, bits, ?_⟩
    intro entryActive
    constructor
    · by_cases type : s.mode = TYPE
      · rw [type]
        decide
      · simpa only [stateEq, if_neg type] using entryActive
    · rfl
  have step : ∀ before heap outcome nextRegs nextHeap, P before heap →
      runX (inflate_dispatch c) before heap = .ok ((outcome, nextRegs), nextHeap) →
      match outcome with
      | .ok () => P nextRegs nextHeap
      | .error stopped => Q stopped nextRegs nextHeap := by
    intro before heap outcome nextRegs nextHeap valid source
    obtain ⟨stream, state, input, currentJ, currentLocal, currentPacket, incoming, prior⟩ := valid
    have env : Env c heap r zs stream state :=
      ⟨E.strm, E.st, currentJ.good.live.hz, currentJ.good.live.hs⟩
    obtain ⟨otherOutcome, otherRegs, otherHeap, finalStream, finalState, used, _made,
      _bound, actual, final, ⟨rest, _, finalPacket⟩, _sizes, _next, _count, _put, _left,
      finalBits, finalLocal, _progress⟩ :=
      inflate_dispatch_default_view_state_rank env currentJ currentPacket currentLocal incoming
    have same := Except.ok.inj (actual.symm.trans source)
    cases same
    have carry : finalState.mode < CHECK → s.mode < CHECK ∧ nextRegs.out_ = z.avail_out := by
      intro nextActive
      have beforeActive := dispatch_active_origin env currentJ currentPacket source final.good.live.hs nextActive incoming
      have notCheck : state.mode ≠ CHECK := by
        intro selected
        rw [selected] at beforeActive
        exact (by decide : ¬ CHECK < CHECK) beforeActive
      have unchanged := inflate_dispatch_output_base_noncheck env notCheck source
      exact ⟨(prior beforeActive).1, unchanged.trans (prior beforeActive).2⟩
    cases outcome with
    | ok unit =>
      cases unit
      exact ⟨finalStream, finalState, rest, final, finalLocal, finalPacket, finalBits, carry⟩
    | error stopped => exact ⟨finalState, final.good.live.hs, carry⟩
  rw [cut] at run
  obtain ⟨state, stateGet, relation⟩ := xwhile_success_control_post P Q step initial run
  have same : state = returned := Option.some.inj (stateGet.symm.trans get)
  exact relation (by simpa only [same] using active)

#print axioms run_active_base

/-- Once a source dispatch has entered block parsing, no subsequent mode
can return to dictionary metadata parsing. -/
theorem dispatch_above_dictionary
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s returned : InflateState} {l regs : IL} {bs : List UInt8}
    {outcome : Except Ex Unit}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (incoming : l.bits.toNat ≤ 39)
    (before : DICT < s.mode)
    (run : runX (inflate_dispatch c) l h = .ok ((outcome, regs), after))
    (get : after.istates zs = some returned) : DICT < returned.mode := by
  rcases defaultMode_cases invariant.modes with head | dictionary | type | stored | construction | data | trailer | terminal | gzipHeader
  · rw [head] at before
    exact False.elim ((by decide : ¬ DICT < HEAD) before)
  · rcases dictionary with mode | mode
    all_goals rw [mode] at before; exact False.elim (by revert before; decide)
  · obtain ⟨_outcome, _regs, _heap, _stream, state, _used, _bound, source, final, modes, _rest⟩ :=
      inflate_dispatch_type_state_rank E invariant buffers type incoming
    have same := xrun_state_eq source run final.good.live.hs get
    rw [← same]
    rcases modes with mode | mode | mode | mode | mode | mode | mode
    all_goals rw [mode]; decide
  · obtain ⟨_outcome, _regs, _heap, _stream, state, _used, _made, _bound, source, final, modes, _rest⟩ :=
      inflate_dispatch_stored_state_rank E invariant buffers stored incoming
    have same := xrun_state_eq source run final.good.live.hs get
    rw [← same]
    rcases modes with mode | mode | mode | mode | mode
    all_goals rw [mode]; decide
  · exact ConstructionMode.dispatch_above_dict E invariant buffers construction run get
  · obtain ⟨_outcome, _regs, _heap, _stream, state, _used, _made, _bound, source, final, modes, _rest⟩ :=
      inflate_dispatch_data_view_state_rank E invariant buffers data
    have same := xrun_state_eq source run final.good.live.hs get
    rw [← same]
    exact ConstructionMode.data_exit_above_dict modes
  · rcases trailer with check | length
    · have inactive := check_inactive E invariant buffers check incoming
        ((inflate_dispatch_CHECK E l check).symm.trans run) get
      change ¬ returned.mode.toNat < 16206 at inactive
      change 16190 < returned.mode.toNat
      omega
    · obtain ⟨_, _, _, _, state2, _, _, source2, final2, _, _, _, _, _, _, _, _, _, ⟨_, _, _, _, _, modes2, _⟩⟩ :=
        inflate_LENGTH_state_rank E invariant buffers length incoming
      have source := (inflate_dispatch_LENGTH E l length).trans source2
      have same := xrun_state_eq source run final2.good.live.hs get
      rw [← same]
      rcases modes2 with m | m | m <;> rw [m] <;> decide
  · have source := inflate_dispatch_terminal_run E l terminal
    have same := xrun_state_eq source run E.hs get
    rw [← same]
    exact before
  · have high := gzipHeader.2.1
    rw [UInt32.le_iff_toNat_le] at high
    rw [UInt32.lt_iff_toNat_lt] at before
    change s.mode.toNat ≤ 16188 at high
    change 16190 < s.mode.toNat at before
    omega

/-- Any actual dispatch returning in header/dictionary modes has not
written an output byte and had not yet entered payload processing. -/
theorem dispatch_dictionary_output_unchanged
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s returned : InflateState} {l regs : IL} {bs : List UInt8}
    {outcome : Except Ex Unit}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (local_ : HeaderLocal c h r s l) (incoming : l.bits.toNat ≤ 39)
    (run : runX (inflate_dispatch c) l h = .ok ((outcome, regs), after))
    (get : after.istates zs = some returned) (low : returned.mode ≤ DICT) :
    s.mode ≤ DICT ∧ regs.put = l.put ∧ regs.left = l.left := by
  have before : s.mode ≤ DICT := by
    by_cases high : DICT < s.mode
    · have next := dispatch_above_dictionary E invariant buffers incoming high run get
      change 16190 < returned.mode.toNat at next
      change returned.mode.toNat ≤ 16190 at low
      omega
    · change ¬ 16190 < s.mode.toNat at high
      change s.mode.toNat ≤ 16190
      omega
  have kinds : s.mode = HEAD ∨ (s.mode = DICTID ∨ s.mode = DICT) ∨ GzipHeaderMode s := by
    rcases invariant.modes with head | interval | header
    · exact Or.inl head
    · right; left
      have lower := interval.1
      change 16189 ≤ s.mode.toNat at lower
      change s.mode.toNat ≤ 16190 at before
      simp only [← UInt32.toNat_inj]
      change s.mode.toNat = 16189 ∨ s.mode.toNat = 16190
      omega
    · exact Or.inr (Or.inr header)
  rcases kinds with head | dictionary | header
  · by_cases gzip : GzipAllowed s.wrap
    · obtain ⟨_outcome, _regs, _heap, _stream, _state, _used, _bound, source, _final, _packet, _sizes,
        _next, _count, put, left, _⟩ :=
        inflate_dispatch_HEAD_gzip_state_rank E invariant buffers head gzip
          (local_ (by rw [head]; decide) (by rw [head]; decide)) incoming
      have same := Except.ok.inj (source.symm.trans run)
      cases same
      exact ⟨before, put, left⟩
    · obtain ⟨_outcome, _regs, _heap, _stream, _state, _used, _bound, source, _final,
        _packet, _sizes, _next, _inputCount, put, left, _rest⟩ :=
        inflate_dispatch_HEAD_state_rank E invariant buffers head gzip incoming
      have same := Except.ok.inj (source.symm.trans run)
      cases same
      exact ⟨before, put, left⟩
  · obtain ⟨_outcome, _regs, _heap, _stream, _state, _used, _bound, source, _final,
      _packet, _sizes, _next, _inputCount, put, left, _rest⟩ :=
      inflate_dispatch_dictionary_state_rank E invariant buffers dictionary incoming
    have same := Except.ok.inj (source.symm.trans run)
    cases same
    exact ⟨before, put, left⟩
  · have lowMode : HEAD ≤ s.mode := by
      have flagsLow := header.1
      rw [UInt32.le_iff_toNat_le] at flagsLow ⊢
      change 16181 ≤ s.mode.toNat at flagsLow
      change 16180 ≤ s.mode.toNat
      omega
    obtain ⟨_outcome, _regs, _heap, _stream, _state, _used, _bound, source, _final, _packet, _sizes,
      _next, _count, put, left, _⟩ :=
      inflate_dispatch_gzip_header_state_rank E invariant buffers header (local_ lowMode header.2.1) incoming
    have same := Except.ok.inj (source.symm.trans run)
    cases same
    exact ⟨before, put, left⟩

#print axioms dispatch_above_dictionary
#print axioms dispatch_dictionary_output_unchanged

/-- The actual complete loop has produced no output whenever it exits
while still parsing the header or dictionary handshake. -/
theorem run_dictionary_output_unchanged
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s returned : InflateState} {regs : IL} {exit : Ex}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : StreamBuffers h r) (nonnull : z.next_out ≠ .null)
    (inputValid : z.next_in = .null → z.avail_in = 0)
    (local_ : HeaderLocal c h r s (dispatchRegs z s))
    (run : runX (inflate_run c) IL.init h = .ok ((.error exit, regs), after))
    (get : after.istates zs = some returned) (low : returned.mode ≤ DICT) :
    regs.put = z.next_out ∧ regs.left = z.avail_out := by
  obtain ⟨entryHeap, entryState, bs, cut, current, _env, packet, bits,
    entrySizes, entryFrame, entryHeapEq, entryStateEq⟩ := entry_exact E invariant buffers nonnull inputValid
  have entryLocal := inflate_run_entry_local invariant current entrySizes entryFrame entryHeapEq entryStateEq local_
  let P := fun (l : IL) (heap : Heap) =>
    ∃ stream state input, DefaultStateJ heap r zs stream state ∧ HeaderLocal c heap r state l ∧
      DispatchBuffers heap r l input ∧ l.bits.toNat ≤ 39 ∧
      (state.mode ≤ DICT → l.put = z.next_out ∧ l.left = z.avail_out)
  let Q := fun (_exit : Ex) (l : IL) (heap : Heap) =>
    ∃ state, heap.istates zs = some state ∧
      (state.mode ≤ DICT → l.put = z.next_out ∧ l.left = z.avail_out)
  have initial : P (dispatchRegs z entryState) entryHeap :=
    ⟨z, entryState, bs, current, entryLocal, packet, bits, fun _ => ⟨rfl, rfl⟩⟩
  have step : ∀ before heap outcome nextRegs nextHeap, P before heap →
      runX (inflate_dispatch c) before heap = .ok ((outcome, nextRegs), nextHeap) →
      match outcome with
      | .ok () => P nextRegs nextHeap
      | .error stopped => Q stopped nextRegs nextHeap := by
    intro before heap outcome nextRegs nextHeap valid source
    obtain ⟨stream, state, input, currentJ, currentLocal, currentPacket, incoming, prior⟩ := valid
    have env : Env c heap r zs stream state :=
      ⟨E.strm, E.st, currentJ.good.live.hz, currentJ.good.live.hs⟩
    obtain ⟨otherOutcome, otherRegs, otherHeap, finalStream, finalState, used, _made,
      _bound, actual, final, ⟨rest, _, finalPacket⟩, _sizes, _next, _count, _put, _left,
      finalBits, finalLocal, _progress⟩ :=
      inflate_dispatch_default_view_state_rank env currentJ currentPacket currentLocal incoming
    have same := Except.ok.inj (actual.symm.trans source)
    cases same
    have carry : finalState.mode ≤ DICT → nextRegs.put = z.next_out ∧ nextRegs.left = z.avail_out := by
      intro nextLow
      obtain ⟨beforeLow, put, left⟩ := dispatch_dictionary_output_unchanged env currentJ currentPacket
        currentLocal incoming source final.good.live.hs nextLow
      exact ⟨put.trans (prior beforeLow).1, left.trans (prior beforeLow).2⟩
    cases outcome with
    | ok unit =>
      cases unit
      exact ⟨finalStream, finalState, rest, final, finalLocal, finalPacket, finalBits, carry⟩
    | error stopped => exact ⟨finalState, final.good.live.hs, carry⟩
  rw [cut] at run
  obtain ⟨state, stateGet, relation⟩ := xwhile_success_control_post P Q step initial run
  have same : state = returned := Option.some.inj (stateGet.symm.trans get)
  exact relation (by simpa only [same] using low)

/-- A true NEED_DICT direct return restores the original output binding
and capacity. Its actual emitted output length is therefore zero. -/
theorem run_need_dict_produces_zero
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {regs : IL}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : StreamBuffers h r) (nonnull : z.next_out ≠ .null)
    (inputValid : z.next_in = .null → z.avail_in = 0)
    (local_ : HeaderLocal c h r s (dispatchRegs z s))
    (run : runX (inflate_run c) IL.init h = .ok ((.error (.ret Z_NEED_DICT), regs), after)) :
    regs.put = z.next_out ∧ regs.left = z.avail_out := by
  obtain ⟨state, get, needMode, _rest⟩ := inflate_run_return_modes E invariant buffers nonnull inputValid local_ run
  have mode := needMode rfl
  exact run_dictionary_output_unchanged E invariant buffers nonnull inputValid local_ run get
    (by rw [mode]; exact UInt32.le_refl _)

#print axioms run_dictionary_output_unchanged
#print axioms run_need_dict_produces_zero
end Zlib.Inflate.Proofs.ActiveSourceCut
