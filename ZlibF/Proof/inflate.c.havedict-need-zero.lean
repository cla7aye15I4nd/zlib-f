import ZlibF.Proof.«inflate.c.normal-mode-base»
import ZlibF.Proof.«inflate.c.return-mode-run»

namespace Zlib.Inflate.Proofs.HaveDict
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false


/-- The actual missing-dictionary return retains the active DICT mode. -/
theorem inflate_DICT_need_zero
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s returned : InflateState} {l regs : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = DICT) (incoming : l.bits.toNat ≤ 39)
    (run : runX (inflate_DICT c) l h = .ok ((.error (.ret Z_NEED_DICT), regs), after))
    (get : after.istates zs = some returned) : returned.havedict = 0 := by
  by_cases missing : s.havedict = 0
  · have source := inflate_DICT_wait_run E l missing
    have same := xrun_state_eq (firstState := leaveState s l) source run
      (by simp only [setI_istates_same]) get
    rw [← same]
    exact missing
  · let ready := { s with check := 1, mode := TYPE }
    let stream := { z with adler := 1 }
    let heap := setI (r.put h stream) zs ready
    have current : DefaultStateJ heap r zs stream ready :=
      invariant.prepare_dictionary (Or.inr mode) 1 TYPE (Or.inr rfl)
    have env : Env c heap r zs stream ready :=
      ⟨E.strm, E.st, current.good.live.hz, current.good.live.hs⟩
    have views : ∀ ref : BRef, (Space.get heap ref : Option (Array UInt8)) = Space.get h ref := by
      intro ref
      rw [byte_view_get_setI, byte_view_get_stream_put]
    have ro : ∀ ref : BRef, Space.ro heap ref = Space.ro h ref := by
      intro ref
      rw [byte_view_ro_setI, byte_view_ro_stream_put]
    have packet := buffers.byte_views invariant.good current.good rfl views ro
    have selector : runX (inflate_dispatch c) l heap = runX (inflate_TYPE c) l heap := by
      rw [inflate_dispatch_block_type env l (Or.inl rfl), ite_eq_left rfl]
    have actual : runX (inflate_dispatch c) l heap = .ok ((.error (.ret Z_NEED_DICT), regs), after) :=
      selector.trans ((inflate_DICT_ready_cut E l missing).symm.trans run)
    obtain ⟨outcome, finalRegs, finalHeap, finalStream, state, used, _, source, final,
      modes, _, _, _, _, _, _, _, _, _, _, progress⟩ :=
      inflate_dispatch_type_state_rank env current packet (Or.inl rfl) incoming
    have observed := xrun_outcome_eq source actual
    rcases progress with leaves | normal
    · cases leaves.symm.trans observed
    · cases normal.1.symm.trans observed


theorem inflate_DICTID_need_zero
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s returned : InflateState} {l regs : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = DICTID)
    (run : runX (inflate_DICTID c) l h = .ok ((.error (.ret Z_NEED_DICT), regs), after))
    (get : after.istates zs = some returned) : returned.havedict = 0 := by
  obtain ⟨outcome, currentRegs, used, pull, usedBound, bitInv, _, _, shape,
    _, _, _, _, kinds, cursor⟩ := NEEDBITS_run_cursor buffers.bits 32 (by decide)
  rcases kinds with normal | wait
  · rw [normal] at pull
    let value := ZSWAP32 currentRegs.hold
    let ready := { s with check := value, mode := DICT }
    let stream := { z with adler := value }
    let heap := setI (r.put h stream) zs ready
    let first := { currentRegs with hold := 0, bits := 0 }
    have current : DefaultStateJ heap r zs stream ready :=
      invariant.prepare_dictionary (Or.inl mode) value DICT (Or.inl rfl)
    have env : Env c heap r zs stream ready :=
      ⟨E.strm, E.st, current.good.live.hz, current.good.live.hs⟩
    have packet : DispatchBuffers h r currentRegs (bs.drop used) :=
      buffers.consume invariant.good invariant.good rfl (fun _ => rfl) (fun _ => rfl)
        (by rw [shape]; rfl) cursor usedBound bitInv
    have views : ∀ ref : BRef, (Space.get heap ref : Option (Array UInt8)) = Space.get h ref := by
      intro ref
      rw [byte_view_get_setI, byte_view_get_stream_put]
    have ro : ∀ ref : BRef, Space.ro heap ref = Space.ro h ref := by
      intro ref
      rw [byte_view_ro_setI, byte_view_ro_stream_put]
    have packet0 : DispatchBuffers heap r first (bs.drop used) :=
      (packet.byte_views invariant.good current.good rfl views ro).clear_bits
    have actual : runX (inflate_DICT c) first heap = .ok ((.error (.ret Z_NEED_DICT), regs), after) :=
      (inflate_DICTID_parsed_cut E l currentRegs pull).symm.trans run
    exact inflate_DICT_need_zero env current packet0 rfl (by change 0 ≤ 39; decide) actual get
  · have source := inflate_DICTID_wait (c := c) (by rwa [wait] at pull)
    have impossible := xrun_outcome_eq source run
    cases impossible

#print axioms inflate_DICTID_need_zero
private theorem ordinary_progress_not_needed
    {outcome : Except Ex Unit} {progress : Prop}
    (ordinary : outcome = .error Ex.leave ∨ (outcome = .ok () ∧ progress))
    (direct : outcome = .error (.ret Z_NEED_DICT)) : False := by
  rcases ordinary with leave | normal
  · cases leave.symm.trans direct
  · cases normal.1.symm.trans direct

/-- In the real default switch only DICTID/DICT can return NEED_DICT, and
the returned private record is in DICT on that exact execution. -/
theorem inflate_dispatch_need_zero
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s returned : InflateState} {l regs : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (incoming : l.bits.toNat ≤ 39)
    (run : runX (inflate_dispatch c) l h = .ok ((.error (.ret Z_NEED_DICT), regs), after))
    (get : after.istates zs = some returned) : returned.havedict = 0 := by
  rcases defaultMode_cases invariant.modes with head | dictionary | type | stored | construction | data | trailer | terminal
  · obtain ⟨outcome, outRegs, heap, stream, state, used, _, source, _, _, _, _, _, _, _, _, _, _, _, progress⟩ :=
      inflate_dispatch_HEAD_state_rank E invariant buffers head incoming
    exact False.elim (ordinary_progress_not_needed progress (xrun_outcome_eq source run))
  · rcases dictionary with id | dictionary
    · exact inflate_DICTID_need_zero E invariant buffers id
        ((inflate_dispatch_DICTID E l id).symm.trans run) get
    · exact inflate_DICT_need_zero E invariant buffers dictionary incoming
        ((inflate_dispatch_DICT E l dictionary).symm.trans run) get
  · obtain ⟨outcome, outRegs, heap, stream, state, used, _, source, _, _, _, _, _, _, _, _, _, _, _, _, progress⟩ :=
      inflate_dispatch_type_state_rank E invariant buffers type incoming
    exact False.elim (ordinary_progress_not_needed progress (xrun_outcome_eq source run))
  · obtain ⟨outcome, outRegs, heap, stream, state, used, made, _, source, _, _, _, _, _, _, _, _, _, _, progress, _, _⟩ :=
      inflate_dispatch_stored_state_rank E invariant buffers stored incoming
    exact False.elim (ordinary_progress_not_needed progress (xrun_outcome_eq source run))
  · obtain ⟨outcome, outRegs, heap, stream, state, used, made, _, source, _, _, _, _, _, _, _, _, progress⟩ :=
      inflate_dispatch_construction_view_state_rank E invariant buffers construction incoming
    exact False.elim (ordinary_progress_not_needed progress (xrun_outcome_eq source run))
  · obtain ⟨outcome, outRegs, heap, stream, state, used, made, _, source, _, _, _, _, _, _, _, _, _, progress⟩ :=
      inflate_dispatch_data_view_state_rank E invariant buffers data
    exact False.elim (ordinary_progress_not_needed progress (xrun_outcome_eq source run))
  · rcases trailer with check | length
    · obtain ⟨outcome, outRegs, heap, stream, state, used, _, source, _, _, _, _, _, _, _, _, _, progress⟩ :=
        inflate_CHECK_default_state_rank E invariant buffers check incoming
      have actual := (inflate_dispatch_CHECK E l check).symm.trans run
      exact False.elim (ordinary_progress_not_needed progress (xrun_outcome_eq source actual))
    · obtain ⟨source, _⟩ := inflate_LENGTH_default_state_boundary E invariant buffers length
      have actual := (inflate_dispatch_LENGTH E l length).trans source
      have impossible := xrun_outcome_eq actual run
      cases impossible
  · have source := inflate_dispatch_terminal_run E l terminal
    have impossible := xrun_outcome_eq source run
    rcases terminal with selected | selected | selected | selected <;>
      rw [selected] at impossible <;>
      simp [terminalExit, DONE, BAD, MEM, SYNC, Z_MEM_ERROR, Z_STREAM_ERROR, Z_NEED_DICT] at impossible

theorem run_need_zero
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s returned : InflateState} {regs : IL}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : StreamBuffers h r) (nonnull : z.next_out ≠ .null)
    (inputValid : z.next_in = .null → z.avail_in = 0)
    (run : runX (inflate_run c) IL.init h = .ok ((.error (.ret Z_NEED_DICT), regs), after))
    (get : after.istates zs = some returned) : returned.havedict = 0 := by
  obtain ⟨entryHeap, entryState, bs, cut, current, _, packet, bits, _, _, _⟩ :=
    inflate_run_default_view_entry E invariant buffers nonnull inputValid
  have start : RetLoopInv r zs (dispatchRegs z entryState) entryHeap :=
    ⟨z, entryState, bs, current, packet, bits, Or.inl rfl⟩
  let Q := fun (exit : Ex) (_l : IL) (heap : Heap) =>
    ∃ state, heap.istates zs = some state ∧ (exit = .ret Z_NEED_DICT → state.havedict = 0)
  have step : ∀ before heap outcome finalRegs finalHeap, RetLoopInv r zs before heap →
      runX (inflate_dispatch c) before heap = .ok ((outcome, finalRegs), finalHeap) →
      match outcome with
      | .ok () => RetLoopInv r zs finalRegs finalHeap
      | .error exit => Q exit finalRegs finalHeap := by
    intro before heap outcome finalRegs finalHeap valid source
    obtain ⟨stream, state, input, initial, beforePacket, incoming, ret⟩ := valid
    have env : Env c heap r zs stream state := ⟨E.strm, E.st, initial.good.live.hz, initial.good.live.hs⟩
    obtain ⟨otherOutcome, otherRegs, otherHeap, finalStream, finalState, used, _, _, actual,
      final, finalPacket, _, _, _, _, _, finalBits, _⟩ :=
      inflate_dispatch_default_view_state_rank env initial beforePacket incoming
    have same := Except.ok.inj (actual.symm.trans source)
    cases same
    cases outcome with
    | ok unit =>
      cases unit
      have normal := (inflate_dispatch_ret_classification env initial beforePacket ret source final.good.live.hs).1 rfl
      exact ⟨finalStream, finalState, input.drop used, final, finalPacket, finalBits, normal⟩
    | error exit =>
      refine ⟨finalState, final.good.live.hs, ?_⟩
      intro needed
      subst exit
      exact inflate_dispatch_need_zero env initial beforePacket incoming source final.good.live.hs
  rw [cut] at run
  obtain ⟨state, stateGet, zero⟩ := xwhile_success_control_post (RetLoopInv r zs) Q step start run
  have same : state = returned := Option.some.inj (stateGet.symm.trans get)
  simpa only [same] using zero rfl

#print axioms inflate_DICT_need_zero
#print axioms inflate_DICTID_need_zero
#print axioms inflate_dispatch_need_zero
#print axioms run_need_zero
end Zlib.Inflate.Proofs.HaveDict
