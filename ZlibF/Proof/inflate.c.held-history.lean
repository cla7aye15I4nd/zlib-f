import ZlibF.Proof.«inflate.c.held-bound»
import ZlibF.Proof.«inflate.c.gzip-dispatch-observe»
import ZlibF.Proof.«inflate.c.normal-mode-base»
import ZlibF.Proof.«inflate.c.loop-control-post»
import ZlibF.Proof.«inflate.c.leave-cause-run»

/-!
# inflate.c: the held-bit bound across the decoder loop

The loop of one call keeps `HeldBits` for its registers. A leave exits with
at most 32 held bits outside `BAD`, `MEM` and `SYNC`; a direct return
(`Z_NEED_DICT` from `DICT`, after restoring the registers, or a `MEM`/`SYNC`
error) leaves a decoder state with `HeldBits`.
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

private theorem ordinary_not_ret {outcome : Except Ex Unit} {v : Int32} {progress : Prop}
    (ordinary : outcome = .error Ex.leave ∨ (outcome = .ok () ∧ progress))
    (direct : outcome = .error (.ret v)) : False := by
  rcases ordinary with leave | normal
  · cases leave.symm.trans direct
  · cases normal.1.symm.trans direct

/-- A direct return from `DICT` restores the registers into the state. -/
theorem inflate_DICT_ret_bits {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = DICT) (incoming : l.bits.toNat ≤ 39)
    {v : Int32} {regs : IL} {after : Heap} {state : InflateState}
    (run : runX (inflate_DICT c) l h = .ok ((.error (.ret v), regs), after))
    (get : after.istates zs = some state) :
    state.bits = l.bits := by
  by_cases missing : s.havedict = 0
  · obtain ⟨run2, good2, _⟩ :=
      inflate_DICT_wait_boundary E invariant.good invariant.pending buffers mode missing incoming
    obtain ⟨_, _, heapEq⟩ := runX_same run run2
    subst heapEq
    have same := Option.some.inj (get.symm.trans good2.live.hs)
    rw [same]
    rfl
  · exfalso
    let ready := { s with check := 1, mode := TYPE }
    let stream0 := { z with adler := 1 }
    let heap0 := setI (r.put h stream0) zs ready
    have good0 : Good heap0 r zs stream0 ready :=
      invariant.good.setZI rfl invariant.good.live.zalloc invariant.good.live.zfree rfl
        (by change HEAD ≤ TYPE ∧ TYPE ≤ SYNC; decide)
        (invariant.good.inv.of_fields rfl rfl rfl rfl rfl rfl rfl rfl rfl invariant.good.inv.bits rfl rfl rfl)
    have views : ∀ ref : BRef, (Space.get heap0 ref : Option (Array UInt8)) = Space.get h ref := by
      intro ref
      rw [byte_view_get_setI, byte_view_get_stream_put]
    have readonly : ∀ ref : BRef, Space.ro heap0 ref = Space.ro h ref := by
      intro ref
      rw [byte_view_ro_setI, byte_view_ro_stream_put]
    have sizes0 : ByteViewSizes h heap0 := by intro ref; rw [views]
    have static0 : heap0.static = h.static := by simp only [heap0, setI, ZStreamRef.put_static]
    have E0 : Env c heap0 r zs stream0 ready := ⟨E.strm, E.st, good0.live.hz, good0.live.hs⟩
    have pending0 : DataPendingInvariant ready := by
      apply dataPendingInvariant_idle (s := ready) invariant.pending.sane
      change TYPE ≠ LENEXT ∧ TYPE ≠ DIST ∧ TYPE ≠ DISTEXT ∧ TYPE ≠ MATCH
      decide
    have tables0 : DataTableInvariant heap0 ready :=
      dataTableInvariant_inactive (by change ¬ DataTableMode TYPE; unfold DataTableMode; decide)
    have state0 := invariant.dictionary_update (Or.inr mode) good0 tables0 pending0
      (by rfl) (Or.inr rfl) invariant.held sizes0 static0
    have packet0 := buffers.byte_views invariant.good good0 rfl views readonly
    have selector : runX (inflate_dispatch c) l heap0 = runX (inflate_TYPE c) l heap0 := by
      rw [inflate_dispatch_block_type E0 l (Or.inl rfl), if_pos rfl]
    obtain ⟨_, _, _, _, _, _, _, run2, _, _, _, _, _, _, _, _, _, _, _, _, progress⟩ :=
      inflate_dispatch_type_state_rank E0 state0 packet0 (Or.inl rfl) incoming
    exact ordinary_not_ret progress
      (xrun_outcome_eq run2 (selector.trans ((inflate_DICT_ready_cut E l missing).symm.trans run)))

/-- A direct return of one dispatch from a state with `HeldBits` leaves a
state with `HeldBits`. -/
theorem inflate_dispatch_ret_held {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (local_ : HeaderLocal c h r s l) (incoming : l.bits.toNat ≤ 39)
    (held : s.mode ≠ BAD → s.mode ≠ MEM → s.mode ≠ SYNC → l.bits.toNat ≤ 32)
    {v : Int32} {regs : IL} {after : Heap} {state : InflateState}
    (run : runX (inflate_dispatch c) l h = .ok ((.error (.ret v), regs), after))
    (get : after.istates zs = some state) :
    HeldBits state := by
  by_cases special : s.mode = MEM ∨ s.mode = SYNC
  · obtain ⟨_, heapEq⟩ := inflate_dispatch_mem_sync_ret E invariant buffers special run
    subst heapEq
    have same : state = s := Option.some.inj (get.symm.trans invariant.good.live.hs)
    subst same
    intro _ notMem notSync
    rcases special with m | m
    · exact absurd m notMem
    · exact absurd m notSync
  have strong : s.mode ≠ BAD → l.bits.toNat ≤ 32 :=
    fun notBad => held notBad (fun m => special (Or.inl m)) (fun m => special (Or.inr m))
  rcases defaultMode_cases invariant.modes with head | dictionary | type | stored | construction | data | trailer | terminal | gzipHeader
  · exfalso
    by_cases gzip : GzipAllowed s.wrap
    · rcases gzip_dispatch_outcome E invariant buffers (Or.inl ⟨head, gzip⟩) local_ incoming run with e | e <;>
        cases e
    obtain ⟨_, _, _, _, _, _, _, source, _, _, _, _, _, _, _, _, _, _, _, progress⟩ :=
      inflate_dispatch_HEAD_state_rank E invariant buffers head gzip incoming
    exact ordinary_not_ret progress (xrun_outcome_eq source run)
  · rcases dictionary with id | dict
    · rw [inflate_dispatch_DICTID E l id] at run
      obtain ⟨_, current, used, pull, usedBound, bitInv, _, _, shape, _, _, _, _, kinds, cursor⟩ :=
        NEEDBITS_run_cursor buffers.bits 32 (by decide)
      rcases kinds with normal | wait
      · rw [normal] at pull
        let value := ZSWAP32 current.hold
        let ready := { s with check := value, mode := DICT }
        let stream0 := { z with adler := value }
        let heap0 := setI (r.put h stream0) zs ready
        let first := { current with hold := 0, bits := 0 }
        have good0 : Good heap0 r zs stream0 ready :=
          invariant.good.setZI rfl invariant.good.live.zalloc invariant.good.live.zfree rfl
            (by change HEAD ≤ DICT ∧ DICT ≤ SYNC; decide)
            (invariant.good.inv.of_fields rfl rfl rfl rfl rfl rfl rfl rfl rfl invariant.good.inv.bits rfl rfl rfl)
        have E0 : Env c heap0 r zs stream0 ready := ⟨E.strm, E.st, good0.live.hz, good0.live.hs⟩
        have pending0 : DataPendingInvariant ready := by
          apply dataPendingInvariant_idle (s := ready) (by exact invariant.pending.sane)
          change DICT ≠ LENEXT ∧ DICT ≠ DIST ∧ DICT ≠ DISTEXT ∧ DICT ≠ MATCH
          decide
        have inv0 : BitInv heap0 first (bs.drop used) := by
          have inv := (INITBITS_inv bitInv).1
          apply inv.byte_views
          intro ref
          rw [byte_view_get_setI, byte_view_get_stream_put]
        have packet0 : DispatchBuffers heap0 r first (bs.drop used) :=
          buffers.consume invariant.good good0 rfl (fun ref => by rw [byte_view_get_setI, byte_view_get_stream_put])
            (fun ref => by rw [byte_view_ro_setI, byte_view_ro_stream_put])
            (by dsimp only [first]; rw [shape]; rfl) cursor usedBound inv0
        have sizes0 : ByteViewSizes h heap0 := by
          intro ref
          rw [byte_view_get_setI, byte_view_get_stream_put]
        have static0 : heap0.static = h.static := by simp only [heap0, setI, ZStreamRef.put_static]
        have tables0 : DataTableInvariant heap0 ready :=
          dataTableInvariant_inactive (by change ¬ DataTableMode DICT; unfold DataTableMode; decide)
        have state0 := invariant.dictionary_update (Or.inl id) good0 tables0 pending0
          (by rfl) (Or.inl rfl) invariant.held sizes0 static0
        have bitsEq := inflate_DICT_ret_bits E0 state0 packet0 rfl (by change (0 : UInt32).toNat ≤ 39; simp)
          ((inflate_DICTID_parsed_cut E l current pull).symm.trans run) get
        intro _ _ _
        rw [bitsEq]
        change (0 : UInt32).toNat ≤ 32
        simp
      · exfalso
        have run2 := inflate_DICTID_wait (c := c) (by rwa [wait] at pull)
        cases xrun_outcome_eq run run2
    · rw [inflate_dispatch_DICT E l dict] at run
      have bitsEq := inflate_DICT_ret_bits E invariant buffers dict incoming run get
      intro _ _ _
      rw [bitsEq]
      exact strong (by rw [dict]; decide)
  · exfalso
    obtain ⟨_, _, _, _, _, _, _, source, _, _, _, _, _, _, _, _, _, _, _, _, progress⟩ :=
      inflate_dispatch_type_state_rank E invariant buffers type incoming
    exact ordinary_not_ret progress (xrun_outcome_eq source run)
  · exfalso
    obtain ⟨_, _, _, _, _, _, _, _, source, _, _, _, _, _, _, _, _, _, _, progress, _, _⟩ :=
      inflate_dispatch_stored_state_rank E invariant buffers stored incoming
    exact ordinary_not_ret progress (xrun_outcome_eq source run)
  · exfalso
    obtain ⟨_, _, _, _, _, _, _, _, source, _, _, _, _, _, _, _, _, progress⟩ :=
      inflate_dispatch_construction_view_state_rank E invariant buffers construction incoming
    exact ordinary_not_ret progress (xrun_outcome_eq source run)
  · exfalso
    obtain ⟨_, _, _, _, _, _, _, _, source, _, _, _, _, _, _, _, _, _, progress⟩ :=
      inflate_dispatch_data_view_state_rank E invariant buffers data
    exact ordinary_not_ret progress (xrun_outcome_eq source run)
  · exfalso
    rcases trailer with check | length
    · obtain ⟨_, _, _, _, _, _, _, source, _, _, _, _, _, _, _, _, _, progress⟩ :=
        inflate_CHECK_default_state_rank E invariant buffers check incoming
      exact ordinary_not_ret progress (xrun_outcome_eq source ((inflate_dispatch_CHECK E l check).symm.trans run))
    · obtain ⟨_, _, _, _, _, _, _, source, _, _, _, _, _, _, _, _, _, progress, _⟩ :=
        inflate_LENGTH_state_rank E invariant buffers length incoming
      exact ordinary_not_ret progress (xrun_outcome_eq source ((inflate_dispatch_LENGTH E l length).symm.trans run))
  · exfalso
    have source := inflate_dispatch_terminal_run E l terminal
    rcases terminal with done | bad | memory | sync
    · have impossible := xrun_outcome_eq source run
      rw [done] at impossible
      simp [terminalExit, DONE, BAD, SYNC] at impossible
    · have impossible := xrun_outcome_eq source run
      rw [bad] at impossible
      simp [terminalExit, DONE, BAD, MEM] at impossible
    · exact special (Or.inl memory)
    · exact special (Or.inr sync)
  · exfalso
    rcases gzip_dispatch_outcome E invariant buffers (Or.inr gzipHeader) local_ incoming run with e | e <;>
      cases e

/-- The loop invariant of the held-bit bound. -/
def HeldLoopInv (c : Ctx) (r : ZStreamRef) (zs : Nat) (l : IL) (h : Heap) : Prop :=
  ∃ z s bs, DefaultStateJ h r zs z s ∧ HeaderLocal c h r s l ∧ DispatchBuffers h r l bs ∧
    l.bits.toNat ≤ 39 ∧ (s.mode ≠ BAD → s.mode ≠ MEM → s.mode ≠ SYNC → l.bits.toNat ≤ 32)

/-- What the held-bit bound says at a loop exit. -/
def HeldLoopPost (zs : Nat) (exit : Ex) (l : IL) (h : Heap) : Prop :=
  ∀ state, h.istates zs = some state →
    (exit = .leave → state.mode ≠ BAD → state.mode ≠ MEM → state.mode ≠ SYNC → l.bits.toNat ≤ 32) ∧
    (∀ v, exit = .ret v → HeldBits state)

theorem inflate_dispatch_held_loop_step
    {c : Ctx} {r : ZStreamRef} {zs : Nat}
    (root : c.strm = some r) (stateRef : c.st = some (.tab zs))
    (l : IL) (h : Heap) (outcome : Except Ex Unit) (regs : IL) (after : Heap)
    (current : HeldLoopInv c r zs l h)
    (run : runX (inflate_dispatch c) l h = .ok ((outcome, regs), after)) :
    match outcome with
    | .ok () => HeldLoopInv c r zs regs after
    | .error exit => HeldLoopPost zs exit regs after := by
  obtain ⟨z, s, bs, invariant, local_, buffers, incoming, held⟩ := current
  have E : Env c h r zs z s := ⟨root, stateRef, invariant.good.live.hz, invariant.good.live.hs⟩
  obtain ⟨otherOutcome, otherRegs, otherHeap, stream, nextState, used, _, _, source,
    final, ⟨rest, _, packet⟩, _, _, _, _, _, bits, finalLocal, _⟩ :=
    inflate_dispatch_default_view_state_rank E invariant buffers local_ incoming
  obtain ⟨outcomeEq, regsEq, heapEq⟩ := runX_same run source
  subst outcomeEq regsEq heapEq
  cases outcome with
  | ok value =>
    cases value
    have strong := HeldBits.strong E invariant buffers held run (fun _ e => by cases e)
    exact ⟨stream, nextState, rest, final, finalLocal, packet, bits,
      fun notBad _ _ => inflate_dispatch_held_bound E invariant buffers local_ strong run final.good.live.hs notBad⟩
  | error exit =>
    intro state get
    have same : state = nextState := Option.some.inj (get.symm.trans final.good.live.hs)
    subst same
    cases exit with
    | leave =>
      have strong := HeldBits.strong E invariant buffers held run (fun _ e => by cases e)
      exact ⟨fun _ notBad _ _ => inflate_dispatch_held_bound E invariant buffers local_ strong run get notBad,
        fun _ e => by cases e⟩
    | ret v =>
      refine ⟨fun e => by cases e, ?_⟩
      intro w e
      cases e
      exact inflate_dispatch_ret_held E invariant buffers local_ incoming held run get

/-- The whole decoder loop of one call keeps the held-bit bound. -/
theorem inflate_run_held
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {regs : IL} {exit : Ex}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : StreamBuffers h r) (nonnull : z.next_out ≠ .null)
    (inputValid : z.next_in = .null → z.avail_in = 0)
    (local_ : HeaderLocal c h r s (dispatchRegs z s)) (held : HeldBits s)
    (run : runX (inflate_run c) IL.init h = .ok ((.error exit, regs), after)) :
    HeldLoopPost zs exit regs after := by
  obtain ⟨entryHeap, entryState, bs, cut, current, _, packet, bits, entrySizes, entryFrame, entryHeapEq,
    entryStateEq⟩ := inflate_run_default_view_entry E invariant buffers nonnull inputValid
  have entryLocal := inflate_run_entry_local invariant current entrySizes entryFrame entryHeapEq entryStateEq local_
  have start : HeldLoopInv c r zs (dispatchRegs z entryState) entryHeap := by
    refine ⟨z, entryState, bs, current, entryLocal, packet, bits, ?_⟩
    intro notBad notMem notSync
    have bitsEq : (dispatchRegs z entryState).bits = s.bits := by
      rw [entryStateEq]
      split <;> rfl
    have modeOf (m : UInt32) (special : m = BAD ∨ m = MEM ∨ m = SYNC) (sm : s.mode = m) : entryState.mode = m := by
      rw [entryStateEq]
      split
      · next type => rw [sm] at type; subst type; rcases special with e | e | e <;> exact absurd e (by decide)
      · exact sm
    rw [bitsEq]
    exact held (fun e => notBad (modeOf _ (Or.inl rfl) e)) (fun e => notMem (modeOf _ (Or.inr (Or.inl rfl)) e))
      (fun e => notSync (modeOf _ (Or.inr (Or.inr rfl)) e))
  rw [cut] at run
  apply xwhile_success_control_post (HeldLoopInv c r zs) (HeldLoopPost zs) ?_ start run
  intro before heap outcome finalRegs finalHeap valid source
  have result := inflate_dispatch_held_loop_step E.strm E.st before heap outcome
    finalRegs finalHeap valid source
  cases outcome with
  | ok value => cases value; exact result
  | error stopped => exact result

end Zlib.Inflate.Proofs
