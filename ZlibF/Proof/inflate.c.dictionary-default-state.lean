import ZlibF.Proof.«inflate.c.construction-default-state»
import ZlibF.Proof.«inflate.c.terminal-dispatch»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Fields written by dictionary-id parsing, checksum reset and direct
request writeback. All reset configuration and wrapper fields are retained. -/
def DictionaryFieldsFrame (before after : InflateState) : Prop :=
  after = { before with check := after.check, mode := after.mode, hold := after.hold, bits := after.bits }

theorem DefaultStateJ.dictionary_format {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (invariant : DefaultStateJ h r zs z s)
    (mode : s.mode = DICTID ∨ s.mode = DICT) : s.wrap = 0 ∨ s.flags = 0 := by
  rcases invariant.phase with head | bad | mem | sync | format
  · rcases mode with selected | selected <;> rw [selected] at head <;> contradiction
  · rcases mode with selected | selected <;> rw [selected] at bad <;> contradiction
  · rcases mode with selected | selected <;> rw [selected] at mem <;> contradiction
  · rcases mode with selected | selected <;> rw [selected] at sync <;> contradiction
  · exact format

/-- Actual dictionary metadata and bit writeback preserve the full default
state relation. Held bits come from the actual source buffer invariant. -/
theorem DefaultStateJ.dictionary_update {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z stream : ZStream} {s state : InflateState} (invariant : DefaultStateJ h r zs z s)
    (beforeMode : s.mode = DICTID ∨ s.mode = DICT)
    (current : Good after r zs stream state) (tables : DataTableInvariant after state)
    (pending : DataPendingInvariant state) (frame : DictionaryFieldsFrame s state)
    (modes : state.mode = DICT ∨ state.mode = TYPE) (held : state.hold.toNat < 2 ^ state.bits.toNat)
    (sizes : ByteViewSizes h after) (static : after.static = h.static) :
    DefaultStateJ after r zs stream state := by
  have guards : state.mode ≠ CODELENS ∧ state.mode ≠ LENLENS ∧ state.mode ≠ CHECK ∧ state.mode ≠ LENGTH ∧
      DICTID ≤ state.mode ∧ state.mode ≤ SYNC := by
    rcases modes with selected | selected <;> rw [selected] <;> decide
  have base : DefaultDecodeJ after r zs stream state := by
    refine ⟨current, tables, pending, ?_, ?_, held, ?_, ?_, ?_, Or.inr guards.2.2.2.2, ?_, ?_, sizes.platform invariant.platform⟩
    · intro active
      exact False.elim (guards.1 active)
    · intro active
      exact False.elim (guards.2.1 active)
    · rw [frame]
      exact invariant.window
    · rw [frame]
      exact invariant.wrapper
    · rw [frame]
      exact invariant.header
    · rintro (active | active)
      · exact False.elim (guards.2.2.1 active)
      · exact False.elim (guards.2.2.2.1 active)
    · change after.static = _
      rw [static]
      exact invariant.globals
  have config : DefaultConfigFrame s state := by rw [frame]; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  exact invariant.config_update base config (invariant.dictionary_format beforeMode)

/-- Actual DICT either writes back normalized bits and directly requests
its dictionary, or resets the checksum and executes the real TYPE branch. -/
theorem inflate_DICT_default_state {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = DICT) (incoming : l.bits.toNat ≤ 39) :
    ∃ outcome regs after stream state,
      runX (inflate_DICT c) l h = .ok ((outcome, regs), after) ∧ DefaultStateJ after r zs stream state := by
  by_cases missing : s.havedict = 0
  · obtain ⟨run, current, tables, pending, _, sizes, static, held, _, _⟩ :=
      inflate_DICT_wait_boundary E invariant.good invariant.pending buffers mode missing incoming
    have final := invariant.dictionary_update (Or.inr mode) current tables pending
      (by rfl) (Or.inl mode) held sizes static
    exact ⟨.error (Ex.ret Z_NEED_DICT), l, _, _, _, run, final⟩
  · let ready := { s with check := 1, mode := TYPE }
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
    obtain ⟨outcome, regs, after, stream, state, _, _, run, final, _⟩ :=
      inflate_dispatch_type_state_rank E0 state0 packet0 (Or.inl rfl) incoming
    have selector : runX (inflate_dispatch c) l heap0 = runX (inflate_TYPE c) l heap0 := by
      rw [inflate_dispatch_block_type E0 l (Or.inl rfl), if_pos rfl]
    exact ⟨outcome, regs, after, stream, state,
      (inflate_DICT_ready_cut E l missing).trans (selector.symm.trans run), final⟩

/-- Actual DICT preserves the full default relation and its complete
buffer/rank result, including its distinct direct Z_NEED_DICT exit. -/
theorem inflate_DICT_default_state_rank {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = DICT) (incoming : l.bits.toNat ≤ 39) :
    ∃ outcome regs after stream state used, used ≤ bs.length ∧
      runX (inflate_DICT c) l h = .ok ((outcome, regs), after) ∧ DefaultStateJ after r zs stream state ∧
      DispatchBuffers after r regs (bs.drop used) ∧ ByteViewSizes h after ∧
      regs.next = inputAdvance l.next used ∧ regs.have_.toNat + used = l.have_.toNat ∧
      regs.put = l.put ∧ regs.left = l.left ∧ regs.bits.toNat ≤ 39 ∧ after.static = h.static ∧
      (outcome = .error (Ex.ret Z_NEED_DICT) ∨ outcome = .error Ex.leave ∨
        (outcome = .ok () ∧ dispatchRank regs state.mode < dispatchRank l s.mode)) := by
  obtain ⟨outcome, regs, after, stream, state, run, final⟩ := inflate_DICT_default_state E invariant buffers mode incoming
  obtain ⟨otherOutcome, otherRegs, otherHeap, otherStream, otherState, used, bound, otherRun,
    good, _, _, packet, sizes, next, count, put, left, bits, static, progress⟩ :=
    inflate_DICT_rank E invariant.good invariant.pending buffers invariant.globals mode incoming
  rw [run] at otherRun
  cases otherRun
  have streamEq : otherStream = stream := Option.some.inj (good.live.hz.symm.trans final.good.live.hz)
  have stateEq : otherState = state := Option.some.inj (good.live.hs.symm.trans final.good.live.hs)
  subst otherStream otherState
  exact ⟨outcome, regs, after, stream, state, used, bound, run, final, packet,
    sizes, next, count, put, left, bits, static, progress⟩

/-- The entire actual DICTID/DICT/TYPE chain preserves the full default
state and exact caller packet, including the early direct dictionary return. -/
theorem inflate_DICTID_default_state_rank {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs)
    (mode : s.mode = DICTID) (incoming : l.bits.toNat ≤ 39) :
    ∃ outcome regs after stream state used, used ≤ bs.length ∧
      runX (inflate_DICTID c) l h = .ok ((outcome, regs), after) ∧
      DefaultStateJ after r zs stream state ∧
      DispatchBuffers after r regs (bs.drop used) ∧ ByteViewSizes h after ∧
      regs.next = inputAdvance l.next used ∧ regs.have_.toNat + used = l.have_.toNat ∧
      regs.put = l.put ∧ regs.left = l.left ∧ regs.bits.toNat ≤ 39 ∧ after.static = h.static ∧
      (outcome = .error (Ex.ret Z_NEED_DICT) ∨ outcome = .error Ex.leave ∨
        (outcome = .ok () ∧ dispatchRank regs state.mode < dispatchRank l s.mode)) := by
  let good := invariant.good
  let pending := invariant.pending
  obtain ⟨outcome, current, used, pull, usedBound, bitInv, _, _, shape,
    bitBound, _, _, _, kinds, cursor⟩ := NEEDBITS_run_cursor buffers.bits 32 (by decide)
  change current.bits.toNat ≤ max l.bits.toNat 39 at bitBound
  have count : current.have_.toNat + used = l.have_.toNat := by
    rw [bitInv.have_eq, buffers.bits.have_eq, List.length_drop]
    omega
  have put : current.put = l.put := by rw [shape]
  have left : current.left = l.left := by rw [shape]
  have packet : DispatchBuffers h r current (bs.drop used) :=
    buffers.consume good good rfl (fun _ => rfl) (fun _ => rfl) (by rw [shape]; rfl) cursor usedBound bitInv
  rcases kinds with normal | wait
  · rw [normal] at pull
    let value := ZSWAP32 current.hold
    let ready := { s with check := value, mode := DICT }
    let stream0 := { z with adler := value }
    let heap0 := setI (r.put h stream0) zs ready
    let first := { current with hold := 0, bits := 0 }
    have good0 : Good heap0 r zs stream0 ready :=
      good.setZI rfl good.live.zalloc good.live.zfree rfl (by change HEAD ≤ DICT ∧ DICT ≤ SYNC; decide)
        (good.inv.of_fields rfl rfl rfl rfl rfl rfl rfl rfl rfl good.inv.bits rfl rfl rfl)
    have E0 : Env c heap0 r zs stream0 ready := ⟨E.strm, E.st, good0.live.hz, good0.live.hs⟩
    have pending0 : DataPendingInvariant ready := by
      apply dataPendingInvariant_idle (s := ready) (by exact pending.sane)
      change DICT ≠ LENEXT ∧ DICT ≠ DIST ∧ DICT ≠ DISTEXT ∧ DICT ≠ MATCH
      decide
    have inv0 : BitInv heap0 first (bs.drop used) := by
      have inv := (INITBITS_inv bitInv).1
      apply inv.byte_views
      intro ref
      rw [byte_view_get_setI, byte_view_get_stream_put]
    have packet0 : DispatchBuffers heap0 r first (bs.drop used) :=
      buffers.consume good good0 rfl (fun ref => by rw [byte_view_get_setI, byte_view_get_stream_put])
        (fun ref => by rw [byte_view_ro_setI, byte_view_ro_stream_put])
        (by dsimp only [first]; rw [shape]; rfl) cursor usedBound inv0
    have sizes0 : ByteViewSizes h heap0 := by
      intro ref
      rw [byte_view_get_setI, byte_view_get_stream_put]
    have static0 : heap0.static = h.static := by simp only [heap0, setI, ZStreamRef.put_static]
    have tables0 : DataTableInvariant heap0 ready :=
      dataTableInvariant_inactive (by change ¬ DataTableMode DICT; unfold DataTableMode; decide)
    have state0 := invariant.dictionary_update (Or.inl mode) good0 tables0 pending0
      (by rfl) (Or.inl rfl) invariant.held sizes0 static0
    obtain ⟨exit, regs, after, stream, state, used2, bound2, run, finalState,
      nextPacket, sizes, next2, count2, put2, left2, bits, static, exits⟩ :=
      inflate_DICT_default_state_rank E0 state0 packet0 rfl (by change 0 ≤ 39; decide)
    have before : dispatchRank first ready.mode < dispatchRank l s.mode := by
      apply dispatchRank_advance (l := l) (regs := first) (used := used) (made := 0) count
      · change current.left.toNat + 0 = l.left.toNat
        rw [left]
        rfl
      · change 0 ≤ _
        omega
      · right
        change dispatchCredit DICT < dispatchCredit s.mode
        rw [mode]
        decide
    have totalBound : used + used2 ≤ bs.length := by rw [List.length_drop] at bound2; omega
    refine ⟨exit, regs, after, stream, state, used + used2, totalBound,
      (inflate_DICTID_parsed_cut E l current pull).trans run, finalState,
      ?_, sizes0.trans sizes, ?_, ?_, ?_, ?_, bits, static.trans static0, ?_⟩
    · simpa only [List.drop_drop] using nextPacket
    · rw [next2]
      change inputAdvance current.next used2 = _
      rw [cursor, inputAdvance_add]
    · change regs.have_.toNat + used2 = current.have_.toNat at count2
      omega
    · exact put2.trans put
    · exact left2.trans left
    · rcases exits with needed | wait | ⟨normal, decreases⟩
      · exact Or.inl needed
      · exact Or.inr (Or.inl wait)
      · exact Or.inr (Or.inr ⟨normal, Nat.lt_trans decreases before⟩)
  · have run := inflate_DICTID_wait (c := c) (by rwa [wait] at pull)
    exact ⟨.error Ex.leave, current, h, z, s, used, usedBound, run, invariant,
      packet, ByteViewSizes.refl h, cursor, count, put, left, by omega, rfl, Or.inr (Or.inl rfl)⟩

/-- Both actual dictionary switch entries use the same complete default
state and bounded progress result. The direct return remains explicit. -/
theorem inflate_dispatch_dictionary_state_rank {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = DICTID ∨ s.mode = DICT) (incoming : l.bits.toNat ≤ 39) :
    ∃ outcome regs after stream state used, used ≤ bs.length ∧
      runX (inflate_dispatch c) l h = .ok ((outcome, regs), after) ∧ DefaultStateJ after r zs stream state ∧
      DispatchBuffers after r regs (bs.drop used) ∧ ByteViewSizes h after ∧
      regs.next = inputAdvance l.next used ∧ regs.have_.toNat + used = l.have_.toNat ∧
      regs.put = l.put ∧ regs.left = l.left ∧ regs.bits.toNat ≤ 39 ∧ after.static = h.static ∧
      (outcome = .error (Ex.ret Z_NEED_DICT) ∨ outcome = .error Ex.leave ∨
        (outcome = .ok () ∧ dispatchRank regs state.mode < dispatchRank l s.mode)) := by
  rcases mode with id | dictionary
  · rw [inflate_dispatch_DICTID E l id]
    exact inflate_DICTID_default_state_rank E invariant buffers id incoming
  · rw [inflate_dispatch_DICT E l dictionary]
    exact inflate_DICT_default_state_rank E invariant buffers dictionary incoming

/-- Actual terminal/error dispatch changes no heap or decoder fields,
so it retains the full default state relation on all four exit paths. -/
theorem inflate_dispatch_terminal_state {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : TerminalMode s.mode) :
    runX (inflate_dispatch c) l h = .ok ((terminalExit s.mode, terminalRegs s.mode l), h) ∧
      DefaultStateJ h r zs z s ∧ DispatchBuffers h r (terminalRegs s.mode l) bs ∧
      (terminalRegs s.mode l).bits = l.bits ∧ (terminalRegs s.mode l).hold = l.hold := by
  obtain ⟨run, _, _, _, packet, bits, hold⟩ :=
    inflate_dispatch_terminal_boundary E invariant.good invariant.pending buffers mode
  exact ⟨run, invariant, packet, bits, hold⟩

end Zlib.Inflate.Proofs
