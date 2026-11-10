import ZlibF.Spec.InflatePendingInvariant
import ZlibF.Proof.«inflate.c.default-entry»
import ZlibF.Proof.«inflate.c.match-output»
import ZlibF.Proof.«inflate.c.literal-step»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Modes outside the pending scalar phases impose none of their constraints. -/
theorem dataPendingInvariant_idle {s : InflateState} (sane : s.sane = 1)
    (inactive : s.mode ≠ LENEXT ∧ s.mode ≠ DIST ∧ s.mode ≠ DISTEXT ∧ s.mode ≠ MATCH) :
    DataPendingInvariant s :=
  ⟨sane, fun mode => False.elim (inactive.1 mode),
    fun mode => False.elim (inactive.2.1 mode),
    fun mode => False.elim (inactive.2.2.1 mode),
    fun mode => False.elim (inactive.2.2.2 mode)⟩

/-- Initialization activates no pending data-decoder phase. -/
theorem dataPendingInvariant_head {s : InflateState} (sane : s.sane = 1) (mode : s.mode = HEAD) :
    DataPendingInvariant s := by
  apply dataPendingInvariant_idle sane
  rw [mode]
  decide

theorem dataPendingInvariant_lenext {s : InflateState} (sane : s.sane = 1)
    (mode : s.mode = LENEXT) (facts : LengthExtraSafe s) : DataPendingInvariant s := by
  refine ⟨sane, fun _ => facts, ?_, ?_, ?_⟩
  all_goals intro selected; rw [mode] at selected; contradiction

theorem dataPendingInvariant_dist {s : InflateState} (sane : s.sane = 1)
    (mode : s.mode = DIST) (facts : DistanceSafe s) : DataPendingInvariant s := by
  refine ⟨sane, ?_, fun _ => facts, ?_, ?_⟩
  all_goals intro selected; rw [mode] at selected; contradiction

theorem dataPendingInvariant_distext {s : InflateState} (sane : s.sane = 1)
    (mode : s.mode = DISTEXT) (facts : DistanceExtraSafe s) : DataPendingInvariant s := by
  refine ⟨sane, ?_, ?_, fun _ => facts, ?_⟩
  all_goals intro selected; rw [mode] at selected; contradiction

theorem dataPendingInvariant_match {s : InflateState} (sane : s.sane = 1)
    (mode : s.mode = MATCH) (facts : MatchSafe s) : DataPendingInvariant s := by
  refine ⟨sane, ?_, ?_, ?_, fun _ => facts⟩
  all_goals intro selected; rw [mode] at selected; contradiction

/-- The actual default initializer establishes the scalar clause from its
writes. The existing successful initialization theorem supplies the run,
Good, table clause and reachability on this same heap. -/
theorem inflate_default_pending_boundary
    (h : Heap) (r : ZStreamRef) (version : BPtr)
    (domain : InitDomain h r version) (platform : ZlibF.PlatformMemory.ByteObjectsFit h)
    (allocation : h.allocOk h.nalloc = true) :
    ∃ after z s,
      C.run (inflateInit_ (some r) version 112) h = .ok (Z_OK, after) ∧
      InflateInitial h after r .zlib 15 ∧ Good after r h.nextBlk z s ∧
      s.mode = HEAD ∧ DataTableInvariant after s ∧ DataPendingInvariant s ∧
      ZlibF.PlatformMemory.ByteObjectsFit after ∧ StreamReachable .inflate after r := by
  obtain ⟨after, z, s, run, initial, good, head, _, _, _, tables, fit, reachable⟩ :=
    inflate_default_init_boundary h r version domain platform allocation
  have sane := inflate_default_success_sane domain allocation run good
  exact ⟨after, z, s, run, initial, good, head, tables, dataPendingInvariant_head sane head, fit, reachable⟩

/-- A concrete default caller reaches the strengthened initial boundary. -/
theorem inflate_default_pending_witness :
    ∃ after z s,
      C.run (inflateInit_ (some (.tab 0)) (.ref (.blk 1) 0) 112) witnessHeap = .ok (Z_OK, after) ∧
      Good after (.tab 0) witnessHeap.nextBlk z s ∧ DataTableInvariant after s ∧
      DataPendingInvariant s ∧ StreamReachable .inflate after (.tab 0) := by
  obtain ⟨after, z, s, run, _, good, _, tables, pending, _, reachable⟩ :=
    inflate_default_pending_boundary witnessHeap (.tab 0) (.ref (.blk 1) 0)
      ZlibF.Spec.Public.Proofs.InflateInit.public_witness_domain inflate_default_witness_platform rfl
  exact ⟨after, z, s, run, good, tables, pending, reachable⟩

/-- The literal mode retains pending scalar safety at both its zero-output
exit and its actual LEN continuation. The fields are supplied by init and
prior dispatch transitions, rather than by public caller arguments. -/
theorem inflate_LIT_pending {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs : List UInt8}
    (E : Env c h r zs z s) (good : Good h r zs z s) (tables : DataTablesSafe h s)
    (buffers : DispatchBuffers h r l bs) (pending : DataPendingInvariant s) :
    ∃ outcome regs after state,
      runX (inflate_LIT c) l h = .ok ((outcome, regs), after) ∧
      Good after r zs z state ∧ DataTablesSafe after state ∧ DispatchBuffers after r regs bs ∧
      DataPendingInvariant state ∧ ByteViewSizes h after ∧ DecodeStateFrame s state := by
  obtain ⟨outcome, regs, after, state, run, finalGood, finalTables, packet, sizes, frame, _, kinds⟩ :=
    inflate_LIT_dispatch E good tables buffers
  refine ⟨outcome, regs, after, state, run, finalGood, finalTables, packet, ?_, sizes, frame⟩
  rcases kinds with ⟨_, _, _, stateEq⟩ | ⟨_, stateEq, _⟩
  · rwa [stateEq]
  · apply dataPendingInvariant_idle
    · rw [frame]
      exact pending.sane
    · rw [stateEq]
      change LEN ≠ LENEXT ∧ LEN ≠ DIST ∧ LEN ≠ DISTEXT ∧ LEN ≠ MATCH
      decide

/-- MATCH, LEN and BAD cannot enter either extra-bit phase by themselves. -/
theorem dataPendingInvariant_match_modes {s : InflateState} (sane : s.sane = 1)
    (modes : s.mode = MATCH ∨ s.mode = LEN ∨ s.mode = BAD)
    (matching : s.mode = MATCH → MatchSafe s) : DataPendingInvariant s := by
  refine ⟨sane, ?_, ?_, ?_, matching⟩
  · intro selected
    rcases modes with mode | mode | mode <;> rw [mode] at selected <;> contradiction
  · intro selected
    rcases modes with mode | mode | mode <;> rw [mode] at selected <;> contradiction
  · intro selected
    rcases modes with mode | mode | mode <;> rw [mode] at selected <;> contradiction

/-- An actual MATCH call preserves both the complete buffer relation and
pending scalar clauses, including output exhaustion, unavailable history
and a partially emitted overlapping copy. The two independently established
postconditions are identified using the same deterministic actual run. -/
theorem inflate_MATCH_pending {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs : List UInt8}
    (E : Env c h r zs z s) (good : Good h r zs z s) (tables : DataTablesSafe h s)
    (buffers : DispatchBuffers h r l bs) (pending : DataPendingInvariant s) (mode : s.mode = MATCH) :
    ∃ outcome regs after stream state made,
      runX (inflate_MATCH c) l h = .ok ((outcome, regs), after) ∧
      Good after r zs stream state ∧ DataTableInvariant after state ∧ DispatchBuffers after r regs bs ∧
      DataPendingInvariant state ∧ ByteViewSizes h after ∧ DecodeStateFrame s state ∧
      regs.left.toNat + made = l.left.toNat ∧ regs.put = inputAdvance l.put made ∧
      EmitRegFrame l regs ∧ Zlib.Inflate.Proofs.stream regs bs = Zlib.Inflate.Proofs.stream l bs ∧
      ((outcome = .error Ex.leave ∧ made = 0) ∨
        (outcome = .ok () ∧ state.mode = BAD ∧ made = 0) ∨
        (outcome = .ok () ∧ 0 < made ∧ (state.mode = LEN ∨ state.mode = MATCH))) := by
  have matchFacts := pending.matching mode
  have sane : s.sane ≠ 0 := by rw [pending.sane]; decide
  obtain ⟨outcome, regs, after, stream, state, made, run, finalGood, data, packet, sizes,
      frame, regFrame, residual, count, put, kinds⟩ :=
    inflate_MATCH_dispatch E good tables buffers mode matchFacts.1 matchFacts.2.2.2 sane
  have output : l.left ≠ 0 → ∃ (dest : BRef) (array : Array UInt8) (off : Nat),
      l.put = .ref dest off ∧ Space.get h dest = some array ∧ Space.ro h dest = false ∧
      off + l.left.toNat ≤ array.size ∧ l.left.toNat ≤ l.out_.toNat ∧
      l.out_.toNat - l.left.toNat ≤ off ∧
      (∀ w, s.window = .ref (.blk w) 0 → dest ≠ .blk w) ∧
      (bs = [] ∨ ∀ i, l.next = .ref dest i → i + bs.length ≤ off ∨ off + l.left.toNat ≤ i) := by
    intro nonempty
    obtain ⟨dest, array, off, ptr, get, write, room, total, produced, privateWindow⟩ :=
      callerRange_slow_output good l buffers.output.range buffers.output.nonnull
        buffers.output.count buffers.output.produced
    exact ⟨dest, array, off, ptr, get, write, room, total, produced, privateWindow,
      buffers.bits.output_positions ptr nonempty buffers.separate⟩
  obtain ⟨otherOutcome, otherRegs, otherHeap, otherStream, otherState, otherRun,
    otherGood, _, _, _, _, modes, retained, _, _⟩ :=
    inflate_MATCH_step_input E good tables buffers.bits mode matchFacts.1 matchFacts.2.1
      matchFacts.2.2.1 matchFacts.2.2.2 sane output
  have sameHeap : otherHeap = after :=
    congrArg Prod.snd (Except.ok.inj (otherRun.symm.trans run))
  have sameState : otherState = state := by
    apply Option.some.inj
    exact otherGood.live.hs.symm.trans (by rw [sameHeap]; exact finalGood.live.hs)
  subst otherState
  have invariant : DataPendingInvariant state := by
    apply dataPendingInvariant_match_modes (by rw [frame]; exact pending.sane) modes
    intro matching
    obtain ⟨positive, lengthWas, wasBound, offsetEq, _, _⟩ := retained matching
    exact ⟨positive, lengthWas, wasBound, by rw [offsetEq]; exact matchFacts.2.2.2⟩
  exact ⟨outcome, regs, after, stream, state, made, run, finalGood, data, packet,
    invariant, sizes, frame, count, put, regFrame, by rw [regFrame]; rfl, kinds⟩

end Zlib.Inflate.Proofs
