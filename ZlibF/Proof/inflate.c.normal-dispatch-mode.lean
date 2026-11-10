import ZlibF.Proof.«inflate.c.normal-dictionary-mode»
import ZlibF.Proof.«inflate.c.check-return-shape»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Every normal iteration of the actual default mode loop stays at or
below BAD. MEM and SYNC are direct terminal entries, never successors of
a continuing dispatch. This is derived from all source mode families. -/
theorem inflate_dispatch_default_normal_mode
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s state : InflateState} {l regs : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (raw : RawFastIO l) (bits : l.bits.toNat ≤ 39)
    (run : runX (inflate_dispatch c) l h = .ok ((.ok (), regs), after))
    (observed : after.istates zs = some state) : state.mode ≤ BAD := by
  rcases defaultMode_cases invariant.modes with head | dictionary | block | stored | construction | data | trailer | terminal
  · have executed := (inflate_dispatch_HEAD E l head).symm.trans run
    rcases invariant.wrapper with rawWrap | wrapped
    · have source := inflate_HEAD_raw_run E l rawWrap
      have currentGet : (setI h zs { s with mode := TYPEDO }).istates zs = some { s with mode := TYPEDO } := by simp
      have same := runX_state_unique source currentGet executed observed
      rw [← same]
      change TYPEDO ≤ BAD
      decide
    · obtain ⟨outcome, regs2, heap2, stream2, state2, used, bound, source, good,
        tables, pending, packet, sizes, next, count, put, left, bitCount, static, kinds, rest⟩ :=
        inflate_HEAD_zlib_window_boundary_budget E invariant.good invariant.pending buffers head wrapped
          invariant.header invariant.window
      have same := Except.ok.inj (source.symm.trans executed)
      have result : outcome = .ok () := congrArg (fun pair => pair.1.1) same
      have stateEq := runX_state_unique source good.live.hs executed observed
      rcases kinds with ⟨wait, _⟩ | ⟨_, modes⟩
      · cases wait.symm.trans result
      · rw [← stateEq]
        rcases modes with equal | equal | equal
        all_goals rw [equal]; decide
  · rcases dictionary with id | dict
    · exact inflate_DICTID_normal_mode E invariant buffers id
        ((inflate_dispatch_DICTID E l id).symm.trans run) observed
    · exact inflate_DICT_normal_mode E invariant buffers dict bits
        ((inflate_dispatch_DICT E l dict).symm.trans run) observed
  · exact inflate_dispatch_type_normal_mode E invariant buffers block bits run observed
  · obtain ⟨outcome, regs2, heap2, stream2, state2, source, current, modes⟩ :=
      inflate_dispatch_stored_state E invariant buffers stored
    have same := runX_state_unique source current.good.live.hs run observed
    rw [← same]
    exact storedExitMode_le_bad modes
  · exact inflate_dispatch_construction_normal_mode E invariant buffers construction raw run observed
  · exact inflate_dispatch_data_normal_mode E invariant buffers data raw run observed
  · rcases trailer with check | length
    · have shape := inflate_CHECK_default_return_shape E invariant buffers check
        ((inflate_dispatch_CHECK E l check).symm.trans run) observed
      rcases shape with ⟨impossible, _⟩ | ⟨_, _, bad, _⟩ | ⟨impossible, _⟩
      · cases impossible
      · rw [bad]
        decide
      · cases impossible
    · obtain ⟨source, current, _⟩ := inflate_LENGTH_default_state_boundary E invariant buffers length
      have same := Except.ok.inj (((inflate_dispatch_LENGTH E l length).trans source).symm.trans run)
      have impossible : (.error Ex.leave : Except Ex Unit) = .ok () := congrArg (fun pair => pair.1.1) same
      cases impossible
  · have source := inflate_dispatch_terminal_run E l terminal
    have same := Except.ok.inj (source.symm.trans run)
    have result : terminalExit s.mode = .ok () := congrArg (fun pair => pair.1.1) same
    rcases terminal with equal | equal | equal | equal
    all_goals rw [equal] at result; simp [terminalExit, DONE, BAD, MEM, SYNC] at result

end Zlib.Inflate.Proofs
