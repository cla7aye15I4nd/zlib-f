import ZlibF.Proof.«inflate.c.normal-mode-base»
import ZlibF.Proof.«inflate.c.dictid-dispatch»
import ZlibF.Proof.«inflate.c.dictionary-dispatch»

/-!
# inflate.c: dispatch from the dictionary modes stays past the header

From `DICTID` or `DICT` one dispatch returns in `DICTID`, `DICT` or one of
the block control modes, never in `HEAD` .. `HCRC`.
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

theorem blockControlMode_floor {mode : UInt32} (control : BlockControlMode mode) : DICTID ≤ mode := by
  rcases control with m | m | m | m | m | m | m <;> rw [m] <;> decide

theorem inflate_DICT_mode_floor {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s returned : InflateState} {l regs : IL} {bs : List UInt8} {outcome : Except Ex Unit}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = DICT) (incoming : l.bits.toNat ≤ 39)
    (actual : runX (inflate_DICT c) l h = .ok ((outcome, regs), after))
    (get : after.istates zs = some returned) : DICTID ≤ returned.mode := by
  by_cases missing : s.havedict = 0
  · have source := inflate_DICT_wait_run E l missing
    have same := xrun_state_eq (firstState := leaveState s l) source actual (by simp only [setI_istates_same]) get
    rw [← same]
    change DICTID ≤ s.mode
    rw [mode]
    decide
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
    have source : runX (inflate_TYPE c) l heap = .ok ((outcome, regs), after) :=
      (inflate_DICT_ready_cut E l missing).symm.trans actual
    obtain ⟨_, _, _, _, state, _, _, run, final, control, _⟩ :=
      inflate_dispatch_type_state_rank env current packet (Or.inl rfl) incoming
    have selected := inflate_dispatch_block_type env l (Or.inl rfl)
    rw [if_pos (show ready.mode = TYPE from rfl)] at selected
    have typeRun := selected.symm.trans run
    have same := xrun_state_eq typeRun source final.good.live.hs get
    rw [← same]
    exact blockControlMode_floor control

theorem inflate_DICTID_mode_floor {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s returned : InflateState} {l regs : IL} {bs : List UInt8} {outcome : Except Ex Unit}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = DICTID)
    (actual : runX (inflate_DICTID c) l h = .ok ((outcome, regs), after))
    (get : after.istates zs = some returned) : DICTID ≤ returned.mode := by
  obtain ⟨decision, currentRegs, used, pull, usedBound, bitInv, _, _, shape,
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
    have source : runX (inflate_DICT c) first heap = .ok ((outcome, regs), after) :=
      (inflate_DICTID_parsed_cut E l currentRegs pull).symm.trans actual
    exact inflate_DICT_mode_floor env current packet0 rfl (by change 0 ≤ 39; decide) source get
  · have source := inflate_DICTID_wait (c := c) (by rwa [wait] at pull)
    have same : after = h := congrArg Prod.snd (Except.ok.inj (actual.symm.trans source))
    rw [same, E.hs] at get
    cases get
    rw [mode]
    decide

theorem inflate_dispatch_dictionary_mode_floor {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s returned : InflateState} {l regs : IL} {bs : List UInt8} {outcome : Except Ex Unit}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = DICTID ∨ s.mode = DICT) (incoming : l.bits.toNat ≤ 39)
    (actual : runX (inflate_dispatch c) l h = .ok ((outcome, regs), after))
    (get : after.istates zs = some returned) : DICTID ≤ returned.mode := by
  rcases mode with id | dictionary
  · rw [inflate_dispatch_DICTID E l id] at actual
    exact inflate_DICTID_mode_floor E invariant buffers id actual get
  · rw [inflate_dispatch_DICT E l dictionary] at actual
    exact inflate_DICT_mode_floor E invariant buffers dictionary incoming actual get

#print axioms inflate_dispatch_dictionary_mode_floor
end Zlib.Inflate.Proofs
