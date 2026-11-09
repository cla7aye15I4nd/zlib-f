import ZlibF.Proof.«inflate.c.origin-fields-head»
import ZlibF.Proof.«inflate.c.normal-mode-dictionary»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Actual DICT either restores the old fields on a dictionary request or
continues through the real TYPE parser after resetting the checksum. -/
theorem inflate_DICT_origin_record {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l regs : IL} {bs : List UInt8} {outcome : Except Ex Unit}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = DICT)
    (actual : runX (inflate_DICT c) l h = .ok ((outcome, regs), after)) :
    ∃ state, after.istates zs = some state ∧ state.flags = s.flags ∧ BlockHeaderPointers s state := by
  by_cases missing : s.havedict = 0
  · have source := inflate_DICT_wait_run E l missing
    have same : after = setI (r.put h (dictWaitStream z l)) zs (leaveState s l) :=
      congrArg Prod.snd (Except.ok.inj (actual.symm.trans source))
    exact ⟨leaveState s l, by rw [same]; exact setI_istates_same .., rfl, Or.inl ⟨rfl, rfl⟩⟩
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
    obtain ⟨state, get, flags, pointers⟩ := inflate_TYPE_origin_record env packet source
    exact ⟨state, get, flags, pointers⟩

/-- Actual DICTID observes the real word read and cleared bit buffer,
then composes the actual DICT origin observer. -/
theorem inflate_DICTID_origin_record {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l regs : IL} {bs : List UInt8} {outcome : Except Ex Unit}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = DICTID)
    (actual : runX (inflate_DICTID c) l h = .ok ((outcome, regs), after)) :
    ∃ state, after.istates zs = some state ∧ state.flags = s.flags ∧ BlockHeaderPointers s state := by
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
    obtain ⟨state, get, flags, pointers⟩ := inflate_DICT_origin_record env current packet0 rfl source
    exact ⟨state, get, flags, pointers⟩
  · have source := inflate_DICTID_wait (c := c) (by rwa [wait] at pull)
    have same : after = h := congrArg Prod.snd (Except.ok.inj (actual.symm.trans source))
    exact ⟨s, by rw [same]; exact E.hs, rfl, Or.inl ⟨rfl, rfl⟩⟩

/-- Both real dictionary switch entries retain the flag and either retain
the table pair or install the paired fixed tables in TYPE. -/
theorem inflate_dispatch_dictionary_origin_record {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l regs : IL} {bs : List UInt8} {outcome : Except Ex Unit}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = DICTID ∨ s.mode = DICT)
    (actual : runX (inflate_dispatch c) l h = .ok ((outcome, regs), after)) :
    ∃ state, after.istates zs = some state ∧ state.flags = s.flags ∧ BlockHeaderPointers s state := by
  rcases mode with id | dictionary
  · rw [inflate_dispatch_DICTID E l id] at actual
    exact inflate_DICTID_origin_record E invariant buffers id actual
  · rw [inflate_dispatch_DICT E l dictionary] at actual
    exact inflate_DICT_origin_record E invariant buffers dictionary actual

#print axioms inflate_dispatch_dictionary_origin_record
end Zlib.Inflate.Proofs
