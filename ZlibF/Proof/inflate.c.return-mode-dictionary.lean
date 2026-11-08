import ZlibF.Proof.«inflate.c.normal-mode-base»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false


/-- The actual missing-dictionary return retains the active DICT mode. -/
theorem inflate_DICT_need_mode
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s returned : InflateState} {l regs : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = DICT) (incoming : l.bits.toNat ≤ 39)
    (run : runX (inflate_DICT c) l h = .ok ((.error (.ret Z_NEED_DICT), regs), after))
    (get : after.istates zs = some returned) : returned.mode = DICT := by
  by_cases missing : s.havedict = 0
  · have source := inflate_DICT_wait_run E l missing
    have same := xrun_state_eq (firstState := leaveState s l) source run
      (by simp only [setI_istates_same]) get
    rw [← same]
    exact mode
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


theorem inflate_DICTID_need_mode
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s returned : InflateState} {l regs : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = DICTID)
    (run : runX (inflate_DICTID c) l h = .ok ((.error (.ret Z_NEED_DICT), regs), after))
    (get : after.istates zs = some returned) : returned.mode = DICT := by
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
    exact inflate_DICT_need_mode env current packet0 rfl (by change 0 ≤ 39; decide) actual get
  · have source := inflate_DICTID_wait (c := c) (by rwa [wait] at pull)
    have impossible := xrun_outcome_eq source run
    cases impossible

#print axioms inflate_DICTID_need_mode
end Zlib.Inflate.Proofs
