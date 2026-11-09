import ZlibF.Proof.«inflate.c.local-normal-mode-base»

namespace Zlib.Inflate.Local
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- A normal DICT return runs the actual prepared TYPE branch. The
missing-dictionary branch is a distinct direct return. -/
theorem inflate_DICT_normal_low
    {c : Ctx} {h after : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s returned : InflateState} {l regs : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : LocalStateJ h cutoff r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = DICT) (incoming : l.bits.toNat ≤ 39)
    (run : runX (inflate_DICT c) l h = .ok ((.ok (), regs), after))
    (get : after.istates zs = some returned) : returned.mode < MEM := by
  by_cases missing : s.havedict = 0
  · have source := inflate_DICT_wait_run E l missing
    have impossible := xrun_outcome_eq source run
    cases impossible
  · let ready := { s with check := 1, mode := TYPE }
    let stream := { z with adler := 1 }
    let heap := setI (r.put h stream) zs ready
    have current : LocalStateJ heap cutoff r zs stream ready :=
      invariant.prepare_dictionary (Or.inr mode) 1 TYPE (Or.inr rfl)
    have env : Env c heap r zs stream ready :=
      ⟨E.strm, E.st, current.good.live.hz, current.good.live.hs⟩
    have views : ∀ ref : BRef, (Space.get heap ref : Option (Array UInt8)) = Space.get h ref := by
      intro ref
      rw [byte_view_get_setI, byte_view_get_stream_put]
    have ro : ∀ ref : BRef, Space.ro heap ref = Space.ro h ref := by
      intro ref
      rw [byte_view_ro_setI, byte_view_ro_stream_put]
    have packet := dispatch_byte_views_local buffers invariant.good current.good rfl views ro
    have selector : runX (inflate_dispatch c) l heap = runX (inflate_TYPE c) l heap := by
      rw [inflate_dispatch_block_type env l (Or.inl rfl), ite_eq_left rfl]
    have actual : runX (inflate_dispatch c) l heap = .ok ((.ok (), regs), after) :=
      selector.trans ((inflate_DICT_ready_cut E l missing).symm.trans run)
    obtain ⟨outcome, finalRegs, finalHeap, finalStream, state, used, _, source, final,
      modes, _, _, _, _, _, _, _, _, _, _, _⟩ :=
      inflate_dispatch_type_state_rank env current packet (Or.inl rfl) incoming
    have same := xrun_state_eq source actual final.good.live.hs get
    rw [← same]
    exact modes.lt_mem

/-- The actual dictionary-id read enters DICT with a cleared local bit
buffer. A normal continuation is therefore still below terminal errors. -/
theorem inflate_DICTID_normal_low
    {c : Ctx} {h after : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s returned : InflateState} {l regs : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : LocalStateJ h cutoff r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = DICTID)
    (run : runX (inflate_DICTID c) l h = .ok ((.ok (), regs), after))
    (get : after.istates zs = some returned) : returned.mode < MEM := by
  obtain ⟨outcome, currentRegs, used, pull, usedBound, bitInv, _, _, shape,
    _, _, _, _, kinds, cursor⟩ := NEEDBITS_run_cursor buffers.bits 32 (by decide)
  rcases kinds with normal | wait
  · rw [normal] at pull
    let value := ZSWAP32 currentRegs.hold
    let ready := { s with check := value, mode := DICT }
    let stream := { z with adler := value }
    let heap := setI (r.put h stream) zs ready
    let first := { currentRegs with hold := 0, bits := 0 }
    have current : LocalStateJ heap cutoff r zs stream ready :=
      invariant.prepare_dictionary (Or.inl mode) value DICT (Or.inl rfl)
    have env : Env c heap r zs stream ready :=
      ⟨E.strm, E.st, current.good.live.hz, current.good.live.hs⟩
    have packet : DispatchBuffers h r currentRegs (bs.drop used) :=
      dispatch_consume_local buffers invariant.good invariant.good rfl (fun _ => rfl) (fun _ => rfl)
        (by rw [shape]; rfl) cursor usedBound bitInv
    have views : ∀ ref : BRef, (Space.get heap ref : Option (Array UInt8)) = Space.get h ref := by
      intro ref
      rw [byte_view_get_setI, byte_view_get_stream_put]
    have ro : ∀ ref : BRef, Space.ro heap ref = Space.ro h ref := by
      intro ref
      rw [byte_view_ro_setI, byte_view_ro_stream_put]
    have packet0 : DispatchBuffers heap r first (bs.drop used) :=
      (dispatch_byte_views_local packet invariant.good current.good rfl views ro).clear_bits
    have actual : runX (inflate_DICT c) first heap = .ok ((.ok (), regs), after) :=
      (inflate_DICTID_parsed_cut E l currentRegs pull).symm.trans run
    exact inflate_DICT_normal_low env current packet0 rfl (by change 0 ≤ 39; decide) actual get
  · have source := inflate_DICTID_wait (c := c) (by rwa [wait] at pull)
    have impossible := xrun_outcome_eq source run
    cases impossible

end Zlib.Inflate.Local
