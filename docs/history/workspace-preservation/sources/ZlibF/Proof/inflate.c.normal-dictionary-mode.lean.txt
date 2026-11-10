import ZlibF.Proof.«inflate.c.normal-mode-bound»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- A normal DICT execution must take the supplied-dictionary branch
and its actual TYPE continuation. It cannot create MEM or SYNC. -/
theorem inflate_DICT_normal_mode
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s state : InflateState} {l regs : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = DICT) (bits : l.bits.toNat ≤ 39)
    (run : runX (inflate_DICT c) l h = .ok ((.ok (), regs), after))
    (observed : after.istates zs = some state) : state.mode ≤ BAD := by
  by_cases missing : s.havedict = 0
  · have source := inflate_DICT_wait_run E l missing
    have same := Except.ok.inj (source.symm.trans run)
    have impossible : (.error (Ex.ret Z_NEED_DICT) : Except Ex Unit) = .ok () :=
      congrArg (fun pair => pair.1.1) same
    cases impossible
  · let ready := { s with check := 1, mode := TYPE }
    let stream0 := { z with adler := 1 }
    let heap0 := setI (r.put h stream0) zs ready
    have good0 : Good heap0 r zs stream0 ready :=
      invariant.good.setZI rfl invariant.good.live.zalloc invariant.good.live.zfree rfl
        (by change HEAD ≤ TYPE ∧ TYPE ≤ SYNC; decide)
        (invariant.good.inv.of_fields rfl rfl rfl rfl rfl rfl rfl rfl rfl invariant.good.inv.bits rfl rfl rfl)
    have env0 : Env c heap0 r zs stream0 ready := ⟨E.strm, E.st, good0.live.hz, good0.live.hs⟩
    have views : ∀ ref : BRef, (Space.get heap0 ref : Option (Array UInt8)) = Space.get h ref := by
      intro ref
      rw [byte_view_get_setI, byte_view_get_stream_put]
    have readonly : ∀ ref : BRef, Space.ro heap0 ref = Space.ro h ref := by
      intro ref
      rw [byte_view_ro_setI, byte_view_ro_stream_put]
    have sizes : ByteViewSizes h heap0 := by intro ref; rw [views]
    have static : heap0.static = h.static := by simp only [heap0, setI, ZStreamRef.put_static]
    have pending : DataPendingInvariant ready := by
      apply dataPendingInvariant_idle (s := ready) invariant.pending.sane
      change TYPE ≠ LENEXT ∧ TYPE ≠ DIST ∧ TYPE ≠ DISTEXT ∧ TYPE ≠ MATCH
      decide
    have tables : DataTableInvariant heap0 ready :=
      dataTableInvariant_inactive (by change ¬ DataTableMode TYPE; unfold DataTableMode; decide)
    have current := invariant.dictionary_update (Or.inr mode) good0 tables pending (by rfl)
      (Or.inr rfl) invariant.held sizes static
    have packet := buffers.byte_views invariant.good good0 rfl views readonly
    have selector : runX (inflate_dispatch c) l heap0 = runX (inflate_TYPE c) l heap0 := by
      rw [inflate_dispatch_block_type env0 l (Or.inl rfl), if_pos rfl]
    exact inflate_dispatch_type_normal_mode env0 current packet (Or.inl rfl) bits
      (selector.trans ((inflate_DICT_ready_cut E l missing).symm.trans run)) observed

/-- DICTID reads the real word, resets held bits and executes DICT.
Normal completion inherits the checked block-mode bound. -/
theorem inflate_DICTID_normal_mode
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s state : InflateState} {l regs : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = DICTID)
    (run : runX (inflate_DICTID c) l h = .ok ((.ok (), regs), after))
    (observed : after.istates zs = some state) : state.mode ≤ BAD := by
  obtain ⟨outcome, current, used, pull, usedBound, bitInv, _, _, shape, _, _, _, _, kinds, cursor⟩ :=
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
    have env0 : Env c heap0 r zs stream0 ready := ⟨E.strm, E.st, good0.live.hz, good0.live.hs⟩
    have pending : DataPendingInvariant ready := by
      apply dataPendingInvariant_idle (s := ready) invariant.pending.sane
      change DICT ≠ LENEXT ∧ DICT ≠ DIST ∧ DICT ≠ DISTEXT ∧ DICT ≠ MATCH
      decide
    have bits0 : BitInv heap0 first (bs.drop used) := by
      apply (INITBITS_inv bitInv).1.byte_views
      intro ref
      rw [byte_view_get_setI, byte_view_get_stream_put]
    have packet : DispatchBuffers heap0 r first (bs.drop used) :=
      buffers.consume invariant.good good0 rfl (fun ref => by rw [byte_view_get_setI, byte_view_get_stream_put])
        (fun ref => by rw [byte_view_ro_setI, byte_view_ro_stream_put])
        (by dsimp only [first]; rw [shape]; rfl) cursor usedBound bits0
    have sizes : ByteViewSizes h heap0 := by
      intro ref
      rw [byte_view_get_setI, byte_view_get_stream_put]
    have static : heap0.static = h.static := by simp only [heap0, setI, ZStreamRef.put_static]
    have tables : DataTableInvariant heap0 ready :=
      dataTableInvariant_inactive (by change ¬ DataTableMode DICT; unfold DataTableMode; decide)
    have currentJ := invariant.dictionary_update (Or.inl mode) good0 tables pending (by rfl)
      (Or.inl rfl) invariant.held sizes static
    exact inflate_DICT_normal_mode env0 currentJ packet rfl (by change 0 ≤ 39; decide)
      ((inflate_DICTID_parsed_cut E l current pull).symm.trans run) observed
  · rw [wait] at pull
    have source := inflate_DICTID_wait (c := c) pull
    have same := Except.ok.inj (source.symm.trans run)
    have impossible : (.error Ex.leave : Except Ex Unit) = .ok () := congrArg (fun pair => pair.1.1) same
    cases impossible

end Zlib.Inflate.Proofs
