import ZlibF.Proof.«inflate.c.held-bound»
import ZlibF.Proof.«inflate.c.gzip-dispatch-observe»
import ZlibF.Proof.«inflate.c.normal-mode-base»
import ZlibF.Proof.«inflate.c.loop-control-post»

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

end Zlib.Inflate.Proofs
