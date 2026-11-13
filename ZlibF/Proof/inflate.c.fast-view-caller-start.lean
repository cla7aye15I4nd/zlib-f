import ZlibF.Proof.«inflate.c.fast-view-caller-state»
import ZlibF.Proof.«inflate.c.default-state»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The actual LEN_ mode transition and full fast continuation preserve
the initialized default state on generic caller byte views. -/
theorem inflate_LEN_start_fast_view_state_run
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = LEN_)
    (fast : (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    ∃ regs after zNext sNext used made,
      runX (inflate_LEN_ c) l h = .ok ((.ok (), regs), after) ∧
      DefaultStateJ after r zs zNext sNext ∧
      StreamAccounting (leaveStream z l) zNext used made := by
  let current := { s with mode := LEN }
  let heap := setI h zs current
  have frame : DecodeStateFrame s current := rfl
  have good := invariant.good.decode_update frame
    (by change HEAD ≤ LEN ∧ LEN ≤ SYNC; decide)
  have oldMode : DataTableMode s.mode := by rw [mode]; unfold DataTableMode; decide
  have tables := (invariant.tables oldMode).decode_update invariant.good.live.hs frame
  have pending : DataPendingInvariant current := by
    apply dataPendingInvariant_idle (s := current) invariant.pending.sane
    change LEN ≠ LENEXT ∧ LEN ≠ DIST ∧ LEN ≠ DISTEXT ∧ LEN ≠ MATCH
    decide
  have decoded := invariant.toDefaultDecodeJ.decode_update good (fun _ => tables)
    pending frame
    (by change DataExitMode LEN; exact Or.inl (by unfold DataTableMode; decide))
    (byte_view_sizes_setI h zs current) rfl
  have currentJ : DefaultStateJ heap r zs z current :=
    ⟨decoded, invariant.requestedBits, invariant.requestedWrap,
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (invariant.data_format oldMode)))))⟩
  have packet : DispatchBuffers heap r l bs :=
    buffers.byte_views invariant.good good rfl
      (byte_view_get_setI h zs current) (byte_view_ro_setI h zs current)
  have env : Env c heap r zs z current :=
    ⟨E.strm, E.st, good.live.hz, good.live.hs⟩
  obtain ⟨regs, after, zNext, sNext, used, made, run, final, accounting⟩ :=
    inflate_LEN_fast_view_state_run env currentJ packet
      (by change DataTableMode LEN; unfold DataTableMode; decide) fast
  have source : runX (inflate_LEN_ c) l h = runX (inflate_LEN c) l heap := by
    unfold inflate_LEN_
    rw [runX_bind, runX_setMode E]
  exact ⟨regs, after, zNext, sNext, used, made, source.trans run, final, accounting⟩

#print axioms inflate_LEN_start_fast_view_state_run
end Zlib.Inflate.Proofs
