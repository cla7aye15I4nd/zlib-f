import ZlibF.Proof.«inflate.c.fast-view-caller-step»
import ZlibF.Proof.«inflate.c.fast-view-caller-start»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The actual LEN_ mode write and full fast continuation retain the
complete generic caller buffer packet, state, source-bit accounting and
a strict decrease of the original outer dispatch rank. -/
theorem inflate_LEN_start_fast_view_step
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = LEN_)
    (fast : (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    ∃ regs after stream state used made, used ≤ bs.length ∧
      runX (inflate_LEN_ c) l h = .ok ((.ok (), regs), after) ∧
      DefaultStateJ after r zs stream state ∧ DataExitMode state.mode ∧
      DispatchBuffers after r regs (bs.drop used) ∧
      ByteViewSizes h after ∧
      regs.next = inputAdvance l.next used ∧ regs.have_.toNat + used = l.have_.toNat ∧
      regs.put = inputAdvance l.put made ∧ regs.left.toNat + made = l.left.toNat ∧
      regs.bits.toNat < 8 ∧ regs.bits.toNat ≤ l.bits.toNat + 8 * used ∧
      regs.out_ = l.out_ ∧ state.window = s.window ∧
      regs.bits = state.bits ∧ regs.hold = state.hold ∧
      (state.mode = BAD ∨ state.mode = TYPE ∨ 0 < made) ∧
      dispatchRank regs state.mode < dispatchRank l s.mode := by
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
      Or.inr (Or.inr (Or.inr (Or.inr (invariant.data_format oldMode))))⟩
  have packet : DispatchBuffers heap r l bs :=
    buffers.byte_views invariant.good good rfl
      (byte_view_get_setI h zs current) (byte_view_ro_setI h zs current)
  have env : Env c heap r zs z current :=
    ⟨E.strm, E.st, good.live.hz, good.live.hs⟩
  obtain ⟨regs, after, zNext, sNext, used, made, bound, run, final, modes,
    finalPacket, sizes, next, count, put, left, small, budget, total,
    window, bitsEq, holdEq, progress, decreases⟩ :=
    inflate_LEN_fast_view_step env currentJ packet rfl fast
  have source : runX (inflate_LEN_ c) l h = runX (inflate_LEN c) l heap := by
    unfold inflate_LEN_
    rw [runX_bind, runX_setMode E]
  have prefixRank : dispatchRank l current.mode < dispatchRank l s.mode := by
    change dispatchRank l LEN < dispatchRank l s.mode
    rw [mode]
    unfold dispatchRank
    have credit : dispatchCredit LEN < dispatchCredit LEN_ := by decide
    omega
  exact ⟨regs, after, zNext, sNext, used, made, bound, source.trans run, final,
    modes, finalPacket, (byte_view_sizes_setI h zs current).trans sizes,
    next, count, put, left, small, budget, total, window, bitsEq, holdEq, progress,
    Nat.lt_trans decreases prefixRank⟩

#print axioms inflate_LEN_start_fast_view_step
end Zlib.Inflate.Proofs
