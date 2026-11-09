import ZlibF.Proof.«inflate.c.local-ret-construction-entry»
import ZlibF.Proof.«inflate.c.ret-construction»

namespace Zlib.Inflate.Local
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

theorem inflate_LENLENS_ret_step
    {c : Ctx} {h after : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s returned : InflateState} {l regs : IL} {bs : List UInt8}
    {outcome : Except Ex Unit}
    (E : Env c h r zs z s) (invariant : LocalStateJ h cutoff r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = LENLENS) (initial : l.ret = Z_OK)
    (run : runX (inflate_LENLENS c) l h = .ok ((outcome, regs), after))
    (get : after.istates zs = some returned) :
    regs.ret = Z_OK ∨ (outcome = .ok () ∧ returned.mode = BAD) := by
  obtain ⟨first, heap0, stream0, state0, used0, _, nextJ, _, packet0, _, _, _, _, _, _, _, _, parts⟩ :=
    inflate_LENLENS_ret_entry E invariant buffers mode initial
  rcases parts with stopped | continued
  · obtain ⟨decision, source, why⟩ := stopped
    rcases why with ⟨_, ret⟩ | ⟨normal, bad⟩
    · exact Or.inl ((congrArg IL.ret (xrun_regs_eq source run)).symm.trans ret)
    · have sameMode := xrun_state_eq source run nextJ.good.live.hs get
      exact Or.inr ⟨(xrun_outcome_eq source run).symm.trans normal,
        by rw [← sameMode]; exact bad⟩
  · obtain ⟨nextMode, ret, source⟩ := continued
    have nextEnv : Env c heap0 r zs stream0 state0 :=
      ⟨E.strm, E.st, nextJ.good.live.hz, nextJ.good.live.hs⟩
    exact inflate_CODELENS_ret_step nextEnv nextJ packet0 nextMode ret (source.symm.trans run) get

theorem inflate_TABLE_ret_step
    {c : Ctx} {h after : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s returned : InflateState} {l regs : IL} {bs : List UInt8}
    {outcome : Except Ex Unit}
    (E : Env c h r zs z s) (invariant : LocalStateJ h cutoff r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = TABLE) (initial : l.ret = Z_OK)
    (run : runX (inflate_TABLE c) l h = .ok ((outcome, regs), after))
    (get : after.istates zs = some returned) :
    regs.ret = Z_OK ∨ (outcome = .ok () ∧ returned.mode = BAD) := by
  obtain ⟨first, heap0, stream0, state0, used0, _, nextJ, _, packet0, _, _, _, _, _, _, _, _, saved, parts⟩ :=
    inflate_TABLE_ret_entry E invariant buffers mode
  rcases parts with stopped | continued
  · obtain ⟨decision, source, why⟩ := stopped
    rcases why with leaves | ⟨normal, bad⟩
    · exact Or.inl ((congrArg IL.ret (xrun_regs_eq source run)).symm.trans (saved.trans initial))
    · have sameMode := xrun_state_eq source run nextJ.good.live.hs get
      exact Or.inr ⟨(xrun_outcome_eq source run).symm.trans normal,
        by rw [← sameMode]; exact bad⟩
  · obtain ⟨nextMode, source⟩ := continued
    have nextEnv : Env c heap0 r zs stream0 state0 :=
      ⟨E.strm, E.st, nextJ.good.live.hz, nextJ.good.live.hs⟩
    exact inflate_LENLENS_ret_step nextEnv nextJ packet0 nextMode (saved.trans initial)
      (source.symm.trans run) get

/-- The actual construction chain can expose a non-OK table result only
on a continuing BAD state. It cannot leave with that internal error code. -/
theorem inflate_dispatch_ret_construction
    {c : Ctx} {h after : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s returned : InflateState} {l regs : IL} {bs : List UInt8}
    {outcome : Except Ex Unit}
    (E : Env c h r zs z s) (invariant : LocalStateJ h cutoff r zs z s)
    (buffers : DispatchBuffers h r l bs)
    (mode : s.mode = TABLE ∨ s.mode = LENLENS ∨ s.mode = CODELENS) (initial : l.ret = Z_OK)
    (run : runX (inflate_dispatch c) l h = .ok ((outcome, regs), after))
    (get : after.istates zs = some returned) :
    regs.ret = Z_OK ∨ (outcome = .ok () ∧ returned.mode = BAD) := by
  rcases mode with table | lengths | codes
  · exact inflate_TABLE_ret_step E invariant buffers table initial
      ((inflate_dispatch_TABLE E l table).symm.trans run) get
  · exact inflate_LENLENS_ret_step E invariant buffers lengths initial
      ((inflate_dispatch_LENLENS E l lengths).symm.trans run) get
  · exact inflate_CODELENS_ret_step E invariant buffers codes initial
      ((inflate_dispatch_CODELENS E l codes).symm.trans run) get

#print axioms inflate_dispatch_ret_construction
end Zlib.Inflate.Local
