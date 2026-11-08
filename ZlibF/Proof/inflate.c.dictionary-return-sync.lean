import ZlibF.Proof.«inflate.c.exit-post»
import ZlibF.Proof.«inflate.c.dictionary-dispatch»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The public cursor bindings agree with the returning mode registers. -/
def StreamRegsSync (r : ZStreamRef) (l : IL) (h : Heap) : Prop :=
  ∃ z, r.get h = some z ∧ z.next_in = l.next ∧ z.avail_in = l.have_ ∧
    z.next_out = l.put ∧ z.avail_out = l.left

def NeedDictPost (r : ZStreamRef) (exit : Ex) (l : IL) (h : Heap) : Prop :=
  exit = .ret Z_NEED_DICT → StreamRegsSync r l h

abbrev NeedDictSyncX {α : Type} (r : ZStreamRef) (program : X α) : Prop :=
  ExitPostX (NeedDictPost r) program

/-- Literal source branch of DICT after the missing-dictionary test. -/
def inflateDictRequest (c : Ctx) : X Unit := do
  RESTORE c.strm c.st
  let l ← get
  wrZ c.strm fun z => { z with total_in := z.total_in + (l.in_ - z.avail_in).toUInt64 }
  throw (Ex.ret Z_NEED_DICT)

/-- Execute the literal request branch, including its early input credit. -/
theorem inflateDictRequest_run {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (E : Env c h r zs z s) (l : IL) :
    runX (inflateDictRequest c) l h = .ok ((.error (Ex.ret Z_NEED_DICT), l),
      setI (r.put h (dictWaitStream z l)) zs (leaveState s l)) := by
  have restored : Env c (setI (r.put h (leaveStream z l)) zs (leaveState s l)) r zs
      (leaveStream z l) (leaveState s l) :=
    ⟨E.strm, E.st, by rw [ZStreamRef.get_setI]; exact ZStreamRef.get_put_same E.hz _, by simp⟩
  unfold inflateDictRequest
  rw [runX_bind, RESTORE_pending_run E]
  simp only []
  rw [runX_bind, runX_get]
  simp only []
  have write : wrZ c.strm (fun stream => { stream with total_in := stream.total_in + (l.in_ - stream.avail_in).toUInt64 })
      (setI (r.put h (leaveStream z l)) zs (leaveState s l)) =
      .ok ((), setI (r.put h (dictWaitStream z l)) zs (leaveState s l)) := by
    simp only [E.strm, wrZ_eq, restored.hz, ZStreamRef.put_setI, ZStreamRef.put_put]
    rfl
  rw [runX_bind, runX_lift_ok write]
  rfl


/-- Every successful direct request has the actual RESTORE bindings. No
state invariant, input restriction or callee contract is assumed here. -/
theorem needDictSyncX_request (r : ZStreamRef) (zs : Nat) (c : Ctx)
    (root : c.strm = some r) (state : c.st = some (.tab zs)) : NeedDictSyncX r (inflateDictRequest c) := by
  intro l h outcome regs after run exit equal wanted
  cases get : r.get h with
  | none =>
    simp only [inflateDictRequest, RESTORE, runX_bind, runX_get, runX_lift,
      root, wrZ_eq, get] at run
    cases run
  | some z =>
    cases hs : h.istates zs with
    | none =>
      simp only [inflateDictRequest, RESTORE, runX_bind, runX_get, runX_lift,
        root, state, wrZ_eq, get, wrI_eq, ZStreamRef.put_istates, hs] at run
      cases run
    | some s =>
      have E : Env c h r zs z s := ⟨root, state, get, hs⟩
      rw [inflateDictRequest_run E] at run
      cases run
      refine ⟨dictWaitStream z l, ?_, rfl, rfl, rfl, rfl⟩
      rw [ZStreamRef.get_setI]
      exact ZStreamRef.get_put_same get _

/-- Control exits other than NEED_DICT have no dictionary binding obligation. -/
theorem needDictSyncX_leave {α : Type} (r : ZStreamRef) :
    NeedDictSyncX r (throw Ex.leave : X α) := by
  apply exitPostX_throw
  intro l h impossible
  cases impossible

theorem needDictSyncX_ret_other {α : Type} (r : ZStreamRef) (code : Int32)
    (different : code ≠ Z_NEED_DICT) : NeedDictSyncX r (throw (.ret code) : X α) := by
  apply exitPostX_throw
  intro l h same
  exact False.elim (different (Ex.ret.inj same))

/-- Compose the actual mode syntax while preserving a proved final-heap
property of dictionary returns. Lifted C operations cannot create X exits. -/
macro "need_dict_sync_mode" r:term : tactic =>
  `(tactic| repeat' first
    | with_reducible assumption
    | with_reducible exact exitPostX_pure _
    | with_reducible exact exitPostX_get
    | with_reducible exact exitPostX_set _
    | with_reducible exact exitPostX_modify _
    | with_reducible exact exitPostX_lift _
    | with_reducible exact needDictSyncX_leave $r
    | with_reducible exact needDictSyncX_ret_other $r _ (by decide)
    | with_reducible apply exitPostX_xdoWhile
    | with_reducible apply exitPostX_xwhile
    | with_reducible apply exitPostX_xwhileBrk
    | with_reducible apply exitPostX_xloopBrk
    | with_reducible apply exitPostX_ite
    | with_reducible refine exitPostX_bind ?_ (fun _ => ?_)
    | split)

#print axioms needDictSyncX_request
end Zlib.Inflate.Proofs
