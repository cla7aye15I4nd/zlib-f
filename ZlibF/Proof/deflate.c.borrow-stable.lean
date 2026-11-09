import ZlibF.Proof.«deflate.c.borrow-stable-strategies»
import ZlibF.Proof.«deflate.c.borrow-stable-lifecycle»

/-!
# Actual public deflate calls preserve the libc borrow observation

Every actual callee has its own unconditional preservation proof. This is an
internal execution receipt for string-view transport, not a public buffer
precondition or a replacement for the safety and correctness contract.
-/

namespace Zlib.Deflate.BorrowProofs
open C C.LibcBorrow Zlib.Deflate
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 200000

/-- Retain the translated do-notation join points. Each shared suffix gets
one locally proved stability fact, derived from that suffix's actual body. -/
elab "public_borrow_join" : tactic =>
  Lean.Elab.Tactic.liftMetaTactic fun goal => goal.withContext do
    let target ← Lean.instantiateMVars (← goal.getType)
    unless target.isAppOf ``C.LibcBorrow.StableM do
      throwError "Expected a stability goal"
    let computation := target.getAppArgs.back!
    match computation with
    | .letE name type value body _ =>
      if type.getForallBody.isAppOf ``C.M then
        Lean.Meta.withLetDecl name type value fun suffix => do
          let stableType ← Lean.Meta.forallBoundedTelescope type (some type.getNumHeadForalls) fun xs _ => do
            let prop ← Lean.Meta.mkAppM ``C.LibcBorrow.StableM #[Lean.mkAppN suffix xs]
            Lean.Meta.mkForallFVars xs prop
          let proof ← Lean.Meta.mkFreshExprSyntheticOpaqueMVar stableType
          let proofName ← Lean.mkFreshUserName `suffix_borrow
          Lean.Meta.withLetDecl proofName stableType proof fun receipt => do
            let nextType ← Lean.Meta.mkAppM ``C.LibcBorrow.StableM #[body.instantiate1 suffix]
            let next ← Lean.Meta.mkFreshExprSyntheticOpaqueMVar nextType
            let result ← Lean.Meta.mkLetFVars #[suffix, receipt] next
              (usedLetOnly := false) (generalizeNondepLet := false)
            goal.assign result
            return [proof.mvarId!, next.mvarId!]
      else
        let nextType ← Lean.Meta.mkAppM ``C.LibcBorrow.StableM #[body.instantiate1 value]
        let next ← Lean.Meta.mkFreshExprSyntheticOpaqueMVar nextType
        goal.assign next
        return [next.mvarId!]
    | _ =>
      let head := computation.getAppFn
      unless head.isFVar do throwError "No local join point"
      for decl in (← Lean.getLCtx) do
        let result := decl.type.getForallBody
        if result.isAppOf ``C.LibcBorrow.StableM then
          let observed := result.getAppArgs.back!
          if observed.getAppFn == head then
            return ← goal.apply (Lean.mkAppN decl.toExpr computation.getAppArgs)
      let decl := (← Lean.getLCtx).get! head.fvarId!
      match decl.value? with
      | none => throwError "The local computation has no proved stability fact"
      | some value =>
        let expanded := (Lean.mkAppN value computation.getAppArgs).headBeta
        let nextType ← Lean.Meta.mkAppM ``C.LibcBorrow.StableM #[expanded]
        let next ← Lean.Meta.mkFreshExprSyntheticOpaqueMVar nextType
        goal.assign next
        return [next.mvarId!]

/-- Match the computation head before applying its proved callee theorem.
The resulting proof still consists solely of kernel-checked composition. -/
elab "public_borrow_head" : tactic => do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let target ← Lean.instantiateMVars (← goal.getType)
  let mut found := false
  if target.isAppOf ``C.LibcBorrow.StableM then
    let head := target.getAppArgs.back!.getAppFn.constName?
    let candidates : List Lean.Name := [
      ``stable_deflateStateCheck,
      ``stable_ERR_RETURN,
      ``stable_RANK,
      ``stable_putShortMSB,
      ``stable_put_byte,
      ``stable_ldGzHeader,
      ``stable_HCRC_UPDATE,
      ``stable_gz_string_loop,
      ``stable_deflate_stored,
      ``stable_deflate_fast,
      ``stable_deflate_slow,
      ``stable_deflate_rle,
      ``stable_deflate_huff,
      ``stable_config_at,
      ``stable_crc32_z,
      ``stable_ineg,
      ``Zlib.Trees.BorrowProofs.stable__tr_align]
    for name in candidates do
      let info ← Lean.getConstInfo name
      let result := info.type.getForallBody
      if result.isAppOf ``C.LibcBorrow.StableM then
        let actual := result.getAppArgs.back!
        if actual.getAppFn.constName? == head then
          Lean.Elab.Tactic.evalTactic (← `(tactic| apply $(Lean.mkIdent name)))
          found := true
          break
  unless found do
    Lean.Elab.Tactic.evalTactic (← `(tactic| strategy_borrow_step))

set_option maxHeartbeats 1000000 in
theorem stable_deflate (p : ZStreamPtr) (flush : Int32) : StableM (deflate p flush) := by
  unfold deflate
  repeat' first | public_borrow_join | public_borrow_head

/-- The view receipt is obtained from this very actual returned run. No
caller promise about a persistent literal or a volatile borrow is needed. -/
theorem deflate_run_borrow_stable {h after : Heap} {p : ZStreamPtr} {flush rc : Int32}
    (run : deflate p flush h = .ok (rc, after)) (ref : BRef) : BorrowStable h after ref :=
  StableM.view (stable_deflate p flush) run ref

/-- Source literals and volatile errno-text views both keep their current
bytes during an actual deflate call. Arbitrary caller edits are not covered. -/
theorem deflate_run_string_get {h after : Heap} {p : ZStreamPtr} {flush rc : Int32}
    (run : deflate p flush h = .ok (rc, after)) (i : Nat) :
    Space.get after (BRef.str i) = Space.get h (BRef.str i) :=
  str_view_stable (deflate_run_borrow_stable run (.str i))

end Zlib.Deflate.BorrowProofs
