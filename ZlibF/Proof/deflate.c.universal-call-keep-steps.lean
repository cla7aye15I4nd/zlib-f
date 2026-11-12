import Lean
import ZlibF.Proof.«deflate.c.universal-call-keep-checksum»

/-!
# deflate.c: record updates and the step tactic of `KeepRel`

Owner 2 of the deflate split (`deflate_call`); port of `deflate.c.universal-params-steps` to the
relation `KeepRel` of `deflate.c.universal-call-keep-base`. `keep_wr`, `keep_md` and
`keep_stTreeDesc` cover the record updates; `keep_step` composes the primitives along the
translated code.
-/

namespace Zlib.Deflate.Universal.Keep
open C Zlib.Deflate Zlib.Deflate.Spec
set_option autoImplicit false

/-- `s->f = ...` (`trees.c`). -/
theorem keep_md (p : DeflateStatePtr) (f : DeflateState → DeflateState) (hf : ∀ d, (f d).gzhead = d.gzhead) :
    KeepM (Zlib.Trees.md p f) := by
  have same : Zlib.Trees.md p f = wr p f := by
    unfold Zlib.Trees.md wr
    rfl
  rw [same]
  exact keep_wr p f hf

theorem keep_ldTreeDesc (p : TreeDescPtr) : KeepM (ldTreeDesc p) := by
  intro h value after run
  unfold ldTreeDesc at run
  repeat' first | split at run | (cases run; exact KeepRel.refl h) | contradiction

theorem keep_ldStaticTreeDesc (p : StaticTreeDescPtr) : KeepM (ldStaticTreeDesc p) := by
  intro h value after run
  unfold ldStaticTreeDesc at run
  repeat' first | split at run | (cases run; exact KeepRel.refl h) | contradiction

theorem keep_stTreeDesc (p : TreeDescPtr) (v : TreeDesc) : KeepM (stTreeDesc p v) := by
  intro h value after run
  unfold stTreeDesc at run
  cases p with
  | none => cases run
  | some r =>
    cases r with
    | in_dstate_l_desc i =>
      cases get : h.dstates i with
      | none => simp [TreeDescRef.get, get] at run
      | some d =>
        simp only [TreeDescRef.get, get, Option.map_some, TreeDescRef.isRo] at run
        cases run
        simp only [TreeDescRef.put, get]
        exact KeepRel.upd_state get _ rfl
    | in_dstate_d_desc i =>
      cases get : h.dstates i with
      | none => simp [TreeDescRef.get, get] at run
      | some d =>
        simp only [TreeDescRef.get, get, Option.map_some, TreeDescRef.isRo] at run
        cases run
        simp only [TreeDescRef.put, get]
        exact KeepRel.upd_state get _ rfl
    | in_dstate_bl_desc i =>
      cases get : h.dstates i with
      | none => simp [TreeDescRef.get, get] at run
      | some d =>
        simp only [TreeDescRef.get, get, Option.map_some, TreeDescRef.isRo] at run
        cases run
        simp only [TreeDescRef.put, get]
        exact KeepRel.upd_state get _ rfl

theorem keep_cfor {σ : Type} (cond : σ → M Bool) (step body : σ → M σ)
    (hc : ∀ s, KeepM (cond s)) (hs : ∀ s, KeepM (step s))
    (hb : ∀ s, KeepM (body s)) (s : σ) : KeepM (Zlib.Trees.cfor cond step body s) := by
  unfold Zlib.Trees.cfor
  apply KeepM.cwhile
  · intro t
    exact KeepM.bind (hc t) (fun _ => KeepM.pure _)
  · intro t
    exact KeepM.bind (hb t) hs

/-- One step of `KeepM` along translated code: a primitive, a record update,
or a composition rule. -/
macro "keep_leaf" : tactic => `(tactic|
  first
    | with_reducible exact KeepM.pure _
    | exact KeepM.ub _
    | with_reducible exact keep_ldDeflateState _
    | with_reducible exact keep_castDeflateState _
    | with_reducible exact keep_ldZStream _
    | with_reducible exact keep_ldGzHeader _
    | with_reducible exact keep_ldTreeDesc _
    | with_reducible exact keep_ldStaticTreeDesc _
    | with_reducible exact keep_stTreeDesc _ _
    | with_reducible exact keep_strLitRef _
    | with_reducible exact keep_load8 _
    | with_reducible exact keep_index8 _ _
    | with_reducible exact keep_store8 _ _
    | with_reducible exact keep_memcpyB _ _ _
    | with_reducible exact keep_memsetB _ _ _
    | with_reducible exact keep_ptr_add _ _
    | with_reducible exact keep_ptr_load _
    | with_reducible exact keep_ptr_index _ _
    | with_reducible exact keep_ptr_store _ _
    | with_reducible exact keep_ptr_memcpy _ _ _
    | with_reducible exact keep_ptr_fill _ _ _
    | with_reducible exact keep_ptr_diff _ _
    | with_reducible exact keep_ptr_lt _ _
    | with_reducible exact keep_adler32 _ _ _
    | with_reducible exact keep_crc32 _ _ _
    | with_reducible exact keep_crc32_z _ _ _
    | with_reducible exact keep_wr _ _ (fun _ => rfl)
    | with_reducible exact keep_md _ _ (fun _ => rfl)
    | ((with_reducible apply keep_zwr) <;> intro _ <;> exact ⟨rfl, rfl, rfl⟩))

/-- One step of `KeepM` along translated code: a primitive, a record update,
or a composition rule. -/
macro "keep_step" : tactic => `(tactic|
  first
    | keep_leaf
    | with_reducible apply keep_cfor
    | with_reducible apply KeepM.cwhile
    | with_reducible apply KeepM.cdoWhile
    | with_reducible apply KeepM.ite
    | with_reducible apply KeepM.bind
    | with_reducible intro _
    | dsimp only)

/-- Keep the translated do-notation join points: one proof per shared suffix. -/
elab "keep_join" : tactic =>
  Lean.Elab.Tactic.liftMetaTactic fun goal => goal.withContext do
    let target ← Lean.instantiateMVars (← goal.getType)
    unless target.isAppOf ``Zlib.Deflate.Universal.Keep.KeepM do
      throwError "Expected a stability goal"
    let computation := target.getAppArgs.back!
    match computation with
    | .letE name type value body _ =>
      if type.getForallBody.isAppOf ``C.M then
        Lean.Meta.withLetDecl name type value fun suffix => do
          let stableType ← Lean.Meta.forallBoundedTelescope type (some type.getNumHeadForalls) fun xs _ => do
            let prop ← Lean.Meta.mkAppM ``Zlib.Deflate.Universal.Keep.KeepM #[Lean.mkAppN suffix xs]
            Lean.Meta.mkForallFVars xs prop
          let proof ← Lean.Meta.mkFreshExprSyntheticOpaqueMVar stableType
          let proofName ← Lean.mkFreshUserName `suffix_exact
          Lean.Meta.withLetDecl proofName stableType proof fun receipt => do
            let nextType ← Lean.Meta.mkAppM ``Zlib.Deflate.Universal.Keep.KeepM #[body.instantiate1 suffix]
            let next ← Lean.Meta.mkFreshExprSyntheticOpaqueMVar nextType
            let result ← Lean.Meta.mkLetFVars #[suffix, receipt] next
              (usedLetOnly := false) (generalizeNondepLet := false)
            goal.assign result
            return [proof.mvarId!, next.mvarId!]
      else
        let nextType ← Lean.Meta.mkAppM ``Zlib.Deflate.Universal.Keep.KeepM #[body.instantiate1 value]
        let next ← Lean.Meta.mkFreshExprSyntheticOpaqueMVar nextType
        goal.assign next
        return [next.mvarId!]
    | _ =>
      let head := computation.getAppFn
      unless head.isFVar do throwError "No local join point"
      for decl in (← Lean.getLCtx) do
        let result := decl.type.getForallBody
        if result.isAppOf ``Zlib.Deflate.Universal.Keep.KeepM then
          let observed := result.getAppArgs.back!
          if observed.getAppFn == head then
            return ← goal.apply (Lean.mkAppN decl.toExpr computation.getAppArgs)
      let decl := (← Lean.getLCtx).get! head.fvarId!
      match decl.value? with
      | none => throwError "The local computation has no proved stability fact"
      | some value =>
        let expanded := (Lean.mkAppN value computation.getAppArgs).headBeta
        let nextType ← Lean.Meta.mkAppM ``Zlib.Deflate.Universal.Keep.KeepM #[expanded]
        let next ← Lean.Meta.mkFreshExprSyntheticOpaqueMVar nextType
        goal.assign next
        return [next.mvarId!]


macro "keep_steps" : tactic => `(tactic| repeat' keep_step)

end Zlib.Deflate.Universal.Keep
