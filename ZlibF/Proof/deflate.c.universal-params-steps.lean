import Lean
import ZlibF.Proof.«deflate.c.universal-params-checksum»

/-!
# deflate.c: record updates and the step tactic of the parameter frame

Batch C of the deflate skeleton. `exact_wr`, `exact_md` and `exact_stTreeDesc` cover the record
updates that change no parameter; `exact_step` composes the primitives along the translated code.
-/

namespace Zlib.Deflate.Universal.Params
open C Zlib.Deflate Zlib.Deflate.Spec
set_option autoImplicit false

/-- Replacing a record by one with the same parameters. -/
theorem ExactRel.upd_state {h : Heap} {i : Nat} {d : DeflateState} (get : h.dstates i = some d)
    (d' : DeflateState) (eq : Pars d' = Pars d) :
    ExactRel h { h with dstates := upd h.dstates i (some d') } := by
  refine ⟨fun ds e got => ?_, fun q z got => ⟨z, ?_, ZSame.refl z⟩⟩
  · by_cases same : ds = i
    · subst same
      have eq' : e = d := Option.some.inj (got.symm.trans get)
      rw [eq']
      exact ⟨d', by simp, eq⟩
    · exact ⟨e, by simpa [upd_ne _ _ _ _ same] using got, rfl⟩
  · cases q <;> simpa only [ZStreamRef.get] using got

/-- `s->f = ...` (`deflate.c`), when `f` keeps every parameter. -/
theorem exact_wr (p : DeflateStatePtr) (f : DeflateState → DeflateState)
    (hf : ∀ d, Pars (f d) = Pars d) : ExactM (wr p f) := by
  intro h value after run
  unfold wr at run
  rw [bind_app] at run
  cases p with
  | none => cases run
  | some r =>
    cases r with
    | tab i =>
      cases get : h.dstates i with
      | none => simp [ldDeflateState, DeflateStateRef.get, get] at run
      | some d =>
        simp only [ldDeflateState, DeflateStateRef.get, get, stDeflateState, DeflateStateRef.isRo] at run
        cases run
        rw [DeflateStateRef.put_tab get]
        exact ExactRel.upd_state get (f d) (hf d)

/-- `s->f = ...` (`trees.c`), when `f` keeps every parameter. -/
theorem exact_md (p : DeflateStatePtr) (f : DeflateState → DeflateState)
    (hf : ∀ d, Pars (f d) = Pars d) : ExactM (Zlib.Trees.md p f) := by
  have same : Zlib.Trees.md p f = wr p f := by
    unfold Zlib.Trees.md wr
    rfl
  rw [same]
  exact exact_wr p f hf

theorem exact_ldTreeDesc (p : TreeDescPtr) : ExactM (ldTreeDesc p) := by
  intro h value after run
  unfold ldTreeDesc at run
  repeat' first | split at run | (cases run; exact ExactRel.refl h) | contradiction

theorem exact_ldStaticTreeDesc (p : StaticTreeDescPtr) : ExactM (ldStaticTreeDesc p) := by
  intro h value after run
  unfold ldStaticTreeDesc at run
  repeat' first | split at run | (cases run; exact ExactRel.refl h) | contradiction

theorem exact_stTreeDesc (p : TreeDescPtr) (v : TreeDesc) : ExactM (stTreeDesc p v) := by
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
        exact ExactRel.upd_state get _ rfl
    | in_dstate_d_desc i =>
      cases get : h.dstates i with
      | none => simp [TreeDescRef.get, get] at run
      | some d =>
        simp only [TreeDescRef.get, get, Option.map_some, TreeDescRef.isRo] at run
        cases run
        simp only [TreeDescRef.put, get]
        exact ExactRel.upd_state get _ rfl
    | in_dstate_bl_desc i =>
      cases get : h.dstates i with
      | none => simp [TreeDescRef.get, get] at run
      | some d =>
        simp only [TreeDescRef.get, get, Option.map_some, TreeDescRef.isRo] at run
        cases run
        simp only [TreeDescRef.put, get]
        exact ExactRel.upd_state get _ rfl

theorem exact_cfor {σ : Type} (cond : σ → M Bool) (step body : σ → M σ)
    (hc : ∀ s, ExactM (cond s)) (hs : ∀ s, ExactM (step s))
    (hb : ∀ s, ExactM (body s)) (s : σ) : ExactM (Zlib.Trees.cfor cond step body s) := by
  unfold Zlib.Trees.cfor
  apply ExactM.cwhile
  · intro t
    exact ExactM.bind (hc t) (fun _ => ExactM.pure _)
  · intro t
    exact ExactM.bind (hb t) hs

/-- One step of the parameter frame along translated code: a primitive, a record update that
keeps every parameter (`rfl`), or a composition rule. -/
macro "exact_leaf" : tactic => `(tactic|
  first
    | with_reducible exact ExactM.pure _
    | exact ExactM.ub _
    | with_reducible exact exact_ldDeflateState _
    | with_reducible exact exact_castDeflateState _
    | with_reducible exact exact_ldZStream _
    | with_reducible exact exact_ldGzHeader _
    | with_reducible exact exact_ldTreeDesc _
    | with_reducible exact exact_ldStaticTreeDesc _
    | with_reducible exact exact_stTreeDesc _ _
    | with_reducible exact exact_strLitRef _
    | with_reducible exact exact_load8 _
    | with_reducible exact exact_index8 _ _
    | with_reducible exact exact_store8 _ _
    | with_reducible exact exact_memcpyB _ _ _
    | with_reducible exact exact_memsetB _ _ _
    | with_reducible exact exact_ptr_add _ _
    | with_reducible exact exact_ptr_load _
    | with_reducible exact exact_ptr_index _ _
    | with_reducible exact exact_ptr_store _ _
    | with_reducible exact exact_ptr_memcpy _ _ _
    | with_reducible exact exact_ptr_fill _ _ _
    | with_reducible exact exact_ptr_diff _ _
    | with_reducible exact exact_ptr_lt _ _
    | with_reducible exact exact_adler32 _ _ _
    | with_reducible exact exact_crc32 _ _ _
    | with_reducible exact exact_crc32_z _ _ _
    | ((with_reducible apply exact_wr) <;> intro _ <;> (simp only [Pars]; done))
    | ((with_reducible apply exact_md) <;> intro _ <;> (simp only [Pars]; done))
    | ((with_reducible apply exact_zwr) <;> intro _ <;> exact ⟨rfl, rfl, rfl⟩))

/-- One step of the parameter frame along translated code: a primitive, a record update that
keeps every parameter, or a composition rule. -/
macro "exact_step" : tactic => `(tactic|
  first
    | exact_leaf
    | with_reducible apply exact_cfor
    | with_reducible apply ExactM.cwhile
    | with_reducible apply ExactM.cdoWhile
    | with_reducible apply ExactM.ite
    | with_reducible apply ExactM.bind
    | with_reducible intro _
    | dsimp only)

/-- Keep the translated do-notation join points: one proof per shared suffix. -/
elab "exact_join" : tactic =>
  Lean.Elab.Tactic.liftMetaTactic fun goal => goal.withContext do
    let target ← Lean.instantiateMVars (← goal.getType)
    unless target.isAppOf ``Zlib.Deflate.Universal.Params.ExactM do
      throwError "Expected a stability goal"
    let computation := target.getAppArgs.back!
    match computation with
    | .letE name type value body _ =>
      if type.getForallBody.isAppOf ``C.M then
        Lean.Meta.withLetDecl name type value fun suffix => do
          let stableType ← Lean.Meta.forallBoundedTelescope type (some type.getNumHeadForalls) fun xs _ => do
            let prop ← Lean.Meta.mkAppM ``Zlib.Deflate.Universal.Params.ExactM #[Lean.mkAppN suffix xs]
            Lean.Meta.mkForallFVars xs prop
          let proof ← Lean.Meta.mkFreshExprSyntheticOpaqueMVar stableType
          let proofName ← Lean.mkFreshUserName `suffix_exact
          Lean.Meta.withLetDecl proofName stableType proof fun receipt => do
            let nextType ← Lean.Meta.mkAppM ``Zlib.Deflate.Universal.Params.ExactM #[body.instantiate1 suffix]
            let next ← Lean.Meta.mkFreshExprSyntheticOpaqueMVar nextType
            let result ← Lean.Meta.mkLetFVars #[suffix, receipt] next
              (usedLetOnly := false) (generalizeNondepLet := false)
            goal.assign result
            return [proof.mvarId!, next.mvarId!]
      else
        let nextType ← Lean.Meta.mkAppM ``Zlib.Deflate.Universal.Params.ExactM #[body.instantiate1 value]
        let next ← Lean.Meta.mkFreshExprSyntheticOpaqueMVar nextType
        goal.assign next
        return [next.mvarId!]
    | _ =>
      let head := computation.getAppFn
      unless head.isFVar do throwError "No local join point"
      for decl in (← Lean.getLCtx) do
        let result := decl.type.getForallBody
        if result.isAppOf ``Zlib.Deflate.Universal.Params.ExactM then
          let observed := result.getAppArgs.back!
          if observed.getAppFn == head then
            return ← goal.apply (Lean.mkAppN decl.toExpr computation.getAppArgs)
      let decl := (← Lean.getLCtx).get! head.fvarId!
      match decl.value? with
      | none => throwError "The local computation has no proved stability fact"
      | some value =>
        let expanded := (Lean.mkAppN value computation.getAppArgs).headBeta
        let nextType ← Lean.Meta.mkAppM ``Zlib.Deflate.Universal.Params.ExactM #[expanded]
        let next ← Lean.Meta.mkFreshExprSyntheticOpaqueMVar nextType
        goal.assign next
        return [next.mvarId!]


macro "exact_steps" : tactic => `(tactic| repeat' exact_step)

end Zlib.Deflate.Universal.Params
