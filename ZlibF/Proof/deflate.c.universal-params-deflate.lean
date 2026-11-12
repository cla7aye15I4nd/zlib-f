import Lean
import ZlibF.Proof.«deflate.c.universal-params-strategies»

/-!
# deflate.c: `deflate` keeps the parameters of every deflate state and stream

Batch C of the deflate skeleton (`bound_before_output`). `deflate` writes `status` (always one of
the states `deflateStateCheck` accepts), `last_flush`, the header progress fields and, after the
trailer, `wrap := -wrap`. It keeps `level`, `w_bits`, `hash_bits`, `gzhead`, `strm` and `|wrap|`
of every state record and `state`, `zalloc`, `zfree` of every stream record (`ParM true`).
-/

namespace Zlib.Deflate.Universal.Params
open C Zlib.Deflate Zlib.Deflate.Spec
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

theorem exact_deflateStateCheck (p : ZStreamPtr) : ExactM (deflateStateCheck p) := by
  unfold deflateStateCheck; x_steps

theorem exact_zError (err : Int32) : ExactM (Zlib.Zutil.zError err) := by
  unfold Zlib.Zutil.zError Zlib.Zutil.strLit
  dsimp only
  split
  · exact exact_strLitRef _
  · exact ExactM.ub _

theorem exact_ERR_MSG (err : Int32) : ExactM (ERR_MSG err) := exact_zError err

theorem exact_ERR_RETURN (p : ZStreamPtr) (err : Int32) : ExactM (ERR_RETURN p err) := by
  unfold ERR_RETURN
  repeat' first | exact exact_ERR_MSG _ | x_step

theorem exact_RANK (flush : Int32) : ExactM (RANK flush) := by
  unfold RANK
  exact ExactM.bind (exact_chk32 _) (fun _ => exact_isub _ _)

theorem exact_HCRC_UPDATE (p : ZStreamPtr) (s : DeflateStatePtr) (beg : UInt64) :
    ExactM (HCRC_UPDATE p s beg) := by
  unfold HCRC_UPDATE; x_steps


/-- The last statements of `deflate`, as in the source: `if (s->wrap > 0) s->wrap = -s->wrap;` and
the return. -/
def trailerTail (s : DeflateStatePtr) : M Int32 := do
  let w ← rd s (·.wrap)
  if w > 0 then
    let nw ← ineg w
    wr s (fun d => { d with wrap := nw })
  return if (← rd s (·.pending)) != 0 then Z_OK else Z_STREAM_END

/-- The negation keeps `|wrap|`: it is applied to the value just read. -/
theorem par_trailerTail_def (s : DeflateStatePtr) : ParM true (trailerTail s) := by
  intro h value after run
  unfold trailerTail at run
  simp only [bind_app] at run
  cases s with
  | none => simp [rd, ldDeflateState] at run
  | some r =>
    cases r with
    | tab i =>
      cases get : h.dstates i with
      | none => simp [rd, ldDeflateState, DeflateStateRef.get, get] at run
      | some d =>
        simp only [rd, ldDeflateState, DeflateStateRef.get, get, bind_app, pure_app] at run
        by_cases pos : d.wrap > 0
        · simp only [pos, ite_true, bind_app] at run
          unfold ineg chk32 at run
          by_cases range : -2147483648 ≤ -d.wrap.toInt ∧ -d.wrap.toInt ≤ 2147483647
          · simp only [range, and_self, ite_true, pure_app] at run
            simp only [wr, bind_app, ldDeflateState, DeflateStateRef.get, get, stDeflateState,
              DeflateStateRef.isRo, Bool.false_eq_true, ite_false] at run
            rw [DeflateStateRef.put_tab get] at run
            simp only [pure_app, upd_same, DeflateStateRef.get] at run
            cases run
            refine ⟨fun ds e got => ?_, fun q z got => ⟨z, ?_, ZSame.refl z⟩⟩
            · by_cases same : ds = i
              · subst same
                have eq : e = d := Option.some.inj (got.symm.trans get)
                rw [eq]
                refine ⟨{ d with wrap := Int32.ofInt (-d.wrap.toInt) }, by simp, rfl, rfl, rfl, rfl, rfl,
                  fun _ => ?_, id⟩
                change (Int32.ofInt (-d.wrap.toInt)).toInt.natAbs = d.wrap.toInt.natAbs
                rw [Int32.toInt_ofInt_of_le range.1 (by have := range.2; omega)]
                omega
              · exact ⟨e, by simpa [upd_ne _ _ _ _ same] using got, Same.refl true e⟩
            · cases q <;> simpa only [ZStreamRef.get] using got
          · simp only [range, ite_false] at run
            cases run
        · simp only [pos, ite_false, bind_app, ldDeflateState, DeflateStateRef.get, get, pure_app] at run
          cases run
          exact ParRel.refl true h

/-- The same, stated on the inline code so that it matches the end of `deflate` syntactically. -/
theorem par_trailerTail (s : DeflateStatePtr) : ParM true (do
    let w ← rd s (·.wrap)
    if w > 0 then
      let nw ← ineg w
      wr s (fun d => { d with wrap := nw })
    return if (← rd s (·.pending)) != 0 then Z_OK else Z_STREAM_END) :=
  par_trailerTail_def s

/-- The status values `deflate` writes. -/
macro "same_tac" : tactic => `(tactic|
  first
    | (apply Same.of_pars; simp only [Pars]; done)
    | (refine ⟨rfl, rfl, rfl, rfl, rfl, fun _ => rfl, fun _ => ?_⟩; simp only [GoodStatus]; decide)
    | exact ⟨rfl, rfl, rfl, rfl, rfl, fun _ => rfl, id⟩)

/-- The callees of `deflate` that keep every parameter exactly. -/
macro "deflate_exact" : tactic => `(tactic|
  first
    | with_reducible exact exact_deflateStateCheck _
    | with_reducible exact exact_ERR_RETURN _ _
    | with_reducible exact exact_RANK _
    | with_reducible exact exact_HCRC_UPDATE _ _ _
    | with_reducible exact exact_flush_pending _
    | with_reducible exact exact_putShortMSB _ _
    | with_reducible exact exact_put_byte _ _
    | with_reducible exact exact_deflate_stored _ _
    | with_reducible exact exact_deflate_fast _ _
    | with_reducible exact exact_deflate_slow _ _
    | with_reducible exact exact_deflate_rle _ _
    | with_reducible exact exact_deflate_huff _ _
    | with_reducible exact exact_CLEAR_HASH _
    | with_reducible exact Zlib.Trees.ParamsProofs.exact__tr_align _
    | with_reducible exact Zlib.Trees.ParamsProofs.exact__tr_stored_block _ _ _ _
    | with_reducible exact Zlib.Trees.ParamsProofs.exact__tr_flush_bits _)

/-- Keep the translated do-notation join points: one proof per shared suffix. -/
elab "par_join" : tactic =>
  Lean.Elab.Tactic.liftMetaTactic fun goal => goal.withContext do
    let target ← Lean.instantiateMVars (← goal.getType)
    unless target.isAppOf ``Zlib.Deflate.Universal.Params.ParM do
      throwError "Expected a stability goal"
    let computation := target.getAppArgs.back!
    let keepArg := target.getAppArgs[1]!
    match computation with
    | .letE name type value body _ =>
      if type.getForallBody.isAppOf ``C.M then
        Lean.Meta.withLetDecl name type value fun suffix => do
          let stableType ← Lean.Meta.forallBoundedTelescope type (some type.getNumHeadForalls) fun xs _ => do
            let prop ← Lean.Meta.mkAppM ``Zlib.Deflate.Universal.Params.ParM #[keepArg, Lean.mkAppN suffix xs]
            Lean.Meta.mkForallFVars xs prop
          let proof ← Lean.Meta.mkFreshExprSyntheticOpaqueMVar stableType
          let proofName ← Lean.mkFreshUserName `suffix_par
          Lean.Meta.withLetDecl proofName stableType proof fun receipt => do
            let nextType ← Lean.Meta.mkAppM ``Zlib.Deflate.Universal.Params.ParM #[keepArg, body.instantiate1 suffix]
            let next ← Lean.Meta.mkFreshExprSyntheticOpaqueMVar nextType
            let result ← Lean.Meta.mkLetFVars #[suffix, receipt] next
              (usedLetOnly := false) (generalizeNondepLet := false)
            goal.assign result
            return [proof.mvarId!, next.mvarId!]
      else
        let nextType ← Lean.Meta.mkAppM ``Zlib.Deflate.Universal.Params.ParM #[keepArg, body.instantiate1 value]
        let next ← Lean.Meta.mkFreshExprSyntheticOpaqueMVar nextType
        goal.assign next
        return [next.mvarId!]
    | _ =>
      let head := computation.getAppFn
      unless head.isFVar do throwError "No local join point"
      for decl in (← Lean.getLCtx) do
        let result := decl.type.getForallBody
        if result.isAppOf ``Zlib.Deflate.Universal.Params.ParM then
          let observed := result.getAppArgs.back!
          if observed.getAppFn == head then
            return ← goal.apply (Lean.mkAppN decl.toExpr computation.getAppArgs)
      let decl := (← Lean.getLCtx).get! head.fvarId!
      match decl.value? with
      | none => throwError "The local computation has no proved stability fact"
      | some value =>
        let expanded := (Lean.mkAppN value computation.getAppArgs).headBeta
        let nextType ← Lean.Meta.mkAppM ``Zlib.Deflate.Universal.Params.ParM #[keepArg, expanded]
        let next ← Lean.Meta.mkFreshExprSyntheticOpaqueMVar nextType
        goal.assign next
        return [next.mvarId!]


/-- One step of the parameter frame of `deflate`. -/
macro "par_step" : tactic => `(tactic|
  first
    | with_reducible exact par_trailerTail _
    | par_join
    | (apply ExactM.par; first | deflate_exact | x_leaf)
    | ((with_reducible apply par_wr) <;> intro _ <;> same_tac)
    | with_reducible apply ParM.cwhile
    | with_reducible apply ParM.cdoWhile
    | with_reducible apply ParM.ite
    | with_reducible apply ParM.bind
    | with_reducible intro _
    | split
    | dsimp only)

/-- The gzip string loop writes `last_flush` before its early return, so it keeps the parameters
in the sense of `ParRel`, not exactly. -/
theorem par_gz_string_loop (p : ZStreamPtr) (s : DeflateStatePtr) (sel : GzHeader → BPtr) :
    ParM true (gz_string_loop p s sel) := by
  unfold gz_string_loop
  repeat' par_step

theorem par_deflate (p : ZStreamPtr) (flush : Int32) : ParM true (deflate p flush) := by
  unfold deflate
  repeat' first
    | with_reducible exact par_gz_string_loop _ _ _
    | par_step

end Zlib.Deflate.Universal.Params
