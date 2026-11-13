import Lean
import ZlibF.Proof.«deflate.c.universal-params-deflate»

/-!
# deflate.c: a deflate call changes a gz record only in its stream

A gz handle embeds its deflate stream in the gz record (`ZStreamRef.in_gzstate_strm i`). The
write side of the gz interface (`gz_comp`) reads and writes the gz record around its calls of
`deflate`, `deflateReset` and `deflateParams`. This module proves that a returning run of each of
them, on any stream, changes every gz record only in its `strm` field (`GzRecordsKept`).

For `deflate` the fact is the third component of the parameter frame (`par_deflate`). The resets
and `deflateParams` write parameters (`status`, `wrap`, `level`), so they are not in that frame;
they are covered by the weaker frame `GzKeepM`, built from the same primitives: every record
update of a deflate state and every stream store keeps the gz records but in `strm`.
-/

namespace Zlib.Deflate.Universal.Params
open C Zlib.Deflate Zlib.Deflate.Spec
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- A returning run changes every gz record only in its stream. -/
def GzKeepM {α : Type} (m : M α) : Prop := ∀ h a h', m h = .ok (a, h') → GzRecordsKept h h'

theorem ExactM.gz {α : Type} {m : M α} (exact : ExactM m) : GzKeepM m :=
  fun h a h' run => (exact h a h' run).2.2

theorem ParM.gz {α : Type} {keep : Bool} {m : M α} (par : ParM keep m) : GzKeepM m :=
  fun h a h' run => (par h a h' run).2.2

theorem GzKeepM.pure {α : Type} (a : α) : GzKeepM (Pure.pure a : M α) := (ExactM.pure a).gz

theorem GzKeepM.bind {α β : Type} {m : M α} {f : α → M β} (hm : GzKeepM m) (hf : ∀ a, GzKeepM (f a)) :
    GzKeepM (m >>= f) := by
  intro h value after run
  rw [bind_app] at run
  cases e : m h with
  | error _ => simp [e] at run
  | ok p =>
    rcases p with ⟨a, h1⟩
    rw [e] at run
    exact (hm h a h1 e).trans (hf a h1 value after run)

theorem GzKeepM.ite {α : Type} (p : Prop) [Decidable p] {a b : M α} (ha : GzKeepM a) (hb : GzKeepM b) :
    GzKeepM (if p then a else b) := by
  split <;> assumption

/-- `s->f = ...`, for every `f`: a deflate state record is not a gz record. -/
theorem gz_wr (p : DeflateStatePtr) (f : DeflateState → DeflateState) : GzKeepM (wr p f) := by
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
        exact GzRecordsKept.of_eq rfl

/-- `strm->f = ...`, for every `f`: a stream store changes at most the `strm` field of a gz record. -/
theorem gz_zwr (p : ZStreamPtr) (f : ZStream → ZStream) : GzKeepM (zwr p f) := by
  intro h value after run
  unfold zwr at run
  rw [bind_app] at run
  cases p with
  | none => cases run
  | some r =>
    cases get : r.get h with
    | none => simp [ldZStream, get] at run
    | some z =>
      simp only [ldZStream, get, stZStream] at run
      split at run
      · cases run
      · cases run
        exact GzRecordsKept.put_stream h r (f z)

/-- **`deflate` changes every gz record only in its stream.** -/
theorem gz_deflate (p : ZStreamPtr) (flush : Int32) : GzKeepM (deflate p flush) := (par_deflate p flush).gz

/-- Keep the translated do-notation join points: one proof per shared suffix. -/
elab "gz_join" : tactic =>
  Lean.Elab.Tactic.liftMetaTactic fun goal => goal.withContext do
    let target ← Lean.instantiateMVars (← goal.getType)
    unless target.isAppOf ``Zlib.Deflate.Universal.Params.GzKeepM do
      throwError "Expected a gz frame goal"
    let computation := target.getAppArgs.back!
    match computation with
    | .letE name type value body _ =>
      if type.getForallBody.isAppOf ``C.M then
        Lean.Meta.withLetDecl name type value fun suffix => do
          let stableType ← Lean.Meta.forallBoundedTelescope type (some type.getNumHeadForalls) fun xs _ => do
            let prop ← Lean.Meta.mkAppM ``Zlib.Deflate.Universal.Params.GzKeepM #[Lean.mkAppN suffix xs]
            Lean.Meta.mkForallFVars xs prop
          let proof ← Lean.Meta.mkFreshExprSyntheticOpaqueMVar stableType
          let proofName ← Lean.mkFreshUserName `suffix_gz
          Lean.Meta.withLetDecl proofName stableType proof fun receipt => do
            let nextType ← Lean.Meta.mkAppM ``Zlib.Deflate.Universal.Params.GzKeepM #[body.instantiate1 suffix]
            let next ← Lean.Meta.mkFreshExprSyntheticOpaqueMVar nextType
            let result ← Lean.Meta.mkLetFVars #[suffix, receipt] next
              (usedLetOnly := false) (generalizeNondepLet := false)
            goal.assign result
            return [proof.mvarId!, next.mvarId!]
      else
        let nextType ← Lean.Meta.mkAppM ``Zlib.Deflate.Universal.Params.GzKeepM #[body.instantiate1 value]
        let next ← Lean.Meta.mkFreshExprSyntheticOpaqueMVar nextType
        goal.assign next
        return [next.mvarId!]
    | _ =>
      let head := computation.getAppFn
      unless head.isFVar do throwError "No local join point"
      for decl in (← Lean.getLCtx) do
        let result := decl.type.getForallBody
        if result.isAppOf ``Zlib.Deflate.Universal.Params.GzKeepM then
          let observed := result.getAppArgs.back!
          if observed.getAppFn == head then
            return ← goal.apply (Lean.mkAppN decl.toExpr computation.getAppArgs)
      let decl := (← Lean.getLCtx).get! head.fvarId!
      match decl.value? with
      | none => throwError "The local computation has no proved gz frame fact"
      | some value =>
        let expanded := (Lean.mkAppN value computation.getAppArgs).headBeta
        let nextType ← Lean.Meta.mkAppM ``Zlib.Deflate.Universal.Params.GzKeepM #[expanded]
        let next ← Lean.Meta.mkFreshExprSyntheticOpaqueMVar nextType
        goal.assign next
        return [next.mvarId!]

/-- One step of the gz frame along translated code. -/
macro "gz_step" : tactic => `(tactic|
  first
    | with_reducible exact gz_deflate _ _
    | with_reducible exact gz_wr _ _
    | with_reducible exact gz_zwr _ _
    | gz_join
    | (apply ExactM.gz; first
        | with_reducible exact exact_deflateStateCheck _
        | with_reducible exact exact_CLEAR_HASH _
        | with_reducible exact exact_slide_hash _
        | with_reducible exact Zlib.Trees.ParamsProofs.exact__tr_init _
        | x_leaf)
    | with_reducible apply GzKeepM.ite
    | with_reducible apply GzKeepM.bind
    | with_reducible intro _
    | split
    | dsimp only)

theorem gz_lm_init (s : DeflateStatePtr) : GzKeepM (lm_init s) := by
  unfold lm_init
  repeat' gz_step

theorem gz_deflateResetKeep (p : ZStreamPtr) : GzKeepM (deflateResetKeep p) := by
  unfold deflateResetKeep
  repeat' gz_step

theorem gz_deflateReset (p : ZStreamPtr) : GzKeepM (deflateReset p) := by
  unfold deflateReset
  repeat' first
    | with_reducible exact gz_deflateResetKeep _
    | with_reducible exact gz_lm_init _
    | gz_step

theorem gz_deflateParams (p : ZStreamPtr) (level strategy : Int32) :
    GzKeepM (deflateParams p level strategy) := by
  unfold deflateParams
  repeat' gz_step

/-- **A returning `deflate` changes every gz record only in its stream** (`strm`). -/
theorem deflate_keeps_gz_records : ∀ (p : ZStreamPtr) (flush : Int32) (h : Heap) (a : Int32) (h' : Heap),
    C.run (Zlib.Deflate.deflate p flush) h = .ok (a, h') → GzRecordsKept h h' :=
  fun p flush h a h' run => gz_deflate p flush h a h' run

/-- **A returning `deflateReset` changes every gz record only in its stream** (`strm`). -/
theorem deflateReset_keeps_gz_records : ∀ (p : ZStreamPtr) (h : Heap) (a : Int32) (h' : Heap),
    C.run (Zlib.Deflate.deflateReset p) h = .ok (a, h') → GzRecordsKept h h' :=
  fun p h a h' run => gz_deflateReset p h a h' run

/-- **A returning `deflateParams` changes every gz record only in its stream** (`strm`). -/
theorem deflateParams_keeps_gz_records :
    ∀ (p : ZStreamPtr) (level strategy : Int32) (h : Heap) (a : Int32) (h' : Heap),
      C.run (Zlib.Deflate.deflateParams p level strategy) h = .ok (a, h') → GzRecordsKept h h' :=
  fun p level strategy h a h' run => gz_deflateParams p level strategy h a h' run

end Zlib.Deflate.Universal.Params
