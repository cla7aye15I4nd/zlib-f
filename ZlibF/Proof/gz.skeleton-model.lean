import ZlibF.Proof.«gz.inv-model»
import ZlibF.Proof.«gz.inv-frame»
import ZlibF.Proof.«gz.inv-reset»
import ZlibF.Proof.«gz.inv-put-scalars»
import ZlibF.Proof.«gzlib.c.error-inv-premises»
import ZlibF.Spec.Public.GzSafety

/-!
# gz file interface, safety skeleton: the model (skeleton)

Skeleton branch only (`skeleton/gz`): `sorry` marks an open lemma. The model is on `dev`: the invariant `GzInv`, the
call shape `GzCallSafe` and the helper shapes (`gz.inv-model`), the history `GzHistory`, the close and open shapes
and `Goal.gz_sequence_safety` (`ZlibF/Spec/Public/GzSafety.lean`), and the interface lemmas of `GzInv`
(`GzInv.caller` in `gz.inv-frame`, `GzInv.gz_error` in `gzlib.c.error-inv-premises`, `GzInv.gz_reset` in `gz.inv-reset`,
`GzInv.put_scalars` in `gz.inv-put-scalars`).

What is left here are the partial-correctness loop rules, which no proof uses yet.
-/

namespace ZlibF.Spec.Public
open C Zlib.GzFs
set_option autoImplicit false

/-- **Partial-correctness rule for `gwhile`** (planned, to move to a proof file): an invariant on the loop state,
world and heap that the condition and the body keep on every `.ok` result, and under which they never fault except
by running out of fuel, gives the same for the loop. The existing loop rules assume `.ok` or prove termination;
this one is what the no-fault half of the goal needs. -/
theorem gwhile_partial {σ : Type} (I : σ → Fs → Heap → Prop) (cond : σ → G (Bool × σ)) (body : σ → G σ)
    (hc : ∀ s fs h, I s fs h → (∀ e, cond s fs h = .error e → e = .outOfFuel) ∧
      ∀ c s' fs' h', cond s fs h = .ok (((c, s'), fs'), h') → I s' fs' h')
    (hb : ∀ s fs h, I s fs h → (∀ e, body s fs h = .error e → e = .outOfFuel) ∧
      ∀ s' fs' h', body s fs h = .ok ((s', fs'), h') → I s' fs' h') :
    ∀ s fs h, I s fs h → (∀ e, gwhile cond body s fs h = .error e → e = .outOfFuel) ∧
      ∀ s' fs' h', gwhile cond body s fs h = .ok ((s', fs'), h') → I s' fs' h' := by
  sorry

/-- The same rule for `gdoWhile`. -/
theorem gdoWhile_partial {σ : Type} (I : σ → Fs → Heap → Prop) (body : σ → G σ) (cond : σ → G (Bool × σ))
    (hb : ∀ s fs h, I s fs h → (∀ e, body s fs h = .error e → e = .outOfFuel) ∧
      ∀ s' fs' h', body s fs h = .ok ((s', fs'), h') → I s' fs' h')
    (hc : ∀ s fs h, I s fs h → (∀ e, cond s fs h = .error e → e = .outOfFuel) ∧
      ∀ c s' fs' h', cond s fs h = .ok (((c, s'), fs'), h') → I s' fs' h') :
    ∀ s fs h, I s fs h → (∀ e, gdoWhile body cond s fs h = .error e → e = .outOfFuel) ∧
      ∀ s' fs' h', gdoWhile body cond s fs h = .ok ((s', fs'), h') → I s' fs' h' := by
  sorry

end ZlibF.Spec.Public
