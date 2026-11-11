import ZlibF.Proof.«deflate.c.universal-window»
import ZlibF.Proof.«trees.c.universal-flush»

/-!
# deflate.c, universal engine: the five compression functions

Batch B of the deflate skeleton (`docs/progress.md`, Core proof skeletons): `deflate_huff`,
`deflate_rle`, `deflate_fast`, `deflate_slow` and `deflate_stored` under the invariant `DInv` and
the strategy entry `StrategyEntry`, for every parameter tuple.

**Loop invariant.** At the head of every iteration of a strategy loop the state satisfies `DInv`
again, with an empty pending buffer and room in the caller's output buffer. Inside an iteration
the symbol buffer may be full; `FLUSH_BLOCK` empties it (batch C, `flush_block_only_safe`).

**Termination.** Every iteration either leaves the loop or consumes one byte of
`avail_in + lookahead` (`fill_window` moves input to lookahead without changing the sum).
-/

namespace Zlib.Deflate.Universal
open C ZlibF.Spec ZlibF.Spec.Public Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Engine.Proofs
open Zlib.Deflate.Proofs
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-! ## A `while` rule with a measure -/

theorem cwhile_go_measure {σ : Type} {cond : σ → M (Bool × σ)} {body : σ → M σ}
    (I : σ → Heap → Prop) (Q : σ → Heap → Prop) (μ : σ → Heap → Nat)
    (step : ∀ s h, I s h → ∃ c s1 h1, cond s h = .ok ((c, s1), h1) ∧
      (c = true → ∃ s2 h2, body s1 h1 = .ok (s2, h2) ∧ I s2 h2 ∧ μ s2 h2 < μ s h) ∧
      (c = false → Q s1 h1)) :
    ∀ n s h, I s h → μ s h < n → ∃ s' h', cwhile.go cond body n s h = .ok (s', h') ∧ Q s' h' := by
  intro n
  induction n with
  | zero => intro s h _ bound; omega
  | succ n ih =>
    intro s h inv bound
    obtain ⟨c, s1, h1, run, more, stop⟩ := step s h inv
    cases c with
    | false =>
      exact ⟨s1, h1, by simp [cwhile.go, run], stop rfl⟩
    | true =>
      obtain ⟨s2, h2, body2, inv2, less⟩ := more rfl
      obtain ⟨s', h', go, q⟩ := ih s2 h2 inv2 (by omega)
      exact ⟨s', h', by simp [cwhile.go, run, body2, go], q⟩

/-- `while` rule for a loop whose iterations decrease a measure below the fuel. -/
theorem cwhile_measure {σ : Type} {cond : σ → M (Bool × σ)} {body : σ → M σ}
    (I : σ → Heap → Prop) (Q : σ → Heap → Prop) (μ : σ → Heap → Nat)
    (step : ∀ s h, I s h → ∃ c s1 h1, cond s h = .ok ((c, s1), h1) ∧
      (c = true → ∃ s2 h2, body s1 h1 = .ok (s2, h2) ∧ I s2 h2 ∧ μ s2 h2 < μ s h) ∧
      (c = false → Q s1 h1))
    {s : σ} {h : Heap} (inv : I s h) (bound : μ s h < fuel) :
    ∃ s' h', cwhile cond body s h = .ok (s', h') ∧ Q s' h' :=
  cwhile_go_measure I Q μ step fuel s h inv bound

/-! ## Scalar updates of the engine fields -/

/-- `d'` changes only the engine scalars of `d`: positions, match state and insertion state. -/
def EngineUpdate (d d' : DeflateState) : Prop :=
  d' = { d with
    strstart := d'.strstart
    lookahead := d'.lookahead
    match_length := d'.match_length
    match_start := d'.match_start
    match_available := d'.match_available
    prev_length := d'.prev_length
    prev_match := d'.prev_match
    insert := d'.insert
    ins_h := d'.ins_h }

/-- An update of the engine scalars keeps `DGood`. -/
theorem engine_update_good {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d d' : DeflateState}
    (good : DGood h r ds z d) (update : EngineUpdate d d') : DGood (setD h ds d') r ds z d' := by
  rw [update]
  have inv : DStInv h ds { d with
      strstart := d'.strstart, lookahead := d'.lookahead, match_length := d'.match_length,
      match_start := d'.match_start, match_available := d'.match_available,
      prev_length := d'.prev_length, prev_match := d'.prev_match, insert := d'.insert,
      ins_h := d'.ins_h } :=
    { good.inv with blocks := good.inv.blocks_keys rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl }
  exact good.setD' rfl good.live.status inv (by trkeep)

/-- An update of the engine scalars keeps `DInv` once the new shape and hash state are shown. -/
theorem engine_update_inv {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d d' : DeflateState}
    (inv : DInv h r ds z d) (update : EngineUpdate d d') (shape : Shape d')
    (hashing : Hashing (setD h ds d') d') : DInv (setD h ds d') r ds z d' := by
  refine ⟨engine_update_good inv.good update, inv.alloc, inv.globals, shape, hashing, ?_⟩
  obtain ⟨⟨xs, ⟨b, a, pbuf, get, ledger⟩, dist⟩, clear, below⟩ := inv.symbols
  rw [update]
  exact ⟨⟨xs, ⟨b, a, pbuf, by simpa using get, ledger.keep rfl rfl rfl rfl⟩, dist⟩,
    ⟨clear.bl, clear.opt, clear.fixed⟩, below⟩

end Zlib.Deflate.Universal
