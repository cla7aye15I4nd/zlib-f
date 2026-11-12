import ZlibF.Proof.«deflate.c.universal-call-lift»
import ZlibF.Proof.«deflate.c.universal-strategy-specs»
import ZlibF.Proof.«deflate.c.universal-slow»
import ZlibF.Proof.«deflate.c.universal-stored-tail»
import ZlibF.Proof.«deflate.c.universal-call-keep-phases»
import ZlibF.Proof.«deflate.c.universal-strategy-frame»

/-!
# deflate.c: the dispatch to the strategies in one `deflate` call

Owner 2 of the deflate split (`deflate_call`). The strategy phase of `deflate` chooses
`deflate_stored` at level 0, `deflate_huff` for `Z_HUFFMAN_ONLY`, `deflate_rle` for `Z_RLE`, and
otherwise the function of the configuration table (`deflate_fast` for levels 1 to 3,
`deflate_slow` for 4 to 9). With batch B's strategy specs, the dispatch keeps the invariant and
concludes the run frame `Fr` and the meaning of the returned state.
-/

namespace Zlib.Deflate.Universal.Call
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Engine.Proofs
set_option autoImplicit false

/-- The dispatch of `deflate`, as in the strategy phase. -/
def dispatch (s : DeflateStatePtr) (flush : Int32) (d : DeflateState) : M block_state :=
  if d.level == 0 then deflate_stored s flush
  else if d.strategy == Z_HUFFMAN_ONLY then deflate_huff s flush
  else if d.strategy == Z_RLE then deflate_rle s flush
  else do
    match (← config_at d.level).func with
    | .stored => deflate_stored s flush
    | .fast => deflate_fast s flush
    | .slow => deflate_slow s flush

/-- The meaning of the returned state: stored's at level 0, the others' otherwise. -/
def DispatchMeaning (d : DeflateState) (flush : Int32) (bstate : block_state) (z' : ZStream)
    (d' : DeflateState) : Prop :=
  (d.level = 0 ∧ StoredMeaning flush bstate z' d') ∨ (d.level ≠ 0 ∧ StratMeaning flush bstate z' d')

/-- The facts every strategy concludes. -/
def DispatchOut (h : Heap) (r : ZStreamRef) (ds : Nat) (z : ZStream) (d : DeflateState) (flush : Int32)
    (run : Except Fault (block_state × Heap)) : Prop :=
  ∃ bstate after z' d', run = .ok (bstate, after) ∧ DInv after r ds z' d' ∧ StreamBuffers after r ∧
    Fr h r ds d z after z' d' ∧ DispatchMeaning d flush bstate z' d'

/-- **The dispatch keeps the invariant**, for every level and strategy, given the overlay for
memLevel 1 and 2. -/
theorem dispatch_spec {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream}
    {d : DeflateState} (inv : DInv h r ds z d) (ov : Block.OverlayAt d.lit_bufsize.toNat) (entry : StrategyEntry h r z d) (flush : Int32) :
    DispatchOut h r ds z d flush (dispatch (some (.tab ds)) flush d h) := by
  have lo := inv.good.inv.level_lo
  have hi := inv.good.inv.level_hi
  have slo := inv.good.inv.strat_lo
  have shi := inv.good.inv.strat_hi
  by_cases l0 : d.level = 0
  · obtain ⟨b, a, z', d', run, i', bu, fr, m⟩ := stored_spec inv entry flush l0
    refine ⟨b, a, z', d', ?_, i', bu, fr, Or.inl ⟨l0, m⟩⟩
    simp only [C.run] at run
    simp [dispatch, l0, run]
  have l0' : (d.level == 0) = false := by simp [l0]
  have nz : d.level.toInt ≠ 0 := fun e => l0 (Int32.toInt_inj.mp (by simpa using e))
  by_cases hf : d.strategy = Z_HUFFMAN_ONLY
  · have s2 : d.strategy.toInt = 2 := by rw [hf]; rfl
    obtain ⟨b, a, z', d', run, i', bu, fr, m⟩ := huff_spec_of (Block.flushSafeAt_of ov) inv entry.toIn flush l0 s2
    refine ⟨b, a, z', d', ?_, i', bu, fr, Or.inr ⟨l0, m⟩⟩
    simp only [C.run] at run
    simp [dispatch, l0', hf, run]
  have hf' : (d.strategy == Z_HUFFMAN_ONLY) = false := by simp [hf]
  have s2 : d.strategy.toInt ≠ 2 := fun e => hf (Int32.toInt_inj.mp (by rw [e]; rfl))
  by_cases rl : d.strategy = Z_RLE
  · have s3 : d.strategy.toInt = 3 := by rw [rl]; rfl
    obtain ⟨b, a, z', d', run, i', bu, fr, m⟩ := rle_spec_of (Block.flushSafeAt_of ov) inv entry.toIn flush l0 s3
    refine ⟨b, a, z', d', ?_, i', bu, fr, Or.inr ⟨l0, m⟩⟩
    simp only [C.run] at run
    simp [dispatch, l0', hf', rl, run, show Z_RLE ≠ Z_HUFFMAN_ONLY by decide]
  have rl' : (d.strategy == Z_RLE) = false := by simp [rl]
  have s3 : d.strategy.toInt ≠ 3 := fun e => rl (Int32.toInt_inj.mp (by rw [e]; rfl))
  by_cases fast : d.level.toInt ≤ 3
  · obtain ⟨b, a, z', d', run, i', bu, fr, m⟩ := fast_spec_of (Block.flushSafeAt_of ov) inv entry.toIn flush ⟨by omega, fast, s2, s3⟩
    refine ⟨b, a, z', d', ?_, i', bu, fr, Or.inr ⟨l0, m⟩⟩
    simp only [C.run] at run
    have values : d.level = 1 ∨ d.level = 2 ∨ d.level = 3 := by
      have : d.level.toInt = 1 ∨ d.level.toInt = 2 ∨ d.level.toInt = 3 := by omega
      simp only [← Int32.toInt_inj]; exact this
    unfold dispatch
    rcases values with e | e | e <;>
      simp [l0', hf', rl', e, config_at, configuration_table, bind_app, pure_app] <;> exact run
  · obtain ⟨b, a, z', d', run, i', bu, fr, m⟩ := slow_spec_of (Block.flushSafeAt_of ov) inv entry.toIn flush ⟨by omega, s2, s3⟩
    refine ⟨b, a, z', d', ?_, i', bu, fr, Or.inr ⟨l0, m⟩⟩
    simp only [C.run] at run
    have values : d.level = 4 ∨ d.level = 5 ∨ d.level = 6 ∨ d.level = 7 ∨ d.level = 8 ∨ d.level = 9 := by
      have : d.level.toInt = 4 ∨ d.level.toInt = 5 ∨ d.level.toInt = 6 ∨ d.level.toInt = 7 ∨
          d.level.toInt = 8 ∨ d.level.toInt = 9 := by omega
      simp only [← Int32.toInt_inj]; exact this
    unfold dispatch
    rcases values with e | e | e | e | e | e <;>
      simp [l0', hf', rl', e, config_at, configuration_table, bind_app, pure_app] <;> exact run

/-- The dispatch is in `KeepRel`: no allocation, `msg` kept, the `data_type` guess. -/
theorem keep_dispatch (s : DeflateStatePtr) (flush : Int32) (d : DeflateState) :
    Zlib.Deflate.Universal.Keep.KeepM (dispatch s flush d) := by
  open Zlib.Deflate.Universal.Keep in
  unfold dispatch
  refine KeepM.ite _ (keep_deflate_stored _ _) (KeepM.ite _ (keep_deflate_huff _ _)
    (KeepM.ite _ (keep_deflate_rle _ _) ?_))
  refine KeepM.bind (keep_config_at _) (fun c => ?_)
  split
  · exact keep_deflate_stored _ _
  · exact keep_deflate_fast _ _
  · exact keep_deflate_slow _ _

/-- Batch B's run frame and `KeepRel` give the strategy frame batch C composes. -/
theorem Fr.strat {h after : Heap} {r : ZStreamRef} {ds : Nat} {d d' : DeflateState} {z z' : ZStream}
    (fr : Fr h r ds d z after z' d') (keep : Zlib.Deflate.Universal.Keep.KeepRel h after) :
    ∃ used produced, StratFrame h after r ds d z z' used produced ∧ Keys d d' := by
  obtain ⟨⟨u, p, acc, tot, buf, shape⟩, keys⟩ := fr
  exact ⟨u, p, ⟨⟨acc, tot.1, tot.2, buf, keep.liveChange, keep.nalloc⟩, shape⟩, keys⟩

end Zlib.Deflate.Universal.Call
