import ZlibF.Proof.«deflate.c.universal-call-dispatch»
import ZlibF.Proof.«deflate.c.universal-call-headerstep»

/-!
# deflate.c: the state stores after a strategy

Owner 2 of the deflate split (`deflate_call`). After the strategy, `deflate` stores
`status := FINISH_STATE` on a finishing return and `last_flush := -1` on a full output. These
lemmas give their frame and carry `DInv`, `HeaderInv`, `CallFacts` and the trees across them.
-/

namespace Zlib.Deflate.Universal.Call
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Engine.Proofs
open Zlib.Trees.Proofs.Out (TreesInvAt)
set_option autoImplicit false

/-- A store into the state record that keeps `depth` changes no byte view and allocates nothing. -/
theorem strat_frame_setD {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (good : DGood h r ds z d) (d' : DeflateState) (depth : d'.depth = d.depth) :
    StratFrame h (setD h ds d') r ds d z z 0 0 := by
  have shape := shape_setD good.live.hs d'
  refine ⟨⟨stream_accounting_zero z, by simp, by simp, ?_, full_shape_live_change shape, rfl⟩, shape⟩
  exact buffer_frame_views
    (full_frame_weaken (state_store_full_frame h ds d') (fun _ same => Or.inr (Or.inl same)))
    (byte_get_setD (d' := d') good.live.hs depth)

/-- The engine invariants across a store of `status` and `last_flush`. -/
theorem good_status_flush {h : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream} {d : DeflateState}
    {buf : Array UInt8} (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (st lf : Int32) (status : GoodStatus st) :
    let result : DeflateState := { d with status := st, last_flush := lf }
    DGood (setD h ds result) r ds z result ∧ TreesInvAt (setD h ds result) ds result pb buf ∧
      StreamBuffers (setD h ds result) r := by
  let result : DeflateState := { d with status := st, last_flush := lf }
  have inv : DStInv h ds result :=
    { good.inv with blocks := good.inv.blocks_keys rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl }
  have goodA := good.setD' (d' := result) rfl status inv (by trkeep)
  have treesA := trees_at_buffer goodA trees.base.pbuf trees.base.bytes
  have sizes := block_record_sizes good.live.hs (show result.depth = d.depth from rfl)
  have owned := stream_owned_keys good goodA rfl rfl rfl rfl
  exact ⟨goodA, treesA, stream_buffers_sizes good.live.hz goodA.live.hz buffers sizes owned (stream_accounting_zero z)⟩

/-- **`DInv`, `HeaderInv` and `CallFacts` across the stores after a strategy**: the status kept
(`BUSY_STATE` or `FINISH_STATE`) or set to `FINISH_STATE` (with no symbol and no lookahead), and a
new `last_flush` in range that is not the reset value. -/
theorem post_store {h : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream} {d : DeflateState}
    {buf : Array UInt8} (inv : DInv h r ds z d) (facts : CallFacts d) (trees : TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (busy : d.status = BUSY_STATE ∨ d.status = FINISH_STATE) (st lf : Int32)
    (status : st = d.status ∨ (st = FINISH_STATE ∧ d.sym_next = 0 ∧ d.lookahead = 0 ∧ d.bi_valid = 0))
    (lfRange : -2 ≤ lf.toInt ∧ lf.toInt ≤ 5) (notReset : lf ≠ -2) :
    let result : DeflateState := { d with status := st, last_flush := lf }
    DInv (setD h ds result) r ds z result ∧ HeaderInv result ∧ CallFacts result ∧
      TreesInvAt (setD h ds result) ds result pb buf ∧ StreamBuffers (setD h ds result) r ∧
      StratFrame h (setD h ds result) r ds d z z 0 0 := by
  intro result
  have busyOrFinish : result.status = BUSY_STATE ∨ result.status = FINISH_STATE := by
    rcases status with e | ⟨e, _⟩
    · show st = BUSY_STATE ∨ st = FINISH_STATE
      rw [e]; exact busy
    · exact Or.inr e
  have goodSt : GoodStatus st := by
    unfold GoodStatus
    rcases busyOrFinish with e | e <;> (change st = _ at e) <;> rw [e] <;> decide
  obtain ⟨good', trees', buffers'⟩ := good_status_flush inv.good trees buffers st lf goodSt
  have fields : HeaderFields d result := rfl
  have shape' : Shape result := Shape.of_fields inv.shape fields lfRange
    (fun hs => by rcases busyOrFinish with e | e <;> rw [e] at hs <;> rcases hs with x | x <;> exact absurd x (by decide))
    (fun neg => by
      rcases status with e | ⟨e, _⟩
      · show st = FINISH_STATE
        rw [e]; exact inv.shape.trailer neg
      · exact e)
    inv.shape.biValid inv.shape.cursor
  have inv' : DInv (setD h ds result) r ds z result :=
    inv.lift good' inv.alloc rfl shape' fields (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun b a _ get => ⟨a, get, fun _ _ => rfl⟩) inv.symbols.below
  refine ⟨inv', HeaderInv.of_busy busyOrFinish, ?_, trees', buffers', strat_frame_setD inv.good result rfl⟩
  exact { fresh := fun e => absurd e notReset, freshStart := fun e => absurd e notReset,
          finishSym := fun e => by
            rcases status with s | ⟨_, sym, _, _⟩
            · exact facts.finishSym (s ▸ e)
            · exact sym,
          finishLook := fun e => by
            rcases status with s | ⟨_, _, look, _⟩
            · exact facts.finishLook (s ▸ e)
            · exact look,
          finishBits := fun e => by
            rcases status with s | ⟨_, _, _, bits⟩
            · exact facts.finishBits (s ▸ e)
            · exact bits }

end Zlib.Deflate.Universal.Call
