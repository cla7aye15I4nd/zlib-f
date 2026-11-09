import ZlibF.Proof.«deflate.c.engine.common-initialized-refusal-storage»
import ZlibF.Proof.«deflate.c.engine.common-first-finish-storage»
import ZlibF.Proof.«deflate.c.engine.common-request-storage»

/-! # All initialized ordinary common-level calls retain exact resource frames -/
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- The exact full object/allocation frame includes INIT, first-call
refusals, either first ordinary flag at every positive raw capacity and
every subsequent ordinary request. This statement uses actual runs only. -/
theorem CommonInitializedEncodingState.ordinary_run_full_storage {h after : Heap} {r : ZStreamRef}
    {ds : Nat} {z : ZStream} {d : DeflateState} {config : EngineConfig} {flush rc : Int32}
    {accepted observed : List UInt8}
    (state : CommonInitializedEncodingState h r ds z d config accepted observed)
    (flag : flush = Z_NO_FLUSH ∨ flush = Z_FINISH) (buffers : StreamBuffers h r)
    (raw : DeflateCore.Output z.next_out) (actual : deflate (some r) flush h = .ok (rc, after)) :
    Shape h after ∧ Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b ∨ ByteRoot z.next_out b) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  rcases state.phase with ⟨_emptyInput, _emptyOutput, initial, boundary⟩ | post
  · have flagLow : 0 ≤ flush.toInt := by rcases flag with eq | eq <;> rw [eq] <;> decide
    have flagHigh : flush.toInt ≤ Z_BLOCK.toInt := by rcases flag with eq | eq <;> rw [eq] <;> decide
    by_cases refused : z.next_out = .null ∨ (z.avail_in ≠ 0 ∧ z.next_in = .null) ∨
        (d.status = FINISH_STATE ∧ flush ≠ Z_FINISH) ∨ z.avail_out = 0
    · obtain ⟨shape, frame, live, count, next⟩ := state.entry_refusal_run_full_storage flagLow flagHigh refused actual
      exact ⟨shape, full_frame_weaken frame (fun _ root => Or.inl root), live, count, next⟩
    · have nonnull : z.next_out ≠ .null := fun eq => refused (Or.inl eq)
      have valid : z.avail_in ≠ 0 → z.next_in ≠ .null := fun count eq => refused (Or.inr (Or.inl ⟨count, eq⟩))
      have positive : 0 < z.avail_out.toNat := by
        have nonzero : z.avail_out.toNat ≠ 0 := fun eq => refused (Or.inr (Or.inr (Or.inr (UInt32.toNat_inj.mp eq))))
        omega
      obtain ⟨ob, oo, pointer⟩ : ∃ ob oo, z.next_out = .ref (.blk ob) oo := raw.resolve_left nonnull
      have levelEq : d.level = config.level := congrArg EngineConfig.level boundary.configuration
      have low : 4 ≤ d.level.toInt := by rw [levelEq]; exact state.configuration.level_low
      have high : d.level.toInt ≤ 9 := by rw [levelEq]; exact state.configuration.level_high
      have executed : ∃ used produced rc' computed z' result,
          deflate (some r) flush h = .ok (rc', computed) ∧ DGood computed r ds z' result ∧
          StreamAccounting z z' used produced ∧ z'.total_in = z.total_in + UInt64.ofNat used ∧
          z'.total_out = z.total_out + UInt64.ofNat produced ∧ Shape h computed ∧
          Frame h computed (fun b => StreamRoot r b ∨ DeflateOwned ds d b ∨ b = ob) ∧
          LiveChange h computed (fun _ => False) (fun _ => False) ∧ computed.nalloc = h.nalloc ∧ computed.nextBlk = h.nextBlk := by
        rcases flag with rfl | rfl
        · obtain ⟨used, produced, computed, z', result, run, goodA, accountA, inputA, outputA, storage⟩ :=
            public_common_first_no_flush_full_storage_execution initial low high boundary buffers pointer positive state.configuration.memory valid
          exact ⟨used, produced, Z_OK, computed, z', result, run, goodA, accountA, inputA, outputA, storage⟩
        · exact public_common_first_finish_full_storage_execution initial low high boundary buffers pointer positive state.configuration.memory valid
      obtain ⟨_used, _produced, _rc, computed, _z, _result, run, _goodA, _accountA, _inputA, _outputA, storage⟩ := executed
      have heaps := (Prod.mk.inj (Except.ok.inj (run.symm.trans actual))).2
      subst computed
      simpa only [pointer, ByteRoot] using storage
  · exact post.protocol.ordinary_run_full_storage flag buffers raw actual

end Zlib.Deflate.Engine.Proofs
