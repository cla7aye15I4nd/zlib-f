import ZlibF.Proof.«deflate.c.engine.public-header»

/-! # Actual default entry checks and slow-strategy dispatch -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- `int ZEXPORT deflate(z_streamp strm, int flush)` (entry prefix).
An actually initialized default stream with valid nonnull buffers reaches
the zlib-header statements after recording Z_NO_FLUSH. Empty input is
included. This is an accepted-entry path, not the refusal theorem. -/
theorem public_default_entry {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState} (start : EngineStart h r ds z d)
    (out : z.next_out ≠ .null) (positive : z.avail_out ≠ 0)
    (input : z.avail_in ≠ 0 → z.next_in ≠ .null) :
    deflate (some r) Z_NO_FLUSH h =
      publicZlibHeader (some r) (some (.tab ds))
        (publicDataTail (some r) (some (.tab ds)) Z_NO_FLUSH)
        (setD h ds { d with last_flush := Z_NO_FLUSH }) := by
  have checked := stateCheck_live start.good.live
  have inputs : (z.avail_in != 0 && z.next_in == .null) = false := by
    by_cases empty : z.avail_in = 0
    · simp [empty]
    · simp [input empty]
  have rank0 : RANK Z_NO_FLUSH = pure 0 := by rfl
  have rankOld : RANK (-2) = pure (-4) := by rfl
  rw [public_deflate_source]
  simp only [bind_app, pure_app, checked, show ((0 : Int32) != 0) = false from rfl,
    show (Z_NO_FLUSH > Z_BLOCK) = False from by decide,
    show (Z_NO_FLUSH < 0) = False from by decide, decide_false, Bool.false_or, Bool.false_eq_true, ite_false,
    zrd_eq, start.good.live.hz, start.good.live.zst, castDeflateState,
    ldZStream_ok start.good.live.hz, ldDeflateState_tab start.good.live.hs, inputs,
    show (z.next_out == .null) = false from beq_eq_false_iff_ne.mpr out,
    start.status, show (INIT_STATE == FINISH_STATE) = false from by decide,
    Bool.false_and, show (z.avail_out == 0) = false from beq_eq_false_iff_ne.mpr positive,
    wrD_eq, start.good.live.hs, start.pending, show ((0 : UInt64) != 0) = false from rfl,
    start.lastFlush, rank0, rankOld, show ((0 : Int32) ≤ -4) = False from by decide,
    Bool.and_false, rdD_eq, setD_dstates_same, ZStreamRef.get_setD]

set_option maxHeartbeats 2500000 in
/-- `int ZEXPORT deflate(z_streamp strm, int flush)` (data dispatch).
For level six, strategy zero and BUSY status, the actual source executes
the proved complete slow loop before block output. Its byte budget is
internal and does not replace the public domain. No callee contract is
an assumption. Positive output and input or lookahead select this path. -/
theorem public_default_data_before_block {h : Heap} {r : ZStreamRef} {ds origin base : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {xs : List Symbol}
    (boundary : ContentBoundary h r ds z d input origin base xs)
    (status : d.status = BUSY_STATE) (level : d.level = 6) (strategy : d.strategy = 0)
    (wrap : d.wrap = 1) (buffers : StreamBuffers h r) (positive : z.avail_out ≠ 0)
    (valid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (data : z.avail_in ≠ 0 ∨ d.lookahead ≠ 0)
    (capacity : 3 * (origin + fillEnd d + z.avail_in.toNat - base + 1) < d.sym_end.toNat) :
    ∃ used after z' result ys extended nextOrigin,
      publicDataTail (some r) (some (.tab ds)) Z_NO_FLUSH h = .ok (Z_OK, after) ∧
      ContentBoundary after r ds z' result extended nextOrigin base ys ∧ StreamBuffers after r ∧
      StreamAccounting z z' used 0 ∧ ByteFrame h after (DeflateOwned ds d) ∧ SlowIterationFrame d result ∧
      (∀ i, i < origin + fillEnd d → extended i = input i) ∧ xs <+: ys ∧
      nextOrigin + fillEnd result = origin + fillEnd d + used ∧
      expandSymbols ys (inputPrefix extended base) =
        inputPrefix extended (nextOrigin + result.strstart.toNat - pendingCredit result) ∧
      used = z.avail_in.toNat ∧ z'.avail_in = 0 ∧ result.lookahead.toNat < 262 := by
  obtain ⟨used, after, z', result, ys, extended, nextOrigin, run, content, buffersA, account, storage, fields,
    agrees, symbols, endpoint, expands, stopped, allInput⟩ :=
    deflate_slow_no_flush_before_block boundary wrap buffers valid capacity
  have output : z'.avail_out = z.avail_out := UInt32.toNat_inj.mp (by
    have count := account.2.2.2.1
    omega)
  have nonempty : (z.avail_in != 0 || d.lookahead != 0) = true := by
    rcases data with inputNonempty | lookNonempty
    · simp [inputNonempty]
    · simp [lookNonempty]
  have cfg : config_at (6 : Int32) = pure (⟨8, 16, 128, 128, .slow⟩ : Config) := by rfl
  have tail : publicDataTail (some r) (some (.tab ds)) Z_NO_FLUSH h = .ok (Z_OK, after) := by
    unfold publicDataTail
    simp only [bind_app, pure_app, rdD_eq, boundary.good.live.hs, status,
      show (BUSY_STATE == GZIP_STATE) = false from by decide,
      show (BUSY_STATE == EXTRA_STATE) = false from by decide,
      show (BUSY_STATE == NAME_STATE) = false from by decide,
      show (BUSY_STATE == COMMENT_STATE) = false from by decide,
      show (BUSY_STATE == HCRC_STATE) = false from by decide,
      Bool.false_eq_true, ite_false, ldDeflateState_tab boundary.good.live.hs,
      zrd_eq, boundary.good.live.hz, nonempty,
      show (Z_NO_FLUSH != Z_NO_FLUSH) = false from rfl, Bool.false_and, Bool.or_false, ite_true,
      level, strategy, show ((6 : Int32) == 0) = false from rfl,
      show ((0 : Int32) == Z_HUFFMAN_ONLY) = false from rfl,
      show ((0 : Int32) == Z_RLE) = false from rfl, cfg, run,
      show (need_more == finish_started) = false from rfl,
      show (need_more == finish_done) = false from rfl,
      show (need_more == need_more) = true from rfl, Bool.false_or, Bool.true_or,
      content.good.live.hz, output,
      show (z.avail_out == 0) = false from beq_eq_false_iff_ne.mpr positive]
  obtain ⟨empty, short⟩ := stopped.resolve_right (by rw [output]; exact positive)
  exact ⟨used, after, z', result, ys, extended, nextOrigin, tail, content, buffersA, account, storage, fields,
    agrees, symbols, endpoint, expands, allInput positive, empty, short⟩

end Zlib.Deflate.Engine.Proofs
