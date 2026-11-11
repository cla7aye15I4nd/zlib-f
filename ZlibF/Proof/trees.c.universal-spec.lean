import ZlibF.Proof.«trees.c.universal-flush»
import ZlibF.Proof.«deflate.c.universal-invariant»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-output-base»

/-!
# trees.c: `FLUSH_BLOCK_ONLY` from the deflate invariant

Batch C of the deflate skeleton. `flush_block_dinv` reads the premises of `flush_block_only_safe`
from `DInv` (engine invariants, recorded symbols with their frequencies, cleared costs, the bit
bound, the pending cursor, the window shape and block span) and from the entry premises of a
block flush (`StreamBuffers`, a non-`NULL` output pointer, a positive level, nothing pending). The dynamic overlay
room is a premise (`DynamicOverlay`); for `memLevel ≥ 5` it is `dynamic_overlay_large`
(`flush_block_dinv_large`).
-/

namespace Zlib.Deflate.Universal.Block
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Engine.Proofs Zlib.Deflate.Universal
open Zlib.Trees.Proofs.Out (TreesInvAt)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- The tree invariant of the live state record. -/
theorem trees_of_good {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (good : DGood h r ds z d) : ∃ pb buf, TreesInvAt h ds d pb buf := by
  obtain ⟨d', pb, buf, trees⟩ := good.trees
  have same : d' = d := Option.some.inj (trees.base.dstate.symm.trans good.live.hs)
  subst same
  exact ⟨pb, buf, trees⟩

/-- A non-`NULL` caller output pointer is a byte block or a foreign `depth` array. -/
theorem output_pointer_cases {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (good : DGood h r ds z d) (buffers : StreamBuffers h r) (out : z.next_out ≠ .null) :
    ∃ ob, (∃ oo, z.next_out = .ref (.blk ob) oo) ∨ (∃ oo, z.next_out = .ref (.dstate_depth ob) oo) := by
  obtain ⟨z0, get0, _, caller, _⟩ := buffers
  have same : z0 = z := Option.some.inj (get0.symm.trans good.live.hz)
  subst same
  rcases caller with null | ⟨_, writable, _⟩
  · exact absurd null out
  · cases pointer : z0.next_out with
    | null => exact absurd pointer out
    | ref ref off =>
      rw [pointer] at writable
      rcases writable_reference_cases (writable rfl) with ⟨b, rfl⟩ | ⟨owner, rfl⟩
      · exact ⟨b, Or.inl ⟨off, rfl⟩⟩
      · exact ⟨owner, Or.inr ⟨off, rfl⟩⟩

/-- **`FLUSH_BLOCK_ONLY(s, last)` from `DInv`.** `last` is 0 or 1, as at every call site. -/
theorem flush_block_dinv {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) (buffers : StreamBuffers h r) (out : z.next_out ≠ .null)
    (level : 0 < d.level.toInt) (pending : d.pending = 0)
    (overlay : ∀ xs, Recorded h d xs → ∀ z', DynamicOverlay (r.put h z') ds d xs) (last : Bool) :
    ∃ (produced : Nat) (after : Heap) (z' : ZStream) (result : DeflateState),
      FLUSH_BLOCK_ONLY (some (.tab ds)) (if last then 1 else 0) h = .ok ((), after) ∧
      DGood after r ds z' result ∧ StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧
      BlockInit.BlockClear result ∧ (∃ b, SymbolLedger b result []) ∧ result.bi_valid.toInt < 8 ∧
      (last = true → result.bi_valid.toInt = 0) ∧
      (result.pending = 0 → result.pending_out = result.pending_buf) ∧
      FlushFrame { d with block_start := d.strstart.toUInt64.toInt64 } result ∧
      (result.pending = 0 ∨ z'.avail_out = 0) := by
  have good := inv.dgood
  obtain ⟨pb, buf, trees⟩ := trees_of_good good
  obtain ⟨xs, recorded, _distance⟩ := inv.recorded
  obtain ⟨b, a, pbuf, bytes, ledger⟩ := recorded
  have blockSame : b = pb := by
    have := pbuf.symm.trans trees.base.pbuf
    simpa only [Ptr.ref.injEq, BRef.blk.injEq, and_true] using this
  subst blockSame
  have arraySame : a = buf := Option.some.inj (bytes.symm.trans trees.base.bytes)
  subst arraySame
  obtain ⟨w, p, q, b0, blocks⟩ := good.inv.blocks
  obtain ⟨window, getWindow, _⟩ := blocks.wa
  have shape : Zlib.Deflate.Universal.Shape d := inv.shape'
  have bsHigh : d.block_start.toInt ≤ d.strstart.toNat := shape.blockStart
  have room : d.strstart.toNat + d.lookahead.toNat ≤ d.window_size.toNat := shape.room
  have biValid : d.bi_valid.toInt ≤ 7 := shape.biValid
  have cursor : d.pending_out = d.pending_buf := shape.cursor pending
  have clear : BlockInit.BlockClear d := inv.symbols.clear
  have span : (d.strstart.toNat : Int) - d.block_start.toInt ≤ 4294967296 := by
    have bound := shape.blockSpan (by intro zero; rw [zero] at level; exact absurd level (by decide))
    have symbols := trees.run.sym_next_le
    have endBound := trees.base.sym_end
    have litHigh := trees.base.lit_hi
    have available : d.match_available.toInt ≤ 1 := by
      rcases shape.matchAvailable with hz | ho
      · rw [hz]; decide
      · rw [ho]; decide
    have count : d.sym_next.toNat / 3 ≤ 32767 := by omega
    omega
  obtain ⟨ob, pointer⟩ := output_pointer_cases good buffers out
  obtain ⟨produced, after, z', result, run, goodA, buffersA, account, _sizes, _storage, clearA, ledgerA,
    low, final, cursorA, frame, drained⟩ :=
    flush_block_only_safe (ob := ob) good trees buffers level pointer cursor pending
      biValid ledger clear blocks.win getWindow span bsHigh (by omega)
      (overlay xs ⟨b, a, pbuf, bytes, ledger⟩) last
  exact ⟨produced, after, z', result, run, goodA, buffersA, account, clearA, ledgerA, low, final, cursorA,
    frame, drained⟩

/-- `flush_block_dinv` for `memLevel ≥ 5` (`lit_bufsize ≥ 2048`), where the overlay room is proved. -/
theorem flush_block_dinv_large {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) (buffers : StreamBuffers h r) (out : z.next_out ≠ .null)
    (level : 0 < d.level.toInt) (pending : d.pending = 0)
    (large : 2048 ≤ d.lit_bufsize.toNat) (last : Bool) :
    ∃ (produced : Nat) (after : Heap) (z' : ZStream) (result : DeflateState),
      FLUSH_BLOCK_ONLY (some (.tab ds)) (if last then 1 else 0) h = .ok ((), after) ∧
      DGood after r ds z' result ∧ StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧
      BlockInit.BlockClear result ∧ (∃ b, SymbolLedger b result []) ∧ result.bi_valid.toInt < 8 ∧
      (last = true → result.bi_valid.toInt = 0) ∧
      (result.pending = 0 → result.pending_out = result.pending_buf) ∧
      FlushFrame { d with block_start := d.strstart.toUInt64.toInt64 } result ∧
      (result.pending = 0 ∨ z'.avail_out = 0) := by
  refine flush_block_dinv inv buffers out level pending ?_ last
  intro xs recorded z'
  obtain ⟨b, a, pbuf, bytes, ledger⟩ := recorded
  have good := inv.dgood
  obtain ⟨pb, buf, trees⟩ := trees_of_good good
  have capacity : xs.length + 1 ≤ d.lit_bufsize.toNat := by
    have bound := trees.run.sym_next_le
    rw [ledger.count, trees.base.sym_end] at bound
    have lowLit := trees.base.lit_lo
    omega
  exact dynamic_overlay_large large pending (show d.bi_valid.toInt ≤ 7 from (inv.shape' : Zlib.Deflate.Universal.Shape d).biValid) capacity

end Zlib.Deflate.Universal.Block
