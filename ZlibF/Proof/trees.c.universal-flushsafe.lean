import ZlibF.Proof.«trees.c.universal-flush»
import ZlibF.Proof.«deflate.c.universal-strategies»

/-!
# trees.c: `FlushSafe` of batch B from the open overlay case

Batch C of the deflate skeleton. Batch B states the block flush it needs as `FlushSafe`
(`deflate.c.universal-strategies`). `flushSafe_of_small` proves it from one hypothesis: the
dynamic overlay room (fact F9) when `lit_bufsize < 2048`, that is `memLevel` 1 to 4. That
hypothesis is the open lemma `dynamic_overlay_small` (`docs/progress.md`); for `memLevel ≥ 5`
the room is `dynamic_overlay_large`.
-/

namespace Zlib.Deflate.Universal.Block
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Engine.Proofs
open Zlib.Trees.Proofs.Out (TreesInvAt)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- **F9 for `memLevel` 1 to 4** (open): the dynamic overlay room of every block of a
small symbol buffer, from a drained entry. -/
def SmallOverlay : Prop :=
  ∀ {h : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream} {d : DeflateState} {buf : Array UInt8}
    {xs : List Symbol},
    DGood h r ds z d → TreesInvAt h ds d pb buf → SymbolLedger buf d xs → d.pending = 0 →
    d.bi_valid.toInt ≤ 7 → d.lit_bufsize.toNat < 2048 → ∀ z', DynamicOverlay (r.put h z') ds d xs

/-- `FlushSafe` with three more facts at the end: `total_out` grows by the published bytes, only
the stream record, the blocks the state owns and the published output range change, and
`total_in` is kept. -/
def FlushSafeFrame : Prop :=
  ∀ {h : Heap} {r : ZStreamRef} {ds pb ob w : Nat} {z : ZStream} {d : DeflateState}
    {buf window : Array UInt8} {xs : List Symbol},
    DGood h r ds z d → TreesInvAt h ds d pb buf → StreamBuffers h r → 0 < d.level.toInt →
    ((∃ oo, z.next_out = .ref (.blk ob) oo) ∨ (∃ oo, z.next_out = .ref (.dstate_depth ob) oo)) →
    d.pending_out = d.pending_buf → d.pending = 0 → d.bi_valid.toInt ≤ 7 →
    SymbolLedger buf d xs → BlockInit.BlockClear d →
    d.window = .ref (.blk w) 0 → h.bytes w = some window →
    -(2 : Int) ^ 62 ≤ d.block_start.toInt → d.block_start.toInt ≤ d.strstart.toNat →
    d.strstart.toNat ≤ d.window_size.toNat → ∀ last : Bool,
    ∃ (produced : Nat) (after : Heap) (z' : ZStream) (result : DeflateState),
      FLUSH_BLOCK_ONLY (some (.tab ds)) (if last then 1 else 0) h = .ok ((), after) ∧
      DGood after r ds z' result ∧ StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧
      ByteSizes h after ∧ OutputStorage h after r ds pb ob ∧
      BlockInit.BlockClear result ∧ (∃ b, SymbolLedger b result []) ∧ result.bi_valid.toInt < 8 ∧
      (last = true → result.bi_valid.toInt = 0) ∧
      (result.pending = 0 → result.pending_out = result.pending_buf) ∧
      FlushFrame { d with block_start := d.strstart.toUInt64.toInt64 } result ∧
      (result.pending = 0 ∨ z'.avail_out = 0) ∧ result.«matches» = 0 ∧
      z'.total_out = z.total_out + UInt64.ofNat produced ∧
      BufferFrame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) [⟨z.next_out, produced⟩] ∧
      z'.total_in = z.total_in

/-- `FlushSafeFrame` drops to batch B's `FlushSafe`. -/
theorem FlushSafeFrame.safe (frame : FlushSafeFrame) : Zlib.Deflate.Universal.FlushSafe := by
  intro h r ds pb ob w z d buf window xs good trees buffers level pointer cursor pending bits ledger clear
    win get low high range last
  obtain ⟨produced, after, z', result, run, goodA, buffersA, account, sizes, storage, clearA, ledgerA, lowA,
    final, cursorA, frameA, drained, matchesA, total, buffer, totalIn⟩ :=
    frame good trees buffers level pointer cursor pending bits ledger clear win get low high range last
  exact ⟨produced, after, z', result, run, goodA, buffersA, account, sizes, storage, clearA, ledgerA, lowA,
    final, cursorA, frameA, drained, matchesA, total, buffer, totalIn⟩

/-- `FlushSafeFrame`, from the open small-memLevel overlay case. -/
theorem flushSafeFrame_of_small (small : SmallOverlay) : FlushSafeFrame := by
  intro h r ds pb ob w z d buf window xs good trees buffers level pointer cursor pending bits ledger clear
    win get low high range last
  have overlay : ∀ z', DynamicOverlay (r.put h z') ds d xs := by
    intro z'
    by_cases large : 2048 ≤ d.lit_bufsize.toNat
    · have capacity : xs.length + 1 ≤ d.lit_bufsize.toNat := by
        have bound := trees.run.sym_next_le
        rw [ledger.count, trees.base.sym_end] at bound
        have lowLit := trees.base.lit_lo
        omega
      exact dynamic_overlay_large large pending bits capacity
    · exact small good trees ledger pending bits (by omega) z'
  exact flush_block_only_safe (ob := ob) good trees buffers level pointer cursor pending bits ledger clear
    win get low high range overlay last

/-- Batch B's `FlushSafe`, from the open small-memLevel overlay case. -/
theorem flushSafe_of_small (small : SmallOverlay) : Zlib.Deflate.Universal.FlushSafe :=
  FlushSafeFrame.safe (flushSafeFrame_of_small small)

end Zlib.Deflate.Universal.Block
