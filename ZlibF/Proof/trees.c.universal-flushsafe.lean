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

/-- Batch B's `FlushSafe`, from the open small-memLevel overlay case. -/
theorem flushSafe_of_small (small : SmallOverlay) : Zlib.Deflate.Universal.FlushSafe := by
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

end Zlib.Deflate.Universal.Block
