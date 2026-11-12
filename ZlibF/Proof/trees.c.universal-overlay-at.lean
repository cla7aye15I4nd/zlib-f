import ZlibF.Proof.«trees.c.universal-overlay-mid»

/-!
# trees.c: the overlay hypothesis per symbol buffer size

`TinyOverlay` (`trees.c.universal-overlay-mid`) is the dynamic-block room for every state with
`lit_bufsize < 512`. `TinyOverlayAt L` is the same room for the states with `lit_bufsize = L`
only, and `TinyOverlay` is `∀ L < 512, TinyOverlayAt L` (`tinyOverlay_iff`). A strategy needs
the instance for its own symbol buffer size, which no operation of a stream changes after
`deflateInit2_`; `OverlayAt L` is that instance, and it holds with no hypothesis for `L ≥ 512`
(`memLevel ≥ 3`), from `dynamic_overlay_mid` and `dynamic_overlay_large`.
-/

namespace Zlib.Deflate.Universal.Block
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Engine.Proofs
open Zlib.Trees.Proofs.Out (TreesInvAt)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- The dynamic-block room for the states with `lit_bufsize = L` (open for `L = 128` and
`L = 256`, `memLevel` 1 and 2). -/
def TinyOverlayAt (L : Nat) : Prop :=
  ∀ {h : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream} {d : DeflateState} {buf : Array UInt8}
    {xs : List Symbol},
    DGood h r ds z d → TreesInvAt h ds d pb buf → SymbolLedger buf d xs → BlockInit.BlockClear d →
    d.pending = 0 → d.bi_valid.toInt ≤ 7 → d.lit_bufsize.toNat = L →
    ∀ z', DynamicOverlay (r.put h z') ds d xs

theorem tinyOverlay_iff : TinyOverlay ↔ ∀ L, L < 512 → TinyOverlayAt L := by
  constructor
  · intro tiny L small h r ds pb z d buf xs good trees ledger clear pending bits size z'
    exact tiny good trees ledger clear pending bits (by omega) z'
  · intro all h r ds pb z d buf xs good trees ledger clear pending bits small z'
    exact all _ small good trees ledger clear pending bits rfl z'

/-- The overlay instance a stream with `lit_bufsize = L` needs. -/
def OverlayAt (L : Nat) : Prop := L < 512 → TinyOverlayAt L

/-- `memLevel ≥ 3`: no hypothesis. -/
theorem overlayAt_mid {L : Nat} (lower : 512 ≤ L) : OverlayAt L := fun small => absurd small (by omega)

theorem TinyOverlay.at (tiny : TinyOverlay) (L : Nat) : OverlayAt L :=
  fun small => tinyOverlay_iff.mp tiny L small

/-- The overlay instance for every size from the two open sizes: `lit_bufsize` is
`1 << (memLevel + 6)`, so below 512 it is 128 or 256 (`deflateInit2_`); the other sizes below
512 never occur and are covered by the hypothesis only through `L = 128` and `L = 256`. -/
theorem overlayAt_of_two (t128 : TinyOverlayAt 128) (t256 : TinyOverlayAt 256) {L : Nat}
    (pow : L = 128 ∨ L = 256 ∨ 512 ≤ L) : OverlayAt L := by
  intro small
  rcases pow with e | e | e
  · subst e; exact t128
  · subst e; exact t256
  · omega

/-- **The block flush for one symbol buffer size**, from its overlay instance. -/
theorem flushSafeAt_of {L : Nat} (ov : OverlayAt L) : Zlib.Deflate.Universal.FlushSafeAt L := by
  intro h r ds pb ob w z d buf window xs size good trees buffers level pointer cursor pending bits ledger clear
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
    · by_cases lower : 512 ≤ d.lit_bufsize.toNat
      · exact dynamic_overlay_mid good trees ledger pending bits lower (by omega) z'
      · exact ov (by omega) good trees ledger clear pending bits size z'
  obtain ⟨produced, after, z', result, run, goodA, buffersA, account, sizes, storage, clearA, ledgerA, lowA,
    final, cursorA, frameA, drained, matchesA, total, buffer, totalIn⟩ :=
    flush_block_only_safe (ob := ob) good trees buffers level pointer cursor pending bits ledger clear
      win get low high range overlay last
  exact ⟨produced, after, z', result, run, goodA, buffersA, account, sizes, storage, clearA, ledgerA, lowA,
    final, cursorA, frameA, drained, matchesA, total, buffer, totalIn⟩

end Zlib.Deflate.Universal.Block
