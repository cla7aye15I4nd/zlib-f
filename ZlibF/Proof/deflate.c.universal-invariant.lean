import ZlibF.Spec.Public.Streams
import ZlibF.Proof.«deflate.c.engine.initial»
import ZlibF.Proof.«deflate.c.engine.symbol-ledger»

/-!
# deflate.c: the universal invariant of a deflate stream

`DInv` holds in every reachable state of a deflate stream, for every level, `memLevel`,
`windowBits`, strategy, tuning and header. Batch A establishes it after `deflateInit2_` and shows
that every stream operation and caller rebuffering keep it. The engine lemmas of batches B and C
assume it at entry and give it back at exit (`docs/progress.md`, section "Core proof skeletons").

Other modules use the interface lemmas `DInv.*` and the field accessors named in the progress
list. A missing fact is not unfolded from the definition: it is reported to batch A, which adds it
here and proves that every operation keeps it.
-/

namespace Zlib.Deflate.Universal
open C ZlibF.Spec ZlibF.Spec.Public Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Engine.Proofs
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-! ## 1. The invariant -/

/-- Scalar shape of the window, match, block and bit state (`docs/proof/deflate.md`, D).
`biValid`: between calls at most 7 bits wait in `bi_buf`, because every path that sends bits ends
with `bi_flush` (`flush_pending`, `_tr_align`, `deflatePrime`) or `bi_windup`. -/
structure Shape (d : DeflateState) : Prop where
  room : d.strstart.toNat + d.lookahead.toNat ≤ d.window_size.toNat
  insert : d.insert.toNat ≤ d.strstart.toNat
  prevLength : d.prev_length.toNat ≤ 258
  matchLength : d.match_length.toNat ≤ 258
  matchAvailable : d.match_available = 0 ∨ d.match_available = 1
  blockStart : -(d.w_size.toNat : Int) ≤ d.block_start.toInt ∧ d.block_start.toInt ≤ d.strstart.toNat
  highWater : d.high_water.toNat ≤ d.window_size.toNat
  lastFlush : -2 ≤ d.last_flush.toInt ∧ d.last_flush.toInt ≤ 5
  trailer : d.wrap.toInt < 0 → d.status = FINISH_STATE
  biUsed : 0 ≤ d.bi_used.toInt ∧ d.bi_used.toInt ≤ 8
  biValid : d.bi_valid.toInt ≤ 7

/-- H1/H2 (`docs/proof/deflate.md`): the hash chains name inserted positions up to the
insertion frontier `strstart - insert`, for every content of the unwritten `prev` slots. -/
def Chains (h : Heap) (d : DeflateState) : Prop :=
  HeapChains h d (d.strstart.toNat - d.insert.toNat)

/-- The recorded symbols of the current block: the bytes of `sym_buf` and the leaf frequencies of
`dyn_ltree` and `dyn_dtree` describe the same list `xs` (`SymbolLedger`). -/
def Recorded (h : Heap) (d : DeflateState) (xs : List Symbol) : Prop :=
  ∃ b a, d.pending_buf = .ref (.blk b) 0 ∧ h.bytes b = some a ∧ SymbolLedger a d xs

/-- Between calls the recorded symbols are counted in the tree frequencies, their distances are
within `MAX_DIST`, and the pending bytes lie below them (F9 at a call boundary). -/
structure Symbols (h : Heap) (d : DeflateState) : Prop where
  recorded : ∃ xs, Recorded h d xs ∧ ∀ s ∈ xs, s.distance ≤ d.w_size.toNat - 262
  below : ∀ b off, d.pending_out = .ref (.blk b) off → d.sym_next ≠ 0 →
    off + d.pending.toNat ≤ d.lit_bufsize.toNat

/-- **The universal invariant of a deflate stream.** Parametric in level, `memLevel`,
`windowBits`, strategy, tuning and header. Use the interface lemmas, not the fields. -/
structure DInv (h : Heap) (r : ZStreamRef) (ds : Nat) (z : ZStream) (d : DeflateState) : Prop where
  good : DGood h r ds z d
  alloc : DefAlloc z
  shape : Shape d
  chains : Chains h d
  symbols : Symbols h d

/-! ## 2. Interface of the invariant -/

theorem DInv.dgood {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) : DGood h r ds z d := inv.good

theorem DInv.defAlloc {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) : DefAlloc z := inv.alloc

theorem DInv.shape' {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) : Shape d := inv.shape

theorem DInv.chains' {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) : Chains h d := inv.chains

/-- The symbol ledger of the current block, with the distance bound. -/
theorem DInv.recorded {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) :
    ∃ xs, Recorded h d xs ∧ ∀ s ∈ xs, s.distance ≤ d.w_size.toNat - 262 :=
  inv.symbols.recorded

/-- Between calls at most 7 bits wait in the bit buffer. -/
theorem DInv.bi_valid_le {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) : 0 ≤ d.bi_valid.toInt ∧ d.bi_valid.toInt ≤ 7 :=
  ⟨inv.good.inv.bits.1, inv.shape.biValid⟩

/-- The stream record, the state block and the state are determined by the heap. -/
theorem DInv.unique {h : Heap} {r : ZStreamRef} {ds i : Nat} {z z' : ZStream}
    {d s : DeflateState} (inv : DInv h r ds z d) (good : DGood h r i z' s) :
    i = ds ∧ z' = z ∧ s = d := by
  have zs : z' = z := Option.some.inj (good.live.hz.symm.trans inv.good.live.hz)
  subst zs
  have is : i = ds := by
    have := good.live.zst.symm.trans inv.good.live.zst
    simpa only [Option.some.injEq, StateRef.deflate.injEq] using this
  subst is
  exact ⟨rfl, rfl, Option.some.inj (good.live.hs.symm.trans inv.good.live.hs)⟩

end Zlib.Deflate.Universal
