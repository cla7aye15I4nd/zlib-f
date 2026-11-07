import ZlibF.Proof.«deflate.c.engine.block-balance»

/-! # The initialized symbol boundary consumed by the strategy loop -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

def deferredCredit (d : DeflateState) : Int := if d.match_available = 0 then 0 else 1

/-- Exact unchanged fields of a non-flushing slow iteration. All fields
that the real search, tally and consumption can write are listed here. -/
def SlowRecordFrame (before after : DeflateState) : Prop :=
  after = { before with
    strstart := after.strstart, lookahead := after.lookahead, ins_h := after.ins_h,
    match_start := after.match_start, match_length := after.match_length,
    prev_match := after.prev_match, prev_length := after.prev_length, match_available := after.match_available,
    sym_next := after.sym_next, dyn_ltree := after.dyn_ltree, dyn_dtree := after.dyn_dtree }

theorem SlowRecordFrame.trans {a b c : DeflateState} (first : SlowRecordFrame a b)
    (second : SlowRecordFrame b c) : SlowRecordFrame a c := by
  unfold SlowRecordFrame at *
  rw [second, first]

theorem deferred_credit_bounds (d : DeflateState) : 0 ≤ deferredCredit d ∧ deferredCredit d ≤ 1 := by
  unfold deferredCredit
  split <;> omega

/-- Packed symbols, their real leaf frequencies and the block position
describe one state. The credit is tied to the actual deferred-byte flag. -/
def SymbolBoundary (h : Heap) (ds : Nat) (d : DeflateState) (xs : List Symbol) : Prop :=
  ∃ b buf, TreesInvAt h ds d b buf ∧ SymbolLedger buf d xs ∧ BlockBalance d xs (deferredCredit d)

theorem trees_at_buffer {h : Heap} {r : ZStreamRef} {ds b : Nat} {z : ZStream} {d : DeflateState}
    {buf : Array UInt8} (good : DGood h r ds z d)
    (pending : d.pending_buf = .ref (.blk b) 0) (get : h.bytes b = some buf) : TreesInvAt h ds d b buf := by
  obtain ⟨d0, b0, buf0, trees⟩ := good.trees
  have state : d0 = d := Option.some.inj (trees.base.dstate.symm.trans good.live.hs)
  subst d0
  have block : b0 = b := by simpa only [pending, Ptr.ref.injEq, BRef.blk.injEq, and_true] using trees.base.pbuf.symm
  subst b0
  have array : buf0 = buf := Option.some.inj (trees.base.bytes.symm.trans get)
  subst buf0
  exact trees

theorem symbol_boundary_of_ledger {h : Heap} {r : ZStreamRef} {ds b : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8} {xs : List Symbol}
    (good : DGood h r ds z d) (pending : d.pending_buf = .ref (.blk b) 0) (get : h.bytes b = some buf)
    (ledger : SymbolLedger buf d xs) (balance : BlockBalance d xs (deferredCredit d)) :
    SymbolBoundary h ds d xs := ⟨b, buf, trees_at_buffer good pending get, ledger, balance⟩

/-- Actual default public initialization establishes the complete symbol
boundary, including the relation between credit and the deferred flag. -/
theorem default_initialization_symbol_boundary {h : Heap} {r : ZStreamRef} {z : ZStream}
    {version : BPtr} {level : Int32} {p : ZlibF.Spec.Api.DeflParams}
    (hf : Fresh h) (hu : Uniq h) (hg : LibraryGlobals h) (hz : r.get h = some z)
    (ha : DefaultOrNull z) (hv : VersionValue h version (some 49))
    (params : ZlibF.Spec.Api.deflInit? level.toInt 8 15 8 0 = some p)
    (alloc : ∀ j, j < 5 → h.allocOk (h.nalloc + j) = true) :
    ∃ after zf sf,
      C.run (deflateInit_ (some r) level version 112) h = .ok (Z_OK, after) ∧
      EngineStart after r h.nextBlk zf sf ∧ DeflateInitial h after r p ∧
      StreamReachable .deflate after r ∧ SymbolBoundary after h.nextBlk sf [] := by
  obtain ⟨after, zf, sf, b, buf, run, start, initial, reachable, pending, get, ledger⟩ :=
    default_initialization_ledger hf hu hg hz ha hv params alloc
  refine ⟨after, zf, sf, run, start, initial, reachable,
    symbol_boundary_of_ledger start.good pending get ledger ?_⟩
  have credit : deferredCredit sf = 0 := by simp [deferredCredit, start.matchAvailable]
  rw [credit]
  exact initialized_block_balance start

end Zlib.Deflate.Engine.Proofs
