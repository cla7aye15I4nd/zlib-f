import ZlibF.Proof.«deflate.c.engine.fill-pending-complete»
import ZlibF.Proof.«deflate.c.engine.rebuffer»

/-! # Caller buffer replacement retains both initialized hash frontiers -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- Arbitrary legal changes to unowned storage preserve the stronger
boundary. The header-free condition holds at the default entry. -/
theorem rebuffer_pending_boundary {h g : Heap} {r : ZStreamRef} {ds origin : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {xs : List ZlibF.Math.DeflateSymbols.Symbol}
    (boundary : PendingBoundary h r ds z d input origin xs)
    (edit : Rebuffer h g r) (header : d.gzhead = none) :
    ∃ z', r.get g = some z' ∧ PendingBoundary g r ds z' d input origin xs := by
  obtain ⟨z', getZ, _, good⟩ := rebuffer_good_no_header boundary.good edit header
  obtain ⟨w, wa, win, get, view, form⟩ := boundary.data
  obtain ⟨b, buf, trees, ledger, balance⟩ := boundary.symbols
  have window := rebuffer_owned boundary.good edit (x := w) (Or.inr (Or.inl win))
  have pending := rebuffer_owned boundary.good edit (x := b)
    (Or.inr (Or.inr (Or.inr (Or.inr trees.base.pbuf))))
  have symbols := symbol_boundary_of_ledger good trees.base.pbuf (pending.1.trans trees.base.bytes) ledger balance
  refine ⟨z', getZ, ⟨good, rebuffer_chains boundary.good edit boundary.chains,
    boundary.range, boundary.history, boundary.deferred, symbols,
    w, wa, win, window.1.trans get, view, form⟩,
    boundary.insert_le, rebuffer_chains boundary.good edit boundary.frontier, boundary.ready⟩

/-- Actual default initialization establishes the boundary before and
after every legal caller buffer replacement. Universal Init2 is not a
callee contract or proof dependency. -/
theorem default_pending_rebuffered {h : Heap} {r : ZStreamRef} {z : ZStream}
    {version : BPtr} {level : Int32} {p : ZlibF.Spec.Api.DeflParams}
    (hf : Fresh h) (hu : Uniq h) (hg : LibraryGlobals h) (hz : r.get h = some z)
    (allocators : DefaultOrNull z) (versionValue : VersionValue h version (some 49))
    (params : ZlibF.Spec.Api.deflInit? level.toInt 8 15 8 0 = some p)
    (alloc : ∀ j, j < 5 → h.allocOk (h.nalloc + j) = true) (input : Nat → UInt8) :
    ∃ after zf sf, C.run (deflateInit_ (some r) level version 112) h = .ok (Z_OK, after) ∧
      PendingBoundary after r h.nextBlk zf sf input 0 [] ∧ StreamReachable .deflate after r ∧
      ∀ g, Rebuffer after g r → ∃ zg,
        PendingBoundary g r h.nextBlk zg sf input 0 [] ∧ StreamReachable .deflate g r := by
  obtain ⟨after, zf, sf, run, start, boundary, initial, reachable⟩ :=
    default_initialization_pending_boundary hf hu hg hz allocators versionValue params alloc input
  refine ⟨after, zf, sf, run, boundary, reachable, ?_⟩
  intro g edit
  obtain ⟨zg, _, boundaryG⟩ := rebuffer_pending_boundary boundary edit (initial_no_header start initial)
  exact ⟨zg, boundaryG, StreamReachable.rebuffer reachable edit⟩

end Zlib.Deflate.Engine.Proofs
