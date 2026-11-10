import ZlibF.Proof.«deflate.c.engine.raw-prefix»

/-! # Actual initialization and caller replacement retain encoding and Adler meaning -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols ZlibF.Math.DeflateEncoding
set_option autoImplicit false

/-- The source-established initial checksum denotes the empty accepted input. -/
theorem EngineStart.logical_adler {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState} (start : EngineStart h r ds z d) (input : Nat → UInt8) :
    z.adler = (ZlibF.Spec.adler32 (inputPrefix input (0 + fillEnd d))).toUInt64 := by
  have nilChecksum : (ZlibF.Spec.adler32 []).toUInt64 = (1 : UInt64) := by decide
  simpa only [fillEnd, start.start, start.lookahead, UInt32.toNat_zero, Nat.add_zero,
    inputPrefix, List.range_zero, List.map_nil, nilChecksum] using start.adler

/-- Actual successful initialization with the default memory parameters
establishes both raw encoding and checksum meaning on the same heap.
No engine invariant, checksum fact or universal Init2 contract is assumed.
The wrapper-header phase and allocation-failure safety have separate results. -/
theorem default_initialization_encoding_checksum {h : Heap} {r : ZStreamRef} {z : ZStream}
    {version : BPtr} {level : Int32} {p : ZlibF.Spec.Api.DeflParams}
    (hf : Fresh h) (hu : Uniq h) (hg : LibraryGlobals h) (hz : r.get h = some z)
    (ha : DefaultOrNull z) (hv : VersionValue h version (some 49))
    (params : ZlibF.Spec.Api.deflInit? level.toInt 8 15 8 0 = some p)
    (alloc : ∀ j, j < 5 → h.allocOk (h.nalloc + j) = true) (input : Nat → UInt8) :
    ∃ after zf sf,
      C.run (deflateInit_ (some r) level version 112) h = .ok (Z_OK, after) ∧
      EngineStart after r h.nextBlk zf sf ∧
      BufferedBoundary after r h.nextBlk zf sf input 0 0 [] (engineConfig sf) ∧
      EndFrontier after sf ∧ StreamReachable .deflate after r ∧ RawPrefix after sf input 0 [] ∧
      zf.adler = (ZlibF.Spec.adler32 (inputPrefix input (0 + fillEnd sf))).toUInt64 := by
  obtain ⟨after, zf, sf, run, start, boundary, frontier, _initial, reachable⟩ :=
    default_initialization_end_frontier hf hu hg hz ha hv params alloc input
  have stateA := boundary.buffered frontier (fun _ => start.pendingOut)
  obtain ⟨_pb, _buf, trees, _ledger, _balance⟩ := boundary.symbols
  have held := pending_bits_base trees start.pendingOut
  have empty := pending_bits_empty held (by rw [start.pending]; rfl) (by rw [start.bits]; rfl)
  rw [empty] at held
  refine ⟨after, zf, sf, run, start, stateA, frontier, reachable, ?_, start.logical_adler input⟩
  refine ⟨[], [], held, rfl, ?_⟩
  simpa only [inputPrefix, List.range_zero, List.map_nil] using block_prefix_empty ([] : List UInt8) [] 0

/-- Legal caller replacement preserves the same logical input, raw prefix
and checksum together. The caller can replace exhausted buffers and edit
unowned allocations without changing this initialized private meaning. -/
theorem rebuffer_encoding_checksum {h g : Heap} {r : ZStreamRef} {ds origin base : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {xs : List Symbol}
    {config : EngineConfig} {published : List UInt8}
    (boundary : BufferedBoundary h r ds z d input origin base xs config)
    (encoding : RawPrefix h d input base published)
    (checksum : z.adler = (ZlibF.Spec.adler32 (inputPrefix input (origin + fillEnd d))).toUInt64)
    (edit : Rebuffer h g r) (header : d.gzhead = none) :
    ∃ z', r.get g = some z' ∧ BufferedBoundary g r ds z' d input origin base xs config ∧
      RawPrefix g d input base published ∧
      z'.adler = (ZlibF.Spec.adler32 (inputPrefix input (origin + fillEnd d))).toUInt64 := by
  obtain ⟨z', get, stateA⟩ := rebuffer_buffered_boundary boundary edit header
  have encodingA := encoding.rebuffer boundary.good edit
  obtain ⟨_fresh, _uniq, _globals, _frame, old, new, oldGet, newGet, fields⟩ := edit
  have oldEq : old = z := Option.some.inj (oldGet.symm.trans boundary.good.live.hz)
  have newEq : new = z' := Option.some.inj (newGet.symm.trans get)
  subst old new
  refine ⟨z', get, stateA, encodingA, ?_⟩
  rw [fields]
  exact checksum

end Zlib.Deflate.Engine.Proofs
