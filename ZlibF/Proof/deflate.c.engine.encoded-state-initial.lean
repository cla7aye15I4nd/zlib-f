import ZlibF.Proof.«deflate.c.engine.encoded-state»
import ZlibF.Proof.«deflate.c.engine.initial-encoding-checksum»
import ZlibF.Proof.«deflate.c.engine.finish-protocol-initial»

/-! # Actual default initialization establishes observed encoding history -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Actual successful default initialization establishes both the complete
structural protocol and the encoding invariant for empty observed input
and output. Neither invariant nor any Init2 execution contract is assumed.
Allocation success is explicit here; actual-success extraction follows
when relating observed public traces to this initialized state. -/
theorem default_initialization_encoding_state {h : Heap} {r : ZStreamRef} {z : ZStream} {version : BPtr}
    (hf : Fresh h) (hu : Uniq h) (hg : LibraryGlobals h) (hz : r.get h = some z)
    (ha : DefaultOrNull z) (hv : VersionValue h version (some 49))
    (alloc : ∀ j, j < 5 → h.allocOk (h.nalloc + j) = true) :
    ∃ after zf sf,
      C.run (deflateInit_ (some r) Z_DEFAULT_COMPRESSION version 112) h = .ok (Z_OK, after) ∧
      DefaultEncodingState after r h.nextBlk zf sf (engineConfig sf) [] [] := by
  obtain ⟨after, zf, sf, run, start, boundary, _frontier, _reachable, _raw, checksum⟩ :=
    default_initialization_encoding_checksum (level := Z_DEFAULT_COMPRESSION)
      (p := ZlibF.Spec.Public.Proofs.DeflateInit.settings 6) hf hu hg hz ha hv
      (by decide +kernel) alloc (fun _ => 0)
  obtain ⟨other, otherZ, otherD, otherRun, protocol⟩ :=
    default_initialization_finish_protocol hf hu hg hz ha hv alloc
  have heaps : other = after := (Prod.mk.inj (Except.ok.inj (otherRun.symm.trans run))).2
  subst other
  have streams : otherZ = zf := Option.some.inj (protocol.good.live.hz.symm.trans start.good.live.hz)
  have states : otherD = sf := Option.some.inj (protocol.good.live.hs.symm.trans start.good.live.hs)
  subst otherZ otherD
  have prefixNil : inputPrefix (fun _ => 0) (0 + fillEnd sf) = [] := by
    simp only [fillEnd, start.start, start.lookahead, UInt32.toNat_zero, Nat.add_zero,
      inputPrefix, List.range_zero, List.map_nil]
  exact ⟨after, zf, sf, run, protocol, by simpa only [prefixNil] using checksum,
    Or.inl ⟨rfl, rfl, (fun _ => 0), start, boundary⟩⟩

open ZlibF.Spec.Public.Proofs.DeflateInit in
/-- The observed encoding invariant is inhabited by a concrete actual
default initialization, including the five real allocated objects. -/
theorem default_encoding_state_witness :
    ∃ after zf sf,
      C.run (deflateInit_ (some (.tab 0)) Z_DEFAULT_COMPRESSION (.ref (.blk 1) 0) 112)
        witnessHeap = .ok (Z_OK, after) ∧
      DefaultEncodingState after (.tab 0) 2 zf sf (engineConfig sf) [] [] := by
  exact default_initialization_encoding_state (h := witnessHeap) (r := .tab 0) (z := default)
    (version := .ref (.blk 1) 0) witness_fresh witness_uniq rfl
    (by simp [ZStreamRef.get, witnessHeap]) ⟨Or.inl rfl, Or.inl rfl⟩ witness_version (by intro _ _; rfl)

end Zlib.Deflate.Engine.Proofs
