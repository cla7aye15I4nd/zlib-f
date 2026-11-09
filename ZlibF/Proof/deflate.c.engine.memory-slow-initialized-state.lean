import ZlibF.Proof.«deflate.c.engine.memory-slow-observed-initial»
import ZlibF.Proof.«deflate.c.engine.common-finished-encoding»
import ZlibF.Proof.«deflate.c.engine.common-header-pending-encoding»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
open Zlib.Deflate.Proofs.MemoryInit (MemoryInitStart)
set_option autoImplicit false

/-- The actual slow initialization and subsequent ordinary public calls
retain their original accepted input and observed output. Phases include
INIT, the one-byte header, working raw compression and final publication.
This is an invariant to establish and preserve, not a callee assumption.
The history family fixes method eight, window fifteen, strategy zero,
zlib and default allocators; normalized slow levels four through nine
and the exact memory parameter remain explicit. -/
structure MemorySlowInitializedEncodingState (memory : Nat) (h : Heap) (r : ZStreamRef) (ds : Nat)
    (z : ZStream) (d : DeflateState) (config : EngineConfig) (accepted observed : List UInt8) : Prop where
  good : DGood h r ds z d
  options : MemorySlowConfig memory config
  reachable : StreamReachable .deflate h r
  globals : LibraryGlobals h
  allocators : DefAlloc z
  lower : -2 ≤ d.last_flush.toInt
  upper : d.last_flush.toInt ≤ 5
  checksum : z.adler = (ZlibF.Spec.adler32 accepted).toUInt64
  phase :
    (accepted = [] ∧ observed = [] ∧ ∃ input,
      MemoryInitStart memory h r ds z d ∧
      MemorySlowBoundary memory h r ds z d input 0 0 [] config) ∨
    (accepted = [] ∧ observed = [120] ∧ ∃ input,
      MemorySlowBoundary memory h r ds z d input 0 0 [] config ∧ d.status = BUSY_STATE ∧
      CommonHeaderPending h d config.level [120]) ∨
    (∃ input origin base xs published,
      observed = levelHeaderPrefix config.level ++ published ∧
      MemorySlowBoundary memory h r ds z d input origin base xs config ∧ d.strstart.toNat < 65536 ∧
      d.status = BUSY_STATE ∧ RawPrefix h d input base published ∧
      inputPrefix input (origin + fillEnd d) = accepted) ∨
    (∃ published, observed = levelHeaderPrefix config.level ++ published ∧
      FinishingPhase d config ∧ CommonFinishedEncoding h d config.level accepted published)

/-- Every phase's actual configuration excludes a custom gzip header. -/
theorem MemorySlowInitializedEncodingState.no_header {memory : Nat} {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig} {accepted observed : List UInt8}
    (state : MemorySlowInitializedEncodingState memory h r ds z d config accepted observed) : d.gzhead = none := by
  rcases state.phase with ⟨_empty, _out, _input, _start, boundary⟩ |
      ⟨_empty, _out, _input, boundary, _status, _encoding⟩ |
      ⟨_input, _origin, _base, _xs, _published, _out, boundary, _small, _status, _encoding, _inputEq⟩ |
      ⟨_published, _out, phase, _encoding⟩
  · exact (congrArg EngineConfig.header boundary.configuration).trans state.options.header
  · exact (congrArg EngineConfig.header boundary.configuration).trans state.options.header
  · exact (congrArg EngineConfig.header boundary.configuration).trans state.options.header
  · exact (congrArg EngineConfig.header phase.configuration).trans state.options.header

/-- Actual successful Init2 establishes the strong initialized encoding
invariant. No representation, checksum or allocation-success fact is an
extra caller premise. Every legal memory setting is included here.
This internal theorem fixes method eight, window fifteen, strategy zero,
zlib wrapping and default-or-null callbacks, with normalized slow levels
four through nine. It establishes the initial phase of the invariant;
preservation by subsequent public calls is a separate proof. -/
theorem memory_slow_initialized_state {memory : Nat} {before initialized : Heap}
    {r : ZStreamRef} {version : BPtr} (domain : InitDomain before r version)
    (low : 1 ≤ memory) (high : memory ≤ 9) (level : Int32)
    (levelLow : 4 ≤ (DefaultInit.levelValue level).toInt)
    (levelHigh : (DefaultInit.levelValue level).toInt ≤ 9)
    (actual : C.run (deflateInit2_ (some r) level 8 15 (Int32.ofInt memory) 0 version 112) before =
      .ok (Z_OK, initialized)) :
    ∃ zf sf, MemorySlowInitializedEncodingState memory initialized r before.nextBlk zf sf
      (engineConfig sf) [] [] := by
  obtain ⟨zf, sf, initial, boundary, _normalized, relation, reachable, _count⟩ :=
    memory_slow_observed_initialization domain low high level levelLow levelHigh actual (fun _ => 0)
  obtain ⟨zi, _si, goodI, allocI, freeI, _level, _strategy, _window, _hash, _wrap, _start,
      _look, _pending, _bits, _header, _totalIn, _totalOut, _message, frame, _live, _owned⟩ := relation
  have same : zi = zf := Option.some.inj (goodI.live.hz.symm.trans initial.good.live.hz)
  subst zi
  have globals : LibraryGlobals initialized := frame.1.symm.trans domain.2.2.1
  refine ⟨zf, sf, initial.good, boundary.options, reachable, globals, ⟨allocI, freeI⟩,
    ?_, ?_, ?_, Or.inl ⟨rfl, rfl, _, initial, boundary⟩⟩
  · rw [initial.lastFlush]; decide
  · rw [initial.lastFlush]; decide
  · change zf.adler = 1
    exact initial.adler

end Zlib.Deflate.Engine.Proofs
#print axioms Zlib.Deflate.Engine.Proofs.MemorySlowInitializedEncodingState.no_header
#print axioms Zlib.Deflate.Engine.Proofs.memory_slow_initialized_state
