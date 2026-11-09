import ZlibF.Proof.«deflate.c.engine.encoding-init-observed»
import ZlibF.Proof.«deflate.c.engine.fill-size-history»
import ZlibF.Math.DeflateCountedBudget

/-! # Internal cumulative cost metadata for actual default data histories

The metadata is established by actual initialization and retained under
legal caller edits here. Actual public request transitions remain separate
execution theorems; this module assumes none of their contracts.
-/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- An active stream has paid its two header bytes and only its actual
full-symbol-block costs. Its current ledger is not charged as a final block. -/
def WorkingCountedState (h : Heap) (r : ZStreamRef) (ds : Nat) (z : ZStream)
    (d : DeflateState) (config : EngineConfig) (accepted written : Nat) : Prop :=
  ∃ input origin base xs blocks,
    BufferedBoundary h r ds z d input origin base xs config ∧ d.status = BUSY_STATE ∧
    origin + fillEnd d = accepted ∧ ShortCandidateQuality d ∧ StoredSourceFloor d ∧
    (∀ s ∈ xs, s.distance ≠ 0 → s.value = 0 → s.distance ≤ 4096) ∧
    16383 * blocks ≤ base ∧
    written + d.pending.toNat + (d.bi_valid.toInt.toNat + 7) / 8 ≤ 2 + base + 5 * blocks

/-- After the single final block, the same cumulative budget reserves
the one-time four-byte trailer whenever the wrapper remains positive. -/
def FinishingCountedState (d : DeflateState) (config : EngineConfig) (accepted written : Nat) : Prop :=
  FinishingPhase d config ∧ ∃ blocks,
    16383 * blocks ≤ accepted ∧
    written + d.pending.toNat + (if d.wrap = 1 then 4 else 0) ≤ accepted + 5 * blocks + 11

/-- Before the header, the exact initial ghost counts are zero. The two
later phases retain actual initialized representation and cumulative cost. -/
def CountedPhase (h : Heap) (r : ZStreamRef) (ds : Nat) (z : ZStream)
    (d : DeflateState) (config : EngineConfig) (accepted written : Nat) : Prop :=
  (accepted = 0 ∧ written = 0 ∧ ∃ input,
    EngineStart h r ds z d ∧ BufferedBoundary h r ds z d input 0 0 [] config) ∨
  WorkingCountedState h r ds z d config accepted written ∨ FinishingCountedState d config accepted written

/-- Proof-local metadata attached to the existing actual default protocol.
It changes no public specification, target or translated function. -/
structure CountedBoundary (h : Heap) (r : ZStreamRef) (ds : Nat) (z : ZStream)
    (d : DeflateState) (config : EngineConfig) (accepted written : Nat) : Prop where
  protocol : DefaultFinishBoundary h r ds z d config
  window : config.windowBits = 15
  phase : CountedPhase h r ds z d config accepted written

private theorem empty_encoding_counted {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig}
    (state : DefaultEncodingState h r ds z d config [] []) :
    CountedBoundary h r ds z d config 0 0 := by
  have initial : ∃ input, EngineStart h r ds z d ∧ BufferedBoundary h r ds z d input 0 0 [] config := by
    rcases state.phase with ⟨_emptyInput, _emptyOutput, input, start, boundary⟩ |
        ⟨_emptyInput, impossible, _rest⟩ | ⟨_input, _origin, _base, _xs, _published, impossible, _rest⟩ |
        ⟨_published, impossible, _rest⟩
    · exact ⟨input, start, boundary⟩
    · cases impossible
    · cases impossible
    · cases impossible
  obtain ⟨input, start, boundary⟩ := initial
  refine ⟨state.protocol, ?_, Or.inl ⟨rfl, rfl, input, start, boundary⟩⟩
  exact (congrArg EngineConfig.windowBits boundary.configuration).symm.trans start.windowBits

/-- A real successful default initialization establishes the counted
boundary on its actual returned heap. The observed success theorem derives
all five allocation successes and the initialized invariant internally. -/
theorem observed_default_init_counted_state {h after : Heap} {r : ZStreamRef} {z : ZStream} {version : BPtr}
    (fresh : Fresh h) (unique : Uniq h) (globals : LibraryGlobals h) (get : r.get h = some z)
    (allocator : DefaultOrNull z) (versionValue : VersionValue h version (some 49))
    (actual : C.run (deflateInit_ (some r) Z_DEFAULT_COMPRESSION version 112) h = .ok (Z_OK, after)) :
    ∃ z' result, CountedBoundary after r h.nextBlk z' result (engineConfig result) 0 0 := by
  obtain ⟨z', result, state⟩ := observed_default_init_encoding_state fresh unique globals get allocator versionValue actual
  exact ⟨z', result, empty_encoding_counted state⟩

open ZlibF.Spec.Public.Proofs.DeflateInit in
/-- The counted metadata is inhabited by an existing concrete actual
default initialization witness, including the real five allocations. -/
theorem default_counted_state_witness :
    ∃ after z' result,
      C.run (deflateInit_ (some (.tab 0)) Z_DEFAULT_COMPRESSION (.ref (.blk 1) 0) 112)
        witnessHeap = .ok (Z_OK, after) ∧
      CountedBoundary after (.tab 0) 2 z' result (engineConfig result) 0 0 := by
  obtain ⟨after, z', result, actual, state⟩ := default_encoding_state_witness
  exact ⟨after, z', result, actual, empty_encoding_counted state⟩

/-- A legal caller replacement changes neither cumulative ghost count.
The actual rebuffer proofs retain each phase's private state and ledger. -/
theorem CountedBoundary.rebuffer {h g : Heap} {r : ZStreamRef} {ds accepted written : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig}
    (boundary : CountedBoundary h r ds z d config accepted written) (edit : Rebuffer h g r) :
    ∃ zg, r.get g = some zg ∧ CountedBoundary g r ds zg d config accepted written := by
  obtain ⟨zg, getG, protocolG⟩ := boundary.protocol.rebuffer edit
  have header := boundary.protocol.no_header
  refine ⟨zg, getG, protocolG, boundary.window, ?_⟩
  rcases boundary.phase with ⟨emptyInput, emptyOutput, input, start, state⟩ | working | finishing
  · obtain ⟨zs, startG⟩ := rebuffer_engine_start start edit header
    obtain ⟨zb, getB, stateG⟩ := rebuffer_buffered_boundary state edit header
    have sameS : zs = zg := Option.some.inj (startG.good.live.hz.symm.trans getG)
    have sameB : zb = zg := Option.some.inj (getB.symm.trans getG)
    subst zs zb
    exact Or.inl ⟨emptyInput, emptyOutput, input, startG, stateG⟩
  · obtain ⟨input, origin, base, xs, blocks, state, status, endpoint, candidate, floor, quality, minimum, cost⟩ := working
    obtain ⟨zb, getB, stateG⟩ := rebuffer_buffered_boundary state edit header
    have sameB : zb = zg := Option.some.inj (getB.symm.trans getG)
    subst zb
    exact Or.inr (Or.inl ⟨input, origin, base, xs, blocks, stateG, status, endpoint,
      candidate, floor, quality, minimum, cost⟩)
  · exact Or.inr (Or.inr finishing)

/-- The active ledger's base lies within the actual accepted endpoint by
its initialized accounting relation. No extra base or full-block limit
is a premise of the resulting complete-input envelope. -/
theorem CountedBoundary.written_default_budget {h : Heap} {r : ZStreamRef} {ds accepted written n : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig}
    (boundary : CountedBoundary h r ds z d config accepted written) (inputBound : accepted ≤ n) :
    written ≤ n + 5 * (n / 16383) + 11 := by
  rcases boundary.phase with ⟨_emptyInput, emptyOutput, _initial⟩ | working | finishing
  · rw [emptyOutput]; omega
  · obtain ⟨input, origin, base, xs, blocks, state, _status, endpoint, _candidate, _floor, _quality, minimum, cost⟩ := working
    have accounting := state.accounted
    have baseBound : base ≤ accepted := by dsimp only [fillEnd] at endpoint; omega
    have count := ZlibF.Math.DeflateBound.counted_blocks_le_input minimum (Nat.le_trans baseBound inputBound)
    omega
  · obtain ⟨_phase, blocks, minimum, cost⟩ := finishing
    have count := ZlibF.Math.DeflateBound.counted_blocks_le_input minimum inputBound
    omega

/-- The original source object's admitted size prevents saturation in
the advertised formula. The actual request-transition induction must
still construct this counted boundary at every desired history prefix. -/
theorem CountedBoundary.written_compress_bound {h : Heap} {r : ZStreamRef} {ds accepted written n : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig}
    (boundary : CountedBoundary h r ds z d config accepted written) (inputBound : accepted ≤ n)
    (object : n < 2 ^ 63) : written ≤ ZlibF.Spec.Api.compressBound n := by
  rw [ZlibF.Math.DeflateBound.compress_bound_object_formula n object]
  have cost := boundary.written_default_budget inputBound
  have envelope := ZlibF.Math.DeflateBound.counted_blocks_to_default_bound n
  omega

/-- Large-object strict slack follows from the same counted state. It is
not, by itself, a claim that a public call has returned STREAM_END. -/
theorem CountedBoundary.written_compress_bound_strict {h : Heap} {r : ZStreamRef} {ds accepted written n : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig}
    (boundary : CountedBoundary h r ds z d config accepted written) (inputBound : accepted ≤ n)
    (object : n < 2 ^ 63) (large : 33554432 ≤ n) : written < ZlibF.Spec.Api.compressBound n := by
  rw [ZlibF.Math.DeflateBound.compress_bound_object_formula n object]
  have cost := boundary.written_default_budget inputBound
  have strict := ZlibF.Math.DeflateBound.counted_budget_large_strict n large
  omega

end Zlib.Deflate.Engine.Proofs
