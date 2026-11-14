import ZlibF.Spec.Public.DeflateCore
import ZlibF.Proof.«deflate.c.engine.common-initial-first-ordinary-encoding»
import ZlibF.Proof.«deflate.c.engine.common-encoded-request»
import ZlibF.Spec.Functional.Api.Goals
import ZlibF.Spec.Functional.Api.InflateAccepted

/-! # A common-level invariant includes initialization before any output -/
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- Actual initialization establishes the first alternative. Every
post-header encoding phase uses the already proved common invariant.
Including INIT makes zero-output and pointer refusals available before
any positive first request. -/
structure CommonInitializedEncodingState (h : Heap) (r : ZStreamRef) (ds : Nat)
    (z : ZStream) (d : DeflateState) (config : EngineConfig) (accepted observed : List UInt8) : Prop where
  configuration : CommonSlowFinishConfig config
  reachable : StreamReachable .deflate h r
  phase :
    (accepted = [] ∧ observed = [] ∧ EngineStart h r ds z d ∧
      BufferedBoundary h r ds z d (fun _ => 0) 0 0 [] config) ∨
    CommonEncodingState h r ds z d config accepted observed

/-- The invariant supplies the same concrete live stream and private state. -/
theorem CommonInitializedEncodingState.good {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig} {accepted observed : List UInt8}
    (state : CommonInitializedEncodingState h r ds z d config accepted observed) : DGood h r ds z d := by
  rcases state.phase with ⟨_, _, start, _⟩ | post
  · exact start.good
  · exact post.protocol.good

/-- The configured stream uses no borrowed custom gzip header. -/
theorem CommonInitializedEncodingState.no_header {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig} {accepted observed : List UInt8}
    (state : CommonInitializedEncodingState h r ds z d config accepted observed) : d.gzhead = none := by
  rcases state.phase with ⟨_, _, _, boundary⟩ | post
  · exact (congrArg EngineConfig.header boundary.configuration).trans state.configuration.header
  · exact post.protocol.no_header

/-- Legal caller replacement retains INIT as well as all post-header
phases, the selected level and both observed byte lists. -/
theorem CommonInitializedEncodingState.rebuffer {h g : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig} {accepted observed : List UInt8}
    (state : CommonInitializedEncodingState h r ds z d config accepted observed) (edit : Rebuffer h g r) :
    ∃ zg, r.get g = some zg ∧ CommonInitializedEncodingState g r ds zg d config accepted observed := by
  have reachableG := StreamReachable.rebuffer state.reachable edit (fun k => nomatch k)
  rcases state.phase with ⟨emptyInput, emptyOutput, start, boundary⟩ | post
  · obtain ⟨zg, getG, boundaryG⟩ := rebuffer_buffered_boundary boundary edit state.no_header
    obtain ⟨zs, startG⟩ := rebuffer_engine_start start edit state.no_header
    have same : zs = zg := Option.some.inj (startG.good.live.hz.symm.trans getG)
    subst zs
    exact ⟨zg, getG, state.configuration, reachableG, Or.inl ⟨emptyInput, emptyOutput, startG, boundaryG⟩⟩
  · obtain ⟨zg, getG, postG⟩ := post.rebuffer edit
    exact ⟨zg, getG, state.configuration, reachableG, Or.inr postG⟩

/-- A message-only refusal retains the source-established INIT fields and
empty observations, or every correlated post-header encoding phase. -/
theorem CommonInitializedEncodingState.message_update {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig} {accepted observed : List UInt8}
    (state : CommonInitializedEncodingState h r ds z d config accepted observed)
    (message : BPtr) (goodA : DGood (r.put h {z with msg := message}) r ds {z with msg := message} d)
    (reachableA : StreamReachable .deflate (r.put h {z with msg := message}) r) :
    CommonInitializedEncodingState (r.put h {z with msg := message}) r ds {z with msg := message} d config accepted observed := by
  refine ⟨state.configuration, reachableA, ?_⟩
  rcases state.phase with ⟨emptyInput, emptyOutput, start, boundary⟩ | post
  · exact Or.inl ⟨emptyInput, emptyOutput, start.put_stream goodA rfl,
      stream_control_buffered boundary goodA⟩
  · have protocolA : CommonSlowFinishBoundary (r.put h {z with msg := message}) r ds {z with msg := message} d config :=
      ⟨goodA, reachableA, post.protocol.configuration,
        common_phase_stream_control post.protocol goodA, post.protocol.lower, post.protocol.upper⟩
    exact Or.inr (post.message_update message protocolA)

end Zlib.Deflate.Engine.Proofs
