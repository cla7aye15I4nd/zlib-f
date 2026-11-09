import ZlibF.Proof.«deflate.c.engine.generic-all-scalar-cleanup»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- The original configuration's four owning pointers remain exact, including
post-trailer states whose wrapper sign changes. -/
theorem DefaultFinishBoundary.generic_ownership_pointers {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig}
    (state : DefaultFinishBoundary h r ds z d config) :
    d.window=config.window ∧ d.prev=config.prev ∧ d.head=config.head ∧ d.pending_buf=config.pending := by
  rcases state.phase with ⟨_,_,_,_initial,boundary⟩ | ⟨_,_,_,_,boundary,_status⟩ | finishing
  · exact ⟨congrArg EngineConfig.window boundary.configuration,congrArg EngineConfig.prev boundary.configuration,
      congrArg EngineConfig.head boundary.configuration,congrArg EngineConfig.pending boundary.configuration⟩
  · exact ⟨congrArg EngineConfig.window boundary.configuration,congrArg EngineConfig.prev boundary.configuration,
      congrArg EngineConfig.head boundary.configuration,congrArg EngineConfig.pending boundary.configuration⟩
  · exact ⟨congrArg EngineConfig.window finishing.configuration,congrArg EngineConfig.prev finishing.configuration,
      congrArg EngineConfig.head finishing.configuration,congrArg EngineConfig.pending finishing.configuration⟩

/-- Ownership is determined by the same state key and four real pointer fields;
no caller ownership invariant or statement about unrelated live objects is needed. -/
theorem DefaultFinishBoundary.generic_same_owned_keys {h g : Heap} {r : ZStreamRef} {ds : Nat}
    {z zg : ZStream} {d dg : DeflateState} {config : EngineConfig}
    (state : DefaultFinishBoundary h r ds z d config) (stateG : DefaultFinishBoundary g r ds zg dg config) :
    ∀ b, DeflateOwned ds dg b ↔ DeflateOwned ds d b := by
  obtain ⟨window,prev,head,pending⟩:=state.generic_ownership_pointers
  obtain ⟨windowG,prevG,headG,pendingG⟩:=stateG.generic_ownership_pointers
  intro b
  simp only [DeflateOwned,window,prev,head,pending,windowG,prevG,headG,pendingG]
end Zlib.Deflate.Engine.Proofs
