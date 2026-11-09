import ZlibF.Proof.«deflate.c.engine.common-valid-header-complete»
import ZlibF.Proof.«deflate.c.engine.header-finish-boundary»

/-! # Common-level complete FINISH headers retain the actual strategy boundary -/
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

def levelHeaderFinishHeap (h : Heap) (r : ZStreamRef) (ds pb ob oo : Nat)
    (z : ZStream) (d : DeflateState) (buf output : Array UInt8) : Heap :=
  setD (levelHeaderCompleteHeap h r ds pb ob oo z d buf output) ds (headerFinishState d)

/-- The completed real header preserves the initialized strategy content
and both chain frontiers. Recording FINISH does not affect those fields. -/
theorem common_header_finish_strategy_boundary {h : Heap} {r : ZStreamRef}
    {ds pb ob oo origin base : Nat} {z : ZStream} {d : DeflateState}
    {buf output : Array UInt8} {input : Nat → UInt8} {config : EngineConfig}
    (boundary : StrategyBoundary h r ds z d input origin base [] config)
    (frontier : EndFrontier h d) (publish : PublishReady d)
    (pending : d.pending_buf = .ref (.blk pb) 0) (get : h.bytes pb = some buf)
    (outGet : h.bytes ob = some output) (outside : ¬ DeflateOwned ds d ob) :
    StrategyBoundary (levelHeaderFinishHeap h r ds pb ob oo z d buf output) r ds
      (headerCompleteStream z ob oo) (headerFinishState d) input origin base [] config ∧
    EndFrontier (levelHeaderFinishHeap h r ds pb ob oo z d buf output) (headerFinishState d) ∧
    PublishReady (headerFinishState d) := by
  have content := common_header_complete_content (oo := oo) boundary.toContentBoundary pending get outGet outside
  have state : StrategyBoundary (levelHeaderCompleteHeap h r ds pb ob oo z d buf output) r ds
      (headerCompleteStream z ob oo) (headerCompleteState d) input origin base [] config :=
    ⟨content, boundary.configuration, ⟨boundary.clear.bl, boundary.clear.opt, boundary.clear.fixed⟩,
      boundary.bits, boundary.strict, fun _ => publish⟩
  have endH : EndFrontier (levelHeaderCompleteHeap h r ds pb ob oo z d buf output) (headerCompleteState d) :=
    common_header_complete_chains boundary.good pending frontier outside
  exact ⟨last_flush_strategy_boundary state Z_FINISH, last_flush_end_frontier (ds := ds) endH Z_FINISH, publish⟩


end Zlib.Deflate.Engine.Proofs
