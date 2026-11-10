import ZlibF.Proof.«deflate.c.engine.public-output-interval-prefix»
import ZlibF.Proof.«deflate.c.engine.public-refusal-full-storage»

/-! # Precise public caller-buffer frames for actual ordinary requests -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Legal-flag entry refusals change only the stream record, preserving the complete caller array. -/
theorem DefaultFinishBoundary.entry_refusal_run_output_effect {h after : Heap} {r : ZStreamRef}
    {ds ob oo produced : Nat} {z : ZStream} {d : DeflateState} {config : EngineConfig} {flush rc : Int32}
    (boundary : DefaultFinishBoundary h r ds z d config) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo)
    (flagLo : 0 ≤ flush.toInt) (flagHi : flush.toInt ≤ Z_BLOCK.toInt)
    (refused : z.next_out = .null ∨ (z.avail_in ≠ 0 ∧ z.next_in = .null) ∨
      (d.status = FINISH_STATE ∧ flush ≠ Z_FINISH) ∨ z.avail_out = 0)
    (run : deflate (some r) flush h = .ok (rc, after)) : RawOutputInterval h after ob oo produced := by
  have storage := boundary.entry_refusal_run_full_storage flagLo flagHi refused run
  have privateFrame : Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) :=
    full_frame_weaken storage.2.1 (fun _ root => Or.inl root)
  exact RawOutputInterval.of_private_frame boundary.good buffers pointer privateFrame

/-- Duplicate NO_FLUSH requests retain the complete caller output array. -/
theorem public_duplicate_no_flush_run_output_effect {h after : Heap} {r : ZStreamRef}
    {ds ob oo produced : Nat} {z : ZStream} {d : DeflateState} {rc : Int32}
    (good : DGood h r ds z d) (buffers : StreamBuffers h r) (pointer : z.next_out = .ref (.blk ob) oo)
    (status : d.status = BUSY_STATE) (input : z.avail_in = 0) (pending : d.pending = 0)
    (out : z.next_out ≠ .null) (positive : z.avail_out ≠ 0)
    (lower : 0 ≤ d.last_flush.toInt) (upper : d.last_flush.toInt ≤ 5)
    (run : deflate (some r) Z_NO_FLUSH h = .ok (rc, after)) : RawOutputInterval h after ob oo produced := by
  have storage := public_duplicate_no_flush_run_full_storage good status input pending out positive lower upper run
  have privateFrame : Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) :=
    full_frame_weaken storage.2.1 (fun _ changed => changed.elim Or.inl (fun same => Or.inr (Or.inl same)))
  exact RawOutputInterval.of_private_frame good buffers pointer privateFrame

end Zlib.Deflate.Engine.Proofs
