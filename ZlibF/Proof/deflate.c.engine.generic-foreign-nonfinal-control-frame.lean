import ZlibF.Proof.«deflate.c.engine.generic-foreign-macro-prefix»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-macro-owner-readonly»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-macro-owner-fields»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-macro-interval»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-macro-physical»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-macro-checksum»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-buffer-frame-restore»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- The actual nonfinal block-control result has its full caller frame and checksum effect. -/
theorem default_foreign_nonfinal_control_run_frame {h after : Heap} {r : ZStreamRef} {ds owner oo origin base produced : Nat}
    {z z' : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {ret : Option block_state}
    (boundary : ContentBoundary h r ds z d input origin base xs)
    (buffers : StreamBuffers h r) (positive : 0<d.level.toInt)
    (pointer : z.next_out=.ref (.dstate_depth owner) oo) (cursor : d.pending_out=d.pending_buf)
    (memory : d.lit_bufsize.toNat=16384) (pending : d.pending=0) (bits : d.bi_valid.toInt≤7)
    (clear : BlockInit.BlockClear d) (available : d.match_available=0)
    (run : FLUSH_BLOCK (some (.tab ds)) 0 h=.ok (ret,after))
    (live : r.get after=some z') (account : StreamAccounting z z' 0 produced) :
    z'.adler=z.adler ∧ Shape h after ∧
      BufferFrame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) [⟨z.next_out,produced⟩] := by
  have adler := default_foreign_flush_control_run_adler boundary buffers positive pointer cursor memory pending bits clear available false run live account
  obtain ⟨shape,frame,_⟩ := default_foreign_flush_control_run_full_storage boundary buffers positive pointer cursor memory pending bits clear available false run
  have fields := default_foreign_flush_control_run_owner_fields boundary buffers positive pointer cursor memory pending bits clear available false run
  have readonly := default_foreign_flush_control_run_owner_readonly boundary buffers positive pointer cursor memory pending bits clear available false run
  have interval := default_foreign_flush_control_run_output_interval boundary buffers positive pointer cursor memory pending bits clear available false run live account
  have coarse : Frame h after (fun b => (StreamRoot r b ∨ DeflateOwned ds d b) ∨ b=owner) :=
    full_frame_weaken frame (fun _ yes => yes.elim (fun root => Or.inl (Or.inl root)) (fun remaining => remaining.elim (fun owned => Or.inl (Or.inr owned)) Or.inr))
  obtain ⟨foreign,get,_⟩ := caller_foreign_output boundary.good buffers pointer
  refine ⟨adler,shape,?_⟩
  rw [pointer]
  exact foreign_buffer_frame_of_fields coarse shape boundary.good.uniq get fields readonly interval

end Zlib.Deflate.Engine.Proofs
