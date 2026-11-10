import ZlibF.Proof.«deflate.c.gzip-read»

namespace Zlib.Deflate.Engine.Proofs.DefaultGzipProofs
open C Zlib.Deflate Zlib.Deflate.Engine.Proofs
set_option autoImplicit false

/-- Actual read_buf zero-length early return, for standalone or embedded streams.
No input pointer, wrapper, checksum, uniqueness or initialized-state assumption is
needed: the source returns before copying bytes or invoking a checksum function. -/
theorem read_buf_any_stream_zero {h : Heap} {r : ZStreamRef} {z : ZStream}
    (get : r.get h = some z) (buf : BPtr) (size : UInt32)
    (zero : rbLen z.avail_in size = 0) :
    read_buf (some r) buf size h = .ok (0,h) := by
  rw [read_buf_ref_eq get, zero]
  simp [rbCore]

end Zlib.Deflate.Engine.Proofs.DefaultGzipProofs
