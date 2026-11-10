import ZlibF.Proof.«deflate.c.gzip-initial-engine»

namespace Zlib.Deflate.Engine.Proofs.DefaultGzipBoundary
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Proofs.DefaultGzipInit
set_option autoImplicit false

/-- A concrete embedded stream reaches the new gzip engine boundary by
actual initialization. The pre-state contains no initialized deflate state. -/
theorem embedded_gzip_initial_engine_witness :
    ∃ after zf sf,
      C.run (deflateInit2_ (some (.in_gzstate_strm 0)) Z_DEFAULT_COMPRESSION 8 31 8 0
        (.ref (.blk 1) 0) 112) embeddedWitnessHeap = .ok (Z_OK, after) ∧
      GzipEngineStart after (.in_gzstate_strm 0) 2 zf sf ∧
      DeflateInitial embeddedWitnessHeap after (.in_gzstate_strm 0) (settings 6) ∧
      StreamReachable .deflate after (.in_gzstate_strm 0) ∧
      after.nalloc = 5 ∧ after.nextBlk = 7 := by
  obtain ⟨after,zf,sf,run,engine,initial,reachable,_allocator,_ni,_ai,_no,_ao,count,next⟩ :=
    public_gzip_initial_engine embedded_witness_fresh embedded_witness_uniq rfl
      (r := .in_gzstate_strm 0) (z := default)
      (by simp [ZStreamRef.get, embeddedWitnessHeap]; rfl)
      ⟨Or.inl rfl, Or.inl rfl⟩ embedded_witness_version Z_DEFAULT_COMPRESSION rfl
      (by intro j below; rfl)
  exact ⟨after,zf,sf,run,engine,initial,reachable,count,next⟩

end Zlib.Deflate.Engine.Proofs.DefaultGzipBoundary
