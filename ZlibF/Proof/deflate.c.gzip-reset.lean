import ZlibF.Proof.«deflate.c.life.reset»

namespace Zlib.Deflate.Engine.Proofs.DefaultGzipProofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
set_option autoImplicit false

/-- `int deflateResetKeep(z_streamp strm)`.
The actual gzip reset tail sets CRC32(empty) to zero and enters GZIP_STATE.
This local execution lemma needs neither a global uniqueness assumption nor
an initialized-state/callee-contract hypothesis. The tree storage is explicit. -/
theorem gzip_reset_keep_run {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState} {b : Nat} {buf : Array UInt8}
    (live : DLive h r ds z d)
    (trees : Zlib.Trees.Proofs.Out.TreesBase h ds d b buf)
    (wrap : d.wrap = 2) :
    ∃ a1 a2 a3,
      deflateResetKeep (some r) h =
        .ok (Z_OK, setD (r.put h { z with total_in := 0, total_out := 0, msg := .null, data_type := Z_UNKNOWN, adler := 0 })
          ds (rkPost ds (rkMid d) a1 a2 a3)) ∧
      a1.size = 573 ∧ a2.size = 61 ∧ a3.size = 39 ∧
      (rkPost ds (rkMid d) a1 a2 a3).status = GZIP_STATE ∧
      (rkPost ds (rkMid d) a1 a2 a3).wrap = 2 ∧
      (rkPost ds (rkMid d) a1 a2 a3).gzhead = none ∧
      (rkPost ds (rkMid d) a1 a2 a3).pending = 0 := by
  obtain ⟨a1, a2, a3, run, s1, s2, s3⟩ := resetKeep_run' live trees
    (by rw [wrap]; decide +kernel) (by rw [wrap]; decide +kernel)
  refine ⟨a1, a2, a3, ?_, s1, s2, s3, ?_, ?_, ?_, ?_⟩
  · simpa only [rkZ, wrap, absWrap, show ¬ ((2 : Int32) < 0) from by decide,
      if_false, show ((2 : Int32) == 2) = true from rfl, if_true] using run
  all_goals simp [rkPost, rkPost3, rkMid, absWrap, wrap,
    Zlib.Trees.Proofs.Out.ibRec, Zlib.Trees.Proofs.Out.trInitRec]

end Zlib.Deflate.Engine.Proofs.DefaultGzipProofs
