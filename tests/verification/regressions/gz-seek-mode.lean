import ZlibF.Spec.Api.Examples
import ZlibF.Proof.Api.GzSeekRead

/-!
# Seek mode regression

The handles are those of the former counterexample. The seek relation
used to accept a reader that came back as a writer. It now rejects that
result, and the seek-then-read goal has a proof.
-/
namespace ZlibF.Spec.Api.Proofs

private def switched : GzHandle := { gzR with mode := .write }

/-- A successful seek cannot change the mode of the handle. -/
theorem seek_model_rejects_mode_change : ¬ GzSeek gzR 0 0 0 switched := by
  simp [GzSeek, GzHandle.tell, GzHandle.CopyMode, gzR, switched, Z.ok, Z.bufError]

/-- The corrected goal holds on the former counterexample's reader. -/
theorem former_counterexample_reads (h1 h2 : GzHandle) (bytes : List UInt8) (ret2 : Int)
    (hseek : GzSeek gzR 0 0 0 h1) (hpush : h1.pushed = []) (hread : GzReadFn h1 1 bytes ret2 h2) :
    bytes = (gzR.dec.drop 0).take 1 :=
  (gz_seek_read gzR h1 h2 0 0 0 1 bytes ret2 rfl rfl (by decide) (Or.inl rfl) hseek (by decide)).2
    hpush hread

#print axioms seek_model_rejects_mode_change
#print axioms former_counterexample_reads
end ZlibF.Spec.Api.Proofs
