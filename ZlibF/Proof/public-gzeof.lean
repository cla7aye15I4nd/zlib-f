import ZlibF.Spec.Public.GzControl
import ZlibF.Proof.«gzlib.c.base»

namespace ZlibF.Spec.Public.Proofs
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib Zlib.Gzlib.Spec Zlib.Gzlib.Proofs

/-- `int gzeof(gzFile file)` reads an existing state record and leaves the heap unchanged. -/
theorem gzeof_record {h : Heap} {i : Nat} {s : GzState} (hs : h.gzstates i = some s) :
    C.run (gzeof (hnd i)) h = .ok ((if s.mode = GZ_READ then s.past else 0), h) := by
  unfold C.run gzeof
  by_cases hr : s.mode = GZ_READ
  · gsimp [hs, hr]
  · by_cases hw : s.mode = GZ_WRITE
    · gsimp [hs, hr, hw]
    · gsimp [hs, hr, hw]

/-- `int gzeof(gzFile file)` satisfies the complete public goal. -/
theorem gzeof_public : Goal.gzeof := by
  constructor
  · intro h
    rfl
  · intro h i s hs
    exact gzeof_record hs

#print axioms gzeof_record
#print axioms gzeof_public

end ZlibF.Spec.Public.Proofs
