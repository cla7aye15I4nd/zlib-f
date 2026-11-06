import ZlibF.Proof.«public-deflate-small-queries»

/-!
# deflate.c: priming refusal before compaction

The entry refuses an invalid stream and any bit count outside 0 through 16.
The accepted-count path, pending-byte compaction and bit-output relation remain open.
The statements below cover refusal paths only, not the complete public prime target.
-/

namespace Zlib.Deflate.Proofs
open C Zlib.Deflate.Spec ZlibF.Spec.Public ZlibF.Spec.Public.DeflateQueryProof

/-- `int deflatePrime(z_streamp strm, int bits, int value)` checks the stream first. -/
theorem deflatePrime_refused {h : Heap} {p : ZStreamPtr} (hr : RefusedDeflate h p)
    (bits value : Int32) :
    C.run (deflatePrime p bits value) h = .ok (Z_STREAM_ERROR, h) := by
  unfold deflatePrime
  exact check_refuse (refused_deflate_dom hr) (refused_deflate_not_init hr) _ _

/-- `int deflatePrime(z_streamp strm, int bits, int value)` refuses invalid counts
before moving pending bytes. This internal branch needs only `DLive`; it does not
assume pending-buffer bounds, a bit-output contract or a callee specification. -/
theorem deflatePrime_invalid_count {h : Heap} {r : ZStreamRef} {i : Nat}
    {z : ZStream} {s : DeflateState} (hl : DLive h r i z s) (bits value : Int32)
    (hb : bits.toInt < 0 ∨ 16 < bits.toInt) :
    C.run (deflatePrime (some r) bits value) h = .ok (Z_BUF_ERROR, h) := by
  have hc : bits < 0 ∨ bits > 16 := by
    rcases hb with hb | hb
    · exact Or.inl (Int32.lt_iff_toInt_lt.mpr (by simpa using hb))
    · exact Or.inr (Int32.lt_iff_toInt_lt.mpr (by simpa using hb))
  show deflatePrime (some r) bits value h = _
  unfold deflatePrime
  dsimp' [stateCheck_live hl, hl.zst, hl.hz, hl.hs, hc]

#print axioms deflatePrime_refused
#print axioms deflatePrime_invalid_count
end Zlib.Deflate.Proofs
