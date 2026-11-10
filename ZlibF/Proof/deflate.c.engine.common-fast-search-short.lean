import ZlibF.Proof.«deflate.c.engine.common-fast-search-source»

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Below three bytes the actual source skips insertion, keeps NIL and
skips the guarded matcher. No state or memory write occurs. -/
theorem fast_search_fewer_three {h : Heap} {ds : Nat} {d : DeflateState}
    (state : h.dstates ds = some d) (short : d.lookahead.toNat < 3) :
    fastSearch (some (.tab ds)) h = .ok (0, h) := by
  have guard : ¬ d.lookahead ≥ MIN_MATCH_u := by
    change ¬ MIN_MATCH_u ≤ d.lookahead
    rw [UInt32.le_iff_toNat_le]
    change ¬ 3 ≤ d.lookahead.toNat
    omega
  unfold fastSearch fastFind
  simp only [bind_app, rdD_eq, state, guard, ite_false, ldDeflateState_tab state]
  rfl

end Zlib.Deflate.Engine.Proofs
#print axioms Zlib.Deflate.Engine.Proofs.fast_search_fewer_three
