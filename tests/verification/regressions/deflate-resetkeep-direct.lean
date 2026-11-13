import ZlibF.Spec.Public.History

open C ZlibF.Spec.Public

/-! The deflate history domain admitted a direct `deflateResetKeep`. It keeps the window and the
hash tables but drops the lookahead; the positions `strstart - 2` and `strstart - 1` stay chain
heads with keys over the dropped bytes, and the hash-chain part of the deflate invariant fails
(the inflate batch 1 history: `deflateInit(6)`, `deflate(Z_NO_FLUSH)` on 1000 bytes, then
`deflateResetKeep`; heads 737 and 738 with `strstart = 739`). On the real C a later match can be
wrong (`docs/findings/deflate-resetkeep-stale-hash`). A direct call is no longer a stream
operation of a deflate history; `deflateReset` is. -/
namespace DeflateResetKeepDirectRegression

theorem direct_excluded (r : ZStreamRef) : ¬ StreamOperation .deflate r (.deflateResetKeep (some r)) := by
  simp [StreamOperation]

theorem reset_kept (r : ZStreamRef) : StreamOperation .deflate r (.deflateReset (some r)) := by
  simp [StreamOperation]

end DeflateResetKeepDirectRegression
