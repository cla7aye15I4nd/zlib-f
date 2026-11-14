import ZlibF.Spec.Public.Sequences

/-!
# Sequences: safety goals

Split from `ZlibF/Spec/Public/Sequences.lean` without a change of statement or name
(`docs/design/safety-functional-split.md`). The namespace stays `ZlibF.Spec.Public`.
-/

namespace ZlibF.Spec.Public
open C Zlib.GzFs ZlibF.Spec

/-- **Safety of every permitted deflate call sequence** (the safety half of
`Goal.deflate_sequence`): every reachable stream satisfies the stream invariant, and one more
permitted call returns without a fault, keeps the invariant, writes only the stream's own blocks,
the stream record and the declared caller regions, and changes the live blocks exactly as the
allocation ledger says (no leak). The project's scope is safety (`docs/progress.md`, Scope); the
functional clauses of `Goal.deflate_sequence` are not planned. -/
def Goal.deflate_sequence_safety : Prop := StreamSequenceSafety .deflate

/-- **Safety of every permitted inflate call sequence** (the safety half of
`Goal.inflate_sequence`): every reachable stream satisfies the stream invariant, and one more
permitted call returns without a fault, keeps the invariant, writes only the stream's own blocks,
the stream record, the gzip header record and the declared caller regions, and changes the live
blocks exactly as the allocation ledger says (no leak); `inflateEnd` frees every block the stream
owns. The functional clauses of `Goal.inflate_sequence` are not planned (`docs/progress.md`,
Scope). -/
def Goal.inflate_sequence_safety : Prop := StreamSequenceSafety .inflate

end ZlibF.Spec.Public
