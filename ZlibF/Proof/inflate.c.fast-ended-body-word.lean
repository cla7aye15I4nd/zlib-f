import ZlibF.Proof.«inflate.c.fast-causal-loop-run»
import ZlibF.Math.HeaderConsumedReplay

namespace Zlib.Inflate.Proofs.FastCommittedLoop
open C ZlibF.Spec ZlibF.Spec.Proofs
open ZlibF.Math.InflateHuffmanBodyContext
set_option autoImplicit false

/-- Actual no-future fast EOB and the independently accepted header
reconstruct the complete original compressed Body for every residual.
The actual source ledger separately identifies that residual with held and
unread caller bytes after suffix rollback. -/
theorem Ended.body_word
    {ctx : FastLoopContext} {p : Parameters ctx} {h : Heap} {q : Zlib.Inffast.L}
    {kind : Nat} {input payload : List Bool}
    (ended : Ended p h q) (header : Header kind input p.L p.D payload) :
    ∃ headerWord, input = headerWord ++ payload ∧
      ∀ residual, Body p.dict kind p.start
        ((headerWord ++ (p.initialWords ++ ended.word)) ++ residual) residual (p.past ++ ended.history) := by
  obtain ⟨headerWord, source, replay⟩ := header.consumed_word
  refine ⟨headerWord, source, ?_⟩
  intro residual
  have symbols := ended.symbols.append header.ext.1 header.ext.2 residual
  have body := (replay ((p.initialWords ++ ended.word) ++ residual)).body_iff.mpr
    (by simpa only [List.nil_append] using symbols)
  simpa only [List.append_assoc] using body

end Zlib.Inflate.Proofs.FastCommittedLoop
