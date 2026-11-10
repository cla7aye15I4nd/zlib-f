import ZlibF.Proof.«deflate.c.engine.existing-slow-huffman-leaf-forest»
namespace Zlib.Trees.Proofs
open C Zlib.Trees
open HuffmanAbstract
set_option autoImplicit false
/-- Queue order is immaterial at the input of one mathematical merge. -/
theorem huffman_step_perm {s s' next : List HTree} {n m : HTree}
    (perm : s.Perm s') (step : HuffmanAbstract.Step s' next n m) :
    HuffmanAbstract.Step s next n m := by
  obtain ⟨rest,selected,first,second,result⟩ := step
  exact ⟨rest,perm.trans selected,first,second,result⟩

/-- A prefix of actual selected merges as a mathematical continuation
relation. It assumes no called C function's contract. The empty prefix is
established before executing the actual merge loop. -/
def HuffmanRunPrefix (initial current removed : List HTree) : Prop :=
  ∀ (tr : List HTree) (T : HTree), Merges current tr T → Merges initial (removed ++ tr) T

/-- No merge has yet removed any node. -/
theorem HuffmanRunPrefix.refl (s : List HTree) : HuffmanRunPrefix s s [] := by
  intro tr T run
  exact run

/-- One actual-step refinement extends the represented prefix. -/
theorem HuffmanRunPrefix.advance {initial current removed old next : List HTree} {n m : HTree}
    (prior : HuffmanRunPrefix initial current removed) (perm : old.Perm current)
    (step : HuffmanAbstract.Step old next n m) :
    HuffmanRunPrefix initial next (removed ++ [n,m]) := by
  intro tr T run
  have selected := huffman_step_perm perm.symm step
  have full := prior (n::m::tr) T (.step selected run)
  simpa only [List.append_assoc,List.cons_append,List.nil_append] using full
end Zlib.Trees.Proofs
#print axioms Zlib.Trees.Proofs.huffman_step_perm
#print axioms Zlib.Trees.Proofs.HuffmanRunPrefix.refl
#print axioms Zlib.Trees.Proofs.HuffmanRunPrefix.advance
