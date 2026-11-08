import ZlibF.Proof.«trees.c.initial-frequencies»

/-! # The actual tree initializer clears the BL frequency alphabet -/

namespace Zlib.Trees.Proofs.Out
open C Zlib.Trees
set_option autoImplicit false

/-- `_tr_init` retains the zero BL-frequency facts produced by the actual
init_block loops. Fresh integer values are unrestricted before those writes. -/
theorem tr_init_bl_zero {h : Heap} {id : Nat} {d : DeflateState} {b : Nat} {buf : Array UInt8}
    (base : TreesBase h id d b buf) :
    ∃ a1 a2 a3 result, «_tr_init» (some (.tab id)) h = .ok ((), setD h id result) ∧
      TreesInvAt (setD h id result) id result b buf ∧ result = ibRec (trInitRec id d) a1 a2 a3 ∧
      a1.size = 573 ∧ a2.size = 61 ∧ a3.size = 39 ∧ (∀ k, k < 19 → a3[k]!.fc = 0) := by
  obtain ⟨baseI, runI⟩ := trInitRec_inv base
  obtain ⟨a1, a2, a3, result, run, trees, fields, s1, s2, s3,
    _lit, _eob, _dist, zero, _lenL, _lenD, _lenB⟩ := init_block_spec0 baseI runI
  simp only [setD_setD] at run trees
  refine ⟨a1, a2, a3, result, ?_, trees, fields, s1, s2, s3, zero⟩
  have record : rdD h id = d := by simp [rdD, base.dstate]
  unfold «_tr_init»
  simp (disch := simp [base.dstate]) only [tr_static_init, bind_app, pure_app,
    sid_run base.dstate, md_run', rdD_setD_same, setD_setD, record]
  exact run

end Zlib.Trees.Proofs.Out
