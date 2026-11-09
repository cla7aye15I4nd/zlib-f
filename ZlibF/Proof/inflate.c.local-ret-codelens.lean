import ZlibF.Proof.«inflate.c.ret-completion»
import ZlibF.Proof.«inflate.c.local-construction»
import ZlibF.Proof.«inflate.c.ret-dispatch»
import ZlibF.Proof.«inflate.c.local-normal-mode-base»

namespace Zlib.Inflate.Local
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs
set_option autoImplicit false

/-- A table-constructor result is retained only on a normal BAD result.
Every CODELENS leave or continuing usable table has the original OK ret. -/
theorem inflate_CODELENS_ret_step
    {c : Ctx} {h after : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s returned : InflateState} {l regs : IL} {bs : List UInt8}
    {outcome : Except Ex Unit}
    (E : Env c h r zs z s) (invariant : LocalStateJ h cutoff r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = CODELENS) (initial : l.ret = Z_OK)
    (run : runX (inflate_CODELENS c) l h = .ok ((outcome, regs), after))
    (get : after.istates zs = some returned) :
    regs.ret = Z_OK ∨ (outcome = .ok () ∧ returned.mode = BAD) := by
  obtain ⟨decision, prefixRegs, prefixHeap, prefixZ, prefixS, used, _, read, current,
    config, packet, _, _, _, _, _, _, _, _, modes, complete⟩ :=
    clRead_default_state_complete E invariant buffers mode
  have saved := retBaseX_clRead Z_OK c _ _ _ _ _ initial read
  cases decision with
  | error exit =>
    have source := run
    rw [inflate_CODELENS_eq, runX_bind, read] at source
    cases source
    exact Or.inl saved
  | ok value =>
    cases value
    have cut : runX (inflate_CODELENS c) l h = runX (clTail c) prefixRegs prefixHeap := by
      rw [inflate_CODELENS_eq, runX_bind, read]
    have env : Env c prefixHeap r zs prefixZ prefixS :=
      ⟨E.strm, E.st, current.good.live.hz, current.good.live.hs⟩
    have done : prefixS.mode = CODELENS → prefixS.have.toNat = prefixS.nlen.toNat + prefixS.ndist.toNat := by
      intro selected
      rcases complete rfl with bad | full
      · rw [selected] at bad
        cases bad
      · exact full
    have format : prefixS.wrap = 0 ∨ prefixS.flags = 0 := by
      rw [config.2.2.1, config.2.2.2]
      exact invariant.construction_format (Or.inr (Or.inr mode))
    rcases clTail_default_state env current packet modes.symm done format with bad | ready
    · obtain ⟨ret, heap1, stream1, state1, source, final, _, badMode, _⟩ := bad
      have sameMode := xrun_state_eq (cut.trans source) run final.good.live.hs get
      have sameOutcome := xrun_outcome_eq (cut.trans source) run
      exact Or.inr ⟨sameOutcome.symm, by rw [← sameMode]; exact badMode⟩
    · obtain ⟨heap1, state1, _, _, _, _, _, _, source⟩ := ready
      by_cases trees : c.flush = Z_TREES
      · rw [ite_eq_left trees] at source
        have same := Except.ok.inj ((cut.trans source).symm.trans run)
        cases same
        exact Or.inl rfl
      · rw [ite_eq_right trees] at source
        have continuation := source.symm.trans (cut.symm.trans run)
        exact Or.inl (retBaseX_inflate_LEN_ Z_OK c _ _ _ _ _ rfl continuation)

#print axioms inflate_CODELENS_ret_step
end Zlib.Inflate.Local
