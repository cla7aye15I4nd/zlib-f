import ZlibF.Proof.«inflate.c.header-actual-code-complete-classifier»
namespace Zlib.Inflate.Proofs.ActualHeader
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs
set_option autoImplicit false
set_option maxHeartbeats 2000000

def CodeTailBranchOutcome (c : Ctx) (h : Heap) (r : ZStreamRef) (zs : Nat) (z : ZStream)
    (s : InflateState) (l : IL) (bs : List UInt8) (alphabet : List Nat)
    (observation : CodeReadObservation c h r zs z s l bs alphabet) : Prop :=
      (∃ exit, observation.outcome = .error exit) ∨
      (observation.outcome = .ok () ∧ observation.state.mode = BAD) ∨
      (observation.outcome = .ok () ∧ observation.state.mode = CODELENS ∧
        (Nonempty (TailRejected c observation.heap r zs observation.streamZ observation.state observation.regs) ∨
         ∃ ready : TailReady c observation.heap r zs observation.streamZ observation.state observation.regs (bs.drop observation.used),
           CodeLens alphabet (s.nlen.toNat + s.ndist.toNat) (actualLengthPrefix s) (stream l bs)
             (stream observation.regs (bs.drop observation.used)) (actualLengthPrefix observation.state) ∧
           Acceptable .litLen ((actualLengthPrefix observation.state).take observation.state.nlen.toNat) ∧
           Acceptable .dist ((actualLengthPrefix observation.state).drop observation.state.nlen.toNat) ∧
           runX (inflate_CODELENS c) l h = if c.flush = Z_TREES then
             .ok ((.error Ex.leave, {observation.regs with ret := 0}), setI observation.heap zs ready.tables.state)
             else runX (inflate_LEN_ c) {observation.regs with ret := 0} (setI observation.heap zs ready.tables.state)))

/-- Continue an already-produced actual reader observation automatically;
no repeated read or alphabet/table oracle is introduced by this adapter. -/
theorem CodeReadObservation.classify_tail
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8} {alphabet : List Nat}
    (observation : CodeReadObservation c h r zs z s l bs alphabet)
    (root : c.strm = some r) (stateRoot : c.st = some (.tab zs)) (literalCount : 256 < s.nlen.toNat) :
    CodeTailBranchOutcome c h r zs z s l bs alphabet observation := by
  unfold CodeTailBranchOutcome
  cases outcomeEq : observation.outcome with
  | error exit => exact Or.inl ⟨exit, rfl⟩
  | ok unit =>
    cases unit
    rcases observation.modes with code | bad
    · apply Or.inr ∘ Or.inr
      refine ⟨rfl, code, ?_⟩
      have complete : observation.state.«have».toNat = observation.state.nlen.toNat + observation.state.ndist.toNat := by
        rcases observation.complete outcomeEq with bad | done
        · rw [code] at bad; cases bad
        · exact done
      have full := observation.full.1
      obtain ⟨state0, _used0, get0, _bound0, _B0, _shape, _bits, frame, _size, _have, _values, _modes, _done⟩ := full
      have stateEq : state0 = observation.state := Option.some.inj (get0.symm.trans observation.origin.good.live.hs)
      have lower : 256 < observation.state.nlen.toNat := by rw [← stateEq, frame]; exact literalCount
      have env : Env c observation.heap r zs observation.streamZ observation.state :=
        ⟨root, stateRoot, observation.origin.good.live.hz, observation.origin.good.live.hs⟩
      rcases clTail_branch_classifier env observation.origin observation.buffers code lower complete with rejected | accepted
      · exact Or.inl rejected
      · obtain ⟨ready⟩ := accepted
        have parsed : CodeLens alphabet (s.nlen.toNat + s.ndist.toNat) (actualLengthPrefix s) (stream l bs)
            (stream observation.regs (bs.drop observation.used)) (actualLengthPrefix observation.state) := by
          rcases observation.grammar outcomeEq code with empty | parsed
          · obtain ⟨_zeroAlphabet, zeros, _badSource⟩ := empty
            have eob := ready.eob
            rw [zeros] at eob
            have haveLower : 256 < observation.state.«have».toNat := by omega
            simp [HasEndOfBlock, List.take_replicate, List.getD_eq_getElem?_getD, Nat.lt_min, lower, haveLower] at eob
          · exact parsed
        obtain ⟨validL, validD⟩ := ready.accepted_lengths complete
        have source : runX (inflate_CODELENS c) l h = runX (clTail c) observation.regs observation.heap := by
          have readNormal : runX (clRead c) l h = .ok ((.ok (), observation.regs), observation.heap) := by simpa only [outcomeEq] using observation.read
          rw [inflate_CODELENS_eq, runX_bind, readNormal]
        exact Or.inr ⟨ready, parsed, validL, validD, source.trans ready.actual⟩
    · exact Or.inr (Or.inl ⟨rfl, bad⟩)


#print axioms CodeReadObservation.classify_tail
end Zlib.Inflate.Proofs.ActualHeader
