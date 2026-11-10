import ZlibF.Proof.«inflate.c.header-actual-tail-classifier»
namespace Zlib.Inflate.Proofs.ActualHeader
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs
set_option autoImplicit false
set_option maxHeartbeats 2000000

theorem TailReady.accepted_lengths
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (ready : TailReady c h r zs z s l bs) (complete : s.«have».toNat = s.nlen.toNat + s.ndist.toNat) :
    Acceptable .litLen ((actualLengthPrefix s).take s.nlen.toNat) ∧
    Acceptable .dist ((actualLengthPrefix s).drop s.nlen.toNat) := by
  have slices := PayloadTables.actualLengthPrefix_payload_slices s complete
  have lit := ready.tables.lens.acceptable
  have dist := ready.tables.dists.acceptable
  change Acceptable .litLen (Zlib.Inftrees.Proofs.lensOf (fun k => (s.lens.getD k 0).toNat) s.nlen.toNat) at lit
  change Acceptable .dist (Zlib.Inftrees.Proofs.lensOf (fun k => (s.lens.getD (s.nlen.toNat + k) 0).toNat) s.ndist.toNat) at dist
  rw [← slices.1] at lit
  rw [← slices.2] at dist
  exact ⟨lit, dist⟩

/-- Automatic complete actual CODELENS branch classification. A ready
branch supplies independent current CodeLens syntax, EOB and acceptable
payload alphabets from actual reading/checking/construction. All malformed
and partial alternatives remain explicit; no valid-future oracle appears. -/
theorem code_reader_tail_classifier
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8} {alphabet : List Nat}
    (E : Env c h r zs z s) (origin : DefaultOriginState h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = CODELENS)
    (literalCount : 256 < s.nlen.toNat)
    (contents : Zlib.Inftrees.Proofs.CodeLengthContents s.codes 0 s.lenbits.toNat alphabet)
    (emptyPrefix : (∀ length ∈ alphabet, length = 0) → actualLengthPrefix s = List.replicate s.«have».toNat 0) :
    ∃ observation : CodeReadObservation c h r zs z s l bs alphabet,
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
             else runX (inflate_LEN_ c) {observation.regs with ret := 0} (setI observation.heap zs ready.tables.state))) := by
  obtain ⟨observation⟩ := code_read_classifier E origin buffers mode literalCount contents emptyPrefix
  refine ⟨observation, ?_⟩
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
        ⟨E.strm, E.st, observation.origin.good.live.hz, observation.origin.good.live.hs⟩
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

#print axioms TailReady.accepted_lengths
#print axioms code_reader_tail_classifier
end Zlib.Inflate.Proofs.ActualHeader
