import ZlibF.Proof.«inflate.c.later-table-source»
namespace Zlib.Inflate.Proofs.LaterHeader
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.CumulativeParser
set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- An actual reader outcome retains initialized representation, buffers
and physical cursor. Outcome selection is established by the source. -/
theorem code_read_observed_packet
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s state : InflateState}
    {l regs : IL} {bs : List UInt8} {outcome : Except Ex Unit}
    (E : Env c h r zs z s) (before : DefaultOriginState h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = CODELENS)
    (actual : runX (clRead c) l h = .ok ((outcome, regs), setI h zs state)) :
    ∃ used, used ≤ bs.length ∧ DefaultOriginState (setI h zs state) r zs z state ∧
      DispatchBuffers (setI h zs state) r regs (bs.drop used) ∧
      regs.next = inputAdvance l.next used ∧ regs.have_.toNat + used = l.have_.toNat ∧
      regs.put = l.put ∧ regs.left = l.left ∧ regs.out_ = l.out_ ∧
      regs.bits.toNat ≤ max l.bits.toNat 21 := by
  obtain ⟨outcome0, regs0, after, stream, state0, used, bound, run, current,
    _config, packet, _sizes, cursor, count, put, left, total, bits, _budget, _modes, _complete⟩ :=
    clRead_default_state_complete E before.toDefaultStateJ buffers mode
  rw [actual] at run
  cases run
  have same : state0 = state := Option.some.inj (current.good.live.hs.symm.trans (setI_istates_same ..))
  subst state0
  have sameZ : stream = z := Option.some.inj (current.good.live.hz.symm.trans (by rw [ZStreamRef.get_setI]; exact E.hz))
  subst stream
  have origin := before.of_field_frame current (originFieldFrameX_clRead r c E.strm _ _ _ _ _ actual)
  exact ⟨used, bound, origin, packet, cursor, count, put, left, total, bits⟩

/-- The actual completed reader proves the current-input CodeLens parse;
no complete future payload is part of this observation. -/
theorem code_boundary_current_parse
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8} {decoded alphabet : List Nat} {future rest : List Bool}
    (E : Env c h r zs z s) (before : DefaultOriginState h r zs z s) (buffers : DispatchBuffers h r l bs)
    (mode : s.mode = CODELENS)
    (contents : Zlib.Inftrees.Proofs.CodeLengthContents s.codes 0 s.lenbits.toNat alphabet)
    (ordinary : ∀ index, index < 2 ^ s.lenbits.toNat → ∃ entry, s.codes[index]? = some entry ∧ entry.op = 0)
    (b : PayloadPhaseView.CodeBoundary c h r zs z s l bs decoded future rest) :
    CodeLens alphabet (s.nlen.toNat + s.ndist.toNat) (actualLengthPrefix s) (stream l bs) b.payload decoded := by
  obtain ⟨outcome, regs, after, state, used, run, _full, get, _bound, inv, _causal, completed⟩ :=
    clRead_exact_trace_format E.strm E.st E.hz E.hs before.good.inv.wf.1 mode before.lengths contents ordinary buffers.bits
  rw [b.readRun] at run
  cases run
  have same : state = b.readState := Option.some.inj (get.symm.trans (setI_istates_same ..))
  subst state
  have sameUsed : used = b.used := by
    have bound := b.bound
    have a := inv.have_eq
    have d := b.buffers.bits.have_eq
    simp only [List.length_drop] at a d
    omega
  subst used
  have notBad : b.readState.mode ≠ BAD := by rw [b.readFrame, mode]; decide
  have parsed := completed rfl notBad
  rw [b.matched, b.source] at parsed
  exact parsed

/-- An actual partial read retains a causal trace and the independent
remaining code-length parser on its real held/current/future stream. -/
theorem code_wait_parse
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s state : InflateState}
    {l regs : IL} {bs : List UInt8} {alphabet decoded : List Nat} {future rest : List Bool} {used : Nat}
    (E : Env c h r zs z s) (before : DefaultOriginState h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = CODELENS)
    (contents : Zlib.Inftrees.Proofs.CodeLengthContents s.codes 0 s.lenbits.toNat alphabet)
    (ordinary : ∀ index, index < 2 ^ s.lenbits.toNat → ∃ entry, s.codes[index]? = some entry ∧ entry.op = 0)
    (parsed : CodeLens alphabet (s.nlen.toNat + s.ndist.toNat) (actualLengthPrefix s) (stream l bs ++ future) rest decoded)
    (actual : runX (clRead c) l h = .ok ((.error Ex.leave, regs), setI h zs state))
    (stateMode : state.mode = CODELENS) (usedBound : used ≤ bs.length) (B : BitInv (setI h zs state) regs (bs.drop used)) :
    ∃ consumed, stream l bs = consumed ++ stream regs (bs.drop used) ∧
      ExactTrace alphabet (s.nlen.toNat + s.ndist.toNat) (actualLengthPrefix s) consumed (actualLengthPrefix state) ∧
      CodeLens alphabet (s.nlen.toNat + s.ndist.toNat) (actualLengthPrefix state) (stream regs (bs.drop used) ++ future) rest decoded := by
  obtain ⟨outcome, regs0, after, state0, used0, run, _full, get, _bound, inv, causal, _completed⟩ :=
    clRead_exact_trace_format E.strm E.st E.hz E.hs before.good.inv.wf.1 mode before.lengths contents ordinary buffers.bits
  rw [actual] at run
  cases run
  have same : state0 = state := Option.some.inj (get.symm.trans (setI_istates_same ..))
  subst state0
  have sameUsed : used0 = used := by
    have a := inv.have_eq
    have d := B.have_eq
    simp only [List.length_drop] at a d
    omega
  subst used0
  have notBad : state.mode ≠ BAD := by rw [stateMode]; decide
  obtain ⟨consumed, source, trace⟩ := causal notBad
  refine ⟨consumed, source, trace, trace.2 _ _ _ ?_⟩
  rw [source, List.append_assoc] at parsed
  exact parsed

#print axioms code_read_observed_packet
#print axioms code_boundary_current_parse
#print axioms code_wait_parse
end Zlib.Inflate.Proofs.LaterHeader
