import ZlibF.Proof.«inflate.c.header-actual-lenlens-source»
namespace Zlib.Inflate.Proofs.ActualHeader
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.HeaderPhaseView
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- The actual rejected CODES return follows the real BAD branch. The
premise is an observed translated installation, not a callee contract. -/
theorem rejected_codes_source
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s filled : InflateState}
    {l regs : IL} {next : CodePtr} {root : UInt32} {work : Array UInt16} {codes : Array Code}
    (E : Env c h r zs z s)
    (cut : runX (inflate_LENLENS c) l h = runX (llTail c) regs (setI h zs filled))
    (install : runX (llInstall c) regs (setI h zs filled) =
      .ok ((.ok (-1), {regs with ret := -1}), setI h zs {llPre zs filled with next := next, lenbits := root, work := work, codes := codes})) :
    ∃ i, runX (inflate_LENLENS c) l h =
      .ok ((.ok (), {regs with ret := -1}), tcBadHeap (setI h zs {llPre zs filled with next := next, lenbits := root, work := work, codes := codes}) r zs z
        {llPre zs filled with next := next, lenbits := root, work := work, codes := codes} i) := by
  let installed := {llPre zs filled with next := next, lenbits := root, work := work, codes := codes}
  have getZ : r.get (setI h zs installed) = some z := by rw [ZStreamRef.get_setI]; exact E.hz
  obtain ⟨i, _literal, bad⟩ := tcBadMode_run (c := c) "invalid code lengths set" lit_code_lengths E.strm E.st getZ (setI_istates_same h zs installed)
  refine ⟨i, ?_⟩
  rw [cut, llTail_install_eq, runX_bind, install]
  simp only [show ((-1 : Int32) != 0) = true from rfl, ite_true]
  simp [runX_bind, runX_lift, runX_pure, bad, installed]

/-- Unconditional actual LENLENS branch production. Current exhaustion
is a genuine wait; a complete alphabet produces an actual CODES call and
its computed zero or minus-one cases. Success automatically supplies CODELENS reading
observations, including empty-root rejection, BAD and partial input.
No independent Header/CodeLens/future parse or successful return is input. -/
theorem lenlens_branch_classifier
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8} {received : List Bool}
    (E : Env c h r zs z s) (origin : DefaultOriginState h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = LENLENS)
    (literalCount : 256 < s.nlen.toNat) (progress : LenlensProgress s l.hold l.bits received) :
    (∃ regs state used, used ≤ bs.length ∧
      runX (inflate_LENLENS c) l h = .ok ((.error Ex.leave, regs), setI h zs state) ∧
      DefaultOriginState (setI h zs state) r zs z state ∧ DispatchBuffers (setI h zs state) r regs (bs.drop used) ∧
      LenlensProgress state regs.hold regs.bits (received ++ bytesBits (bs.take used))) ∨
    (∃ (regs : IL) (used : Nat) (filled : InflateState) (ret : Int32)
      (next : CodePtr) (root : UInt32) (work : Array UInt16) (codes : Array Code),
      used ≤ bs.length ∧
      runX (do xwhile (llCond c) (llBody c); xwhile (lzCond c) (lzBody c)) l h = .ok ((.ok (), regs), setI h zs filled) ∧
      runX (llInstall c) regs (setI h zs filled) = .ok ((.ok ret, {regs with ret := ret}),
        setI h zs {llPre zs filled with next := next, lenbits := root, work := work, codes := codes}) ∧
      (ret = 0 ∨ ret = -1) ∧
      (ret = 0 ↔ Acceptable .codeLength (Zlib.Inftrees.Proofs.lensOf (fun k => (filled.lens.getD k 0).toNat) 19)) ∧
      (∀ tail, readCodeLenLens s.ncode.toNat ((received ++ bytesBits (bs.take used)) ++ tail) =
        some (Zlib.Inftrees.Proofs.lensOf (fun k => (filled.lens.getD k 0).toNat) 19, natBits regs.bits.toNat regs.hold.toNat ++ tail)) ∧
      (ret = -1 → ∃ i,
        runX (inflate_LENLENS c) l h = .ok ((.ok (), {regs with ret := -1}),
          tcBadHeap (setI h zs {llPre zs filled with next := next, lenbits := root, work := work, codes := codes}) r zs z
            {llPre zs filled with next := next, lenbits := root, work := work, codes := codes} i)) ∧
      (ret = 0 →
        let state := {llPre zs filled with next := next, lenbits := root, work := work, codes := codes, «have» := 0, mode := CODELENS}
        DefaultOriginState (setI h zs state) r zs z state ∧
        DispatchBuffers (setI h zs state) r {regs with ret := 0} (bs.drop used) ∧
        LengthTableFrame s state ∧ state.nlen = s.nlen ∧ state.ndist = s.ndist ∧ state.last = s.last ∧
        runX (inflate_LENLENS c) l h = runX (inflate_CODELENS c) {regs with ret := 0} (setI h zs state) ∧
        Nonempty (CodeReadObservation c (setI h zs state) r zs z state {regs with ret := 0} (bs.drop used)
          (Zlib.Inftrees.Proofs.lensOf (fun k => (filled.lens.getD k 0).toNat) 19)))) := by
  by_cases short : (stream l bs).length < 3 * (s.ncode.toNat - s.«have».toNat)
  · obtain ⟨regs, state, used, bound, actual, current, packet, _frame, _last, _lit, _dist, _code, _mode, nextProgress, _rest⟩ :=
      LaterHeader.lenlens_short_source E origin buffers mode progress short
    exact Or.inl ⟨regs, state, used, bound, actual, current, packet, nextProgress⟩
  have enough : 3 * (s.ncode.toNat - s.«have».toNat) ≤ (stream l bs).length := by omega
  obtain ⟨regs, used, filled, ret, next, root, work, codes, bound, headerRun, install, cut, kinds, precise, alphabetRead, ready⟩ :=
    lenlens_constructor_cases_source E origin buffers mode progress enough
  refine Or.inr ⟨regs, used, filled, ret, next, root, work, codes, bound, headerRun, install, kinds, precise, alphabetRead, ?_, ?_⟩
  · intro rejected
    apply rejected_codes_source E cut
    simpa only [rejected] using install
  · intro success
    obtain ⟨current, packet, _sizes, _wf, frame, _code, lit, dist, last, _pointer, contents, _empty,
      _cursor, _count, _put, _left, _out, _bits, _budget, actual⟩ := ready success
    let state := {llPre zs filled with next := next, lenbits := root, work := work, codes := codes, «have» := 0, mode := CODELENS}
    have env : Env c (setI h zs state) r zs z state := ⟨E.strm, E.st, current.good.live.hz, current.good.live.hs⟩
    have lower : 256 < state.nlen.toNat := by rw [lit]; exact literalCount
    have observation := code_read_classifier env current packet rfl lower contents
      (actualLengthPrefix_empty_for_alphabet rfl _)
    exact ⟨current, packet, frame, lit, dist, last, actual, observation⟩

#print axioms rejected_codes_source
#print axioms lenlens_branch_classifier
end Zlib.Inflate.Proofs.ActualHeader
