import ZlibF.Proof.«inflate.c.global-output-credit-transport»
import ZlibF.Proof.«inflate.c.output-credit-append»
import ZlibF.Proof.«inflate.c.fast-future-representation-loaded-v2»

namespace Zlib.Inflate.Proofs.FunctionalEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.FunctionalTrailer Zlib.Inflate.Proofs.WrapperGlue
set_option autoImplicit false

/-- During payload decoding the current call's output is wholly
uncredited. Its physical byte ledger supplies the fast consumer's history
view by actual pointer/array uniqueness, including previous blocks. -/
theorem output_credit_history_view
    {h : Heap} {r : ZStreamRef} {z : ZStream} {s : InflateState} {l : IL}
    {bs prior emitted : List UInt8}
    (buffers : DispatchBuffers h r l bs)
    (output : OutputCredit h z s l prior emitted 0) :
    ∀ dest off array, l.put = .ref dest off → Space.get h dest = some array →
      ZlibF.Math.LZ77Copy.writtenBytes array off (l.out_.toNat - l.left.toNat) = emitted := by
  intro dest off array pointer get
  obtain ⟨ref, base, before, oldPointer, oldGet, _start, _bound, bytes⟩ := output.physical
  have same := oldPointer.symm.trans pointer
  cases same
  have sameArray : before = array := Option.some.inj (oldGet.symm.trans get)
  subst before
  have count := output.pending
  rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr buffers.output.count)] at count
  simp only [Nat.sub_zero] at count
  rwa [count]

/-- The internal installed flags packet supplies the fast distance query
fact for whichever actual table reference the callee resolves. -/
theorem InstalledQueryFlags.distance_resolved
    {h : Heap} {s : InflateState} (flags : InstalledQueryFlags h s) :
    ∀ ref offset codes, s.distcode = .ref ref offset → Space.get h ref = some codes →
      Zlib.Inftrees.Spec.FastTableFlags.QueryCompatible DISTS codes offset s.distbits.toNat := by
  intro ref offset codes pointer get
  obtain ⟨actualRef, actualOffset, actualCodes, actualPointer, actualGet, compatible⟩ := flags.2
  have same := actualPointer.symm.trans pointer
  cases same
  have sameCodes : actualCodes = codes := Option.some.inj (actualGet.symm.trans get)
  subst actualCodes
  exact compatible

/-- The valid-source projection of the causal ledger drives the actual
complete fast callee and LOAD. Its exact segment frame extends the full
physical/checksum output ledger, with arbitrary saved window and prior
current-call output. This is an internal execution prefix, not a public
END/completion theorem. -/
theorem PayloadLedger.fast_output_credit
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs dict prior emitted : List UInt8} {originalBits rest : List Bool}
    {L D : List Nat} {future target : List UInt8}
    (E : Env c h r zs z s)
    (ledger : PayloadLedger h r zs z s l bs dict prior emitted originalBits L D 0)
    (mode : DataTableMode s.mode)
    (parsed : Blocks dict [] (originalBits ++ bytesToBits (bs ++ future)) rest target)
    (fast : (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    let restored := setI (r.put h (leaveStream z l)) zs (leaveState s l)
    ∃ finished after stream state regs more,
      runX (RESTORE c.strm c.st) l h = .ok ((.ok (), l), restored) ∧
      C.run (Zlib.Inffast.inflate_fast (some r) l.out_) restored = .ok ((), finished) ∧
      runX (inflateAfterFast c) l finished = .ok ((.ok (), regs), after) ∧
      DefaultStateJ after r zs stream state ∧
      OutputCredit after stream state regs prior (emitted ++ more) 0 ∧
      prior ++ (emitted ++ more) <+: target := by
  dsimp only
  obtain ⟨bodyRest, bodyOutput, symbols, currentPrefix, bodyPrefix⟩ := ledger.current_symbols parsed
  obtain ⟨finished, after, stream, state, regs, ctx, array, off, made, next, more,
    restoreRun, callRun, loadRun, current, frame, outputPointer, advanced, bound,
    leftCount, outField, get, written, moreLength, nextAppend, nextPrefix,
    check, adler, wrap, flags⟩ :=
    ledger.representation.restore_fast_callee_loaded_v2 E mode
      ledger.queryFlags.distance_resolved
      (output_credit_history_view ledger.representation.2.1 ledger.output) symbols fast
  have seed := ledger.output.checksum
  have credit : AdlerCredit stream state (prior ++ emitted.take 0) := by
    exact ⟨wrap.trans seed.1, flags.trans seed.2.1, check.trans seed.2.2.1,
      adler.trans (seed.2.2.2.trans check.symm)⟩
  have count : (regs.out_ - regs.left).toNat = (l.out_ - l.left).toNat + more.length := by
    have oldBound := ledger.representation.2.1.output.count
    have newBound : regs.left.toNat ≤ regs.out_.toNat := by rw [outField]; omega
    rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr newBound),
      UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr oldBound), outField]
    omega
  obtain ⟨ref, base, oldArray, pointer, _oldGet, _start, _finish, _oldBytes⟩ := ledger.output.physical
  have newPointer : regs.put = .ref ref (base + made) := by
    rw [advanced, pointer]
    rfl
  have same := Ptr.ref.inj (outputPointer.symm.trans newPointer)
  have physical : ∃ ref off array,
      l.put = .ref ref off ∧ regs.put = .ref ref (off + more.length) ∧
      Space.get after ref = some array ∧ off + more.length ≤ array.size ∧
      ZlibF.Math.LZ77Copy.writtenBytes array (off + more.length) more.length = more := by
    refine ⟨ref, base, array, pointer, ?_, ?_, ?_, ?_⟩
    · simpa only [moreLength] using newPointer
    · simpa only [same.1] using get
    · rw [moreLength, ← same.2]
      exact bound
    · simpa only [moreLength, same.2] using written
  have output := ledger.output.restore.append_observed
    (by simpa only [moreLength] using frame) credit count physical
  have priorPrefix : prior <+: bodyOutput := (List.prefix_append prior emitted).trans currentPrefix
  have whole : prior ++ next <+: bodyOutput := by
    have whole := (List.prefix_append_right_inj prior).mpr nextPrefix
    rw [List.prefix_iff_eq_append.mp priorPrefix] at whole
    exact whole
  refine ⟨finished, after, stream, state, regs, more, restoreRun, callRun, loadRun,
    current, output, ?_⟩
  rw [nextAppend] at whole
  exact whole.trans bodyPrefix

end Zlib.Inflate.Proofs.FunctionalEpoch
