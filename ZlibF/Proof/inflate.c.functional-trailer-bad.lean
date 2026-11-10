import ZlibF.Proof.«inflate.c.functional-trailer-splits»

namespace Zlib.Inflate.Proofs.FunctionalTrailerReject
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.WrapperGlue Zlib.Inflate.Proofs.FunctionalTrailer
open Zlib.Inflate.Proofs.FunctionalTrailerSplits
set_option autoImplicit false

/-- The actual rebased error leave keeps the fully committed checksum.
It cannot allocate a fresh window, double-credit output, or change the
DATA_ERROR return. -/
theorem leave_after_bad_adler
    {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs : List UInt8} {credited : List UInt8}
    (E : Env c h r zs z s) (origin : DefaultOriginState h r zs z s)
    (allocator : DefAlloc z) (packet : DispatchBuffers h r l bs) (bits : l.bits.toNat ≤ 39)
    (credit : AdlerCredit z s credited) (zero : l.out_ = l.left) (ret : l.ret = Z_DATA_ERROR) :
    ∃ after stream state, inflate_leave c l h = .ok (Z_DATA_ERROR, after) ∧
      DefaultOriginState after r zs stream state ∧ DefAlloc stream ∧ AdlerCredit stream state credited := by
  obtain ⟨ref, a, off, ptr, get, _, room, count, made, unowned⟩ :=
    callerRange_slow_output origin.good l packet.output.range packet.output.nonnull
      packet.output.count packet.output.produced
  have start : (l.out_ - l.left).toNat ≤ off := by rw [zero]; simp
  have written : ZlibF.Math.LZ77Copy.writtenBytes a off (l.out_ - l.left).toNat = [] := by
    rw [zero]; simp [ZlibF.Math.LZ77Copy.writtenBytes]
  obtain ⟨rc, after, stream, state, run, getZ, getS, outcome⟩ :=
    inflate_leave_adler_credit E origin.good allocator.1 bits credit ptr get start (by omega) written unowned
  have ended : rc = Z_DATA_ERROR := by
    rcases outcome with ordinary | failure
    · simpa only [ret, show (Z_DATA_ERROR == Z_OK) = false from rfl,
        Bool.and_false, Bool.false_eq_true, ite_false] using ordinary.1
    · rw [failure.1] at run
      exact False.elim (inflate_leave_zero_output_not_memory E origin.good allocator.1 origin.pending
        packet bits (Or.inr (Or.inr ret)) zero run)
  obtain ⟨otherRc, otherAfter, otherZ, otherS, otherRun, final, finalAlloc⟩ :=
    inflate_leave_default_origin E origin allocator packet bits
  have same := Except.ok.inj (otherRun.symm.trans run)
  cases same
  have sameZ : otherZ = stream := Option.some.inj (final.good.live.hz.symm.trans getZ)
  have sameS : otherS = state := Option.some.inj (final.good.live.hs.symm.trans getS)
  subst otherZ otherS
  refine ⟨after, stream, state, by simpa only [ended] using run, final, finalAlloc, ?_⟩
  rcases outcome with ordinary | failure
  · simpa only [List.append_nil] using ordinary.2
  · rw [ended] at failure
    exact False.elim ((by decide : Z_DATA_ERROR ≠ Z_MEM_ERROR) failure.1)

#print axioms leave_after_bad_adler

/-- A genuinely mismatching source checksum reaches BAD in CHECK, executes
its next real dispatch to DATA_ERROR, and performs complete leave with the
output checksum committed exactly once. No invalid-path callee contract
or desired mainwhile result is assumed. -/
theorem CHECK_mismatch_suffix
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l current : IL} {bs prior emitted : List UInt8} {credited : Nat}
    (E : Env c h r zs z s) (origin : DefaultOriginState h r zs z s)
    (allocator : DefAlloc z) (packet : DispatchBuffers h r l bs) (bits : l.bits.toNat ≤ 39)
    (mode : s.mode = CHECK) (ledger : OutputCredit h z s l prior emitted credited)
    (pull : runX (NEEDBITS 32) l h = .ok ((.ok (), current), h))
    (outField : current.out_ = l.out_) (leftField : current.left = l.left)
    (putField : current.put = l.put)
    (mismatch : ZSWAP32 current.hold ≠ (adler32 (prior ++ emitted)).toUInt64) :
    ∃ regs checked used after finalZ finalS,
      runX (xwhile (pure true) (inflate_dispatch c)) l h = .ok ((.error Ex.leave, regs), checked) ∧
      regs.ret = Z_DATA_ERROR ∧
      inflate_leave c regs checked = .ok (Z_DATA_ERROR, after) ∧
      DefaultOriginState after r zs finalZ finalS ∧ DefAlloc finalZ ∧
      AdlerCredit finalZ finalS (prior ++ emitted) ∧ used ≤ bs.length := by
  let zc := { z with total_out := z.total_out + (l.out_ - l.left).toUInt64, adler := (adler32 (prior ++ emitted)).toUInt64 }
  let sc := { s with total := s.total + (l.out_ - l.left).toUInt64, check := (adler32 (prior ++ emitted)).toUInt64 }
  let hc := setI (r.put h zc) zs sc
  obtain ⟨i, _literal, check⟩ := (CHECK_after_pull E ledger pull outField leftField putField).2 mismatch
  let badZ := { zc with msg := .ref (.str i) 0 }
  let badS := { sc with mode := BAD }
  let badH := tcBadHeap hc r zs zc sc i
  let badRegs := { current with out_ := l.left }
  let regs := { badRegs with ret := Z_DATA_ERROR }
  have step : runX (inflate_dispatch c) l h = .ok ((.ok (), badRegs), badH) :=
    (inflate_dispatch_CHECK E l mode).trans check
  have getZ : r.get badH = some badZ := by
    dsimp only [badH, tcBadHeap]
    rw [ZStreamRef.get_setI]
    apply ZStreamRef.get_put_same
    rw [ZStreamRef.get_setI]
    exact ZStreamRef.get_put_same E.hz _
  have getS : badH.istates zs = some badS := by dsimp only [badH, tcBadHeap]; rw [setI_istates_same]
  obtain ⟨currentOrigin, currentPacket⟩ := origin_packet_of_actual E origin packet bits step getZ getS
  let used := l.have_.toNat - badRegs.have_.toNat
  have usedBound : used ≤ bs.length := by dsimp only [used]; have count := packet.bits.have_eq; omega
  have env : Env c badH r zs badZ badS := ⟨E.strm, E.st, getZ, getS⟩
  have terminal : runX (inflate_dispatch c) badRegs badH = .ok ((.error Ex.leave, regs), badH) := by
    simpa [badS, terminalExit, terminalRegs, show BAD ≠ DONE from by decide, regs] using
      inflate_dispatch_terminal_run env badRegs (Or.inr (Or.inl rfl))
  have packet1 : DispatchBuffers badH r regs (bs.drop used) := by
    simpa only [badS, terminalRegs, show BAD ≠ DONE from by decide, ite_false, ite_true, regs, used] using
      (inflate_dispatch_terminal_boundary env currentOrigin.good currentOrigin.pending currentPacket
        (Or.inr (Or.inl rfl))).2.2.2.2.1
  have small : regs.bits.toNat ≤ 39 := by
    obtain ⟨_rr, _locals, _heap, _stream, _state, _used, _made, _bound, source,
      _current, _packet, _sizes, _next, _have, _put, _left, small, _rank⟩ :=
      inflate_dispatch_default_origin_state_rank E origin packet bits
    have same := Except.ok.inj (source.symm.trans step)
    cases same
    exact small
  have credit : AdlerCredit badZ badS (prior ++ emitted) :=
    ⟨ledger.checksum.1, ledger.checksum.2.1, rfl, rfl⟩
  have alloc : DefAlloc badZ := allocator
  obtain ⟨after, finalZ, finalS, leave, final, finalAlloc, finalCredit⟩ :=
    leave_after_bad_adler env currentOrigin alloc packet1 small credit
      (by change l.left = current.left; exact leftField.symm) rfl
  have loop := xwhile_run_chain (inflate_dispatch c)
    (fun j => if j = 0 then l else badRegs) (fun j => if j = 0 then h else badH)
    1 (by unfold fuel; decide) Ex.leave regs badH
    (by
      intro j bound
      have zero : j = 0 := by omega
      subst j
      simpa using step)
    (by simpa using terminal)
  exact ⟨regs, badH, used, after, finalZ, finalS, loop, rfl, leave, final, finalAlloc, finalCredit, usedBound⟩

#print axioms CHECK_mismatch_suffix
/-- Arbitrary-input CHECK soundness direction: a real complete trailer
pull followed by an actual ordinary CHECK exit forces equality with the
checksum of observed output. The equality is a conclusion, not an oracle. -/
theorem CHECK_observed_exit_checksum
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l current returned : IL} {prior emitted : List UInt8} {credited : Nat}
    (E : Env c h r zs z s) (ledger : OutputCredit h z s l prior emitted credited)
    (pull : runX (NEEDBITS 32) l h = .ok ((.ok (), current), h))
    (outField : current.out_ = l.out_) (leftField : current.left = l.left)
    (putField : current.put = l.put)
    (observed : runX (inflate_CHECK c) l h = .ok ((.error Ex.leave, returned), after)) :
    ZSWAP32 current.hold = (adler32 (prior ++ emitted)).toUInt64 := by
  by_cases matched : ZSWAP32 current.hold = (adler32 (prior ++ emitted)).toUInt64
  · exact matched
  · obtain ⟨i, _literal, rejected⟩ :=
      (CHECK_after_pull E ledger pull outField leftField putField).2 matched
    have impossible := xrun_outcome_eq rejected observed
    cases impossible

#print axioms CHECK_observed_exit_checksum

end Zlib.Inflate.Proofs.FunctionalTrailerReject
