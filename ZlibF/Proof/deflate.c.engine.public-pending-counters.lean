import ZlibF.Proof.«deflate.c.engine.pending-counters»
import ZlibF.Proof.«deflate.c.engine.public-pending»

/-! # Actual public pending-first exhaustion has exact totals -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- A real pending-first public return accounts for every written output byte. -/
theorem public_pending_exhausted_counter_execution {h : Heap} {r : ZStreamRef} {ds ob oo : Nat}
    {z : ZStream} {d : DeflateState} {before : List Bool} (flush : Int32)
    (good : DGood h r ds z d) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo) (input : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (flagLo : 0 ≤ flush.toInt) (flagHi : flush.toInt ≤ Z_BLOCK.toInt)
    (status : d.status = FINISH_STATE → flush = Z_FINISH) (positive : 0 < z.avail_out.toNat)
    (enough : z.avail_out.toNat ≤ d.pending.toNat) (low : d.bi_valid.toInt < 8)
    (pending : PendingBits h d before) :
    ∃ after z' result,
      deflate (some r) flush h = .ok (Z_OK, after) ∧ DGood after r ds z' result ∧
      StreamAccounting z z' 0 z.avail_out.toNat ∧ z'.total_in = z.total_in ∧
      z'.total_out = z.total_out + UInt64.ofNat z.avail_out.toNat := by
  let d0 := { d with last_flush := flush }
  let h0 := setD h ds d0
  have good0 := last_flush_good good flush
  have buffers0 := last_flush_buffers good buffers flush
  have pending0 := last_flush_pending_bits good pending flush
  obtain ⟨pb, produced, middle, z', result, written, remaining, base, run, goodM, buffersM, account,
    sizesM, storageM, count, pendingCount, lowM, fields, _reset, bytes, pendingM, bits⟩ :=
    flush_pending_resume_raw_bits good0 buffers0 pointer low pending0
  have amount : produced = z.avail_out.toNat := by rw [count]; exact Nat.min_eq_right enough
  rw [amount] at account pendingCount bytes
  have outputZero : z'.avail_out = 0 := UInt32.toNat_inj.mp (by
    have balance := account.2.2.2.1
    change z'.avail_out.toNat = 0
    omega)
  let final := setD middle ds { result with last_flush := -1 }
  have goodF := last_flush_good goodM (-1)
  have buffersF := last_flush_buffers goodM buffersM (-1)
  have pendingF := last_flush_pending_bits goodM pendingM (-1)
  have effects := flush_pending_low_run_counter_effects good0 buffers0 pointer low run goodM.live.hz account
  have publicRun : deflate (some r) flush h = .ok (Z_OK, final) := by
    have checked := stateCheck_live good.live
    have inputs : (z.avail_in != 0 && z.next_in == .null) = false := by
      by_cases empty : z.avail_in = 0
      · simp [empty]
      · simp [input empty]
    have outNonzero : z.avail_out ≠ 0 := by intro zero; rw [zero] at positive; contradiction
    have pendingNonzero : d.pending ≠ 0 := by intro zero; rw [zero] at enough; change z.avail_out.toNat ≤ 0 at enough; omega
    have flagUpper : ¬ flush > Z_BLOCK := by
      change ¬ Z_BLOCK < flush
      rw [Int32.lt_iff_toInt_lt]
      omega
    have flagLower : ¬ flush < 0 := by
      rw [Int32.lt_iff_toInt_lt]
      change ¬ flush.toInt < 0
      omega
    have finishAllowed : (d.status == FINISH_STATE && flush != Z_FINISH) = false := by
      by_cases finished : d.status = FINISH_STATE
      · simp [finished, status finished]
      · simp [finished]
    rw [public_deflate_source]
    simp only [bind_app, pure_app, checked, show ((0 : Int32) != 0) = false from rfl,
      flagUpper, flagLower,
      decide_false, Bool.false_or, Bool.false_eq_true, ite_false,
      zrd_eq, good.live.hz, good.live.zst, castDeflateState, ldZStream_ok good.live.hz,
      ldDeflateState_tab good.live.hs, inputs,
      show (z.next_out == .null) = false from by rw [pointer]; rfl,
      finishAllowed, show (z.avail_out == 0) = false from beq_eq_false_iff_ne.mpr outNonzero,
      wrD_eq, good.live.hs, show (d.pending != 0) = true from bne_iff_ne.mpr pendingNonzero,
      ite_true, run, goodM.live.hz, outputZero, BEq.rfl, goodM.live.hs]
    rfl
  exact ⟨final, z', { result with last_flush := -1 }, publicRun, goodF, account, effects⟩

end Zlib.Deflate.Engine.Proofs
