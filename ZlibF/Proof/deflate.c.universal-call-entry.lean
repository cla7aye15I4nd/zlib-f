import ZlibF.Proof.«deflate.c.universal-call-phases»
import ZlibF.Proof.«deflate.c.engine.public-finish»
import ZlibF.Proof.«trees.c.universal-spec»

/-!
# deflate.c: the entry phase of an accepted call

Batch C (hand-over from batch D). `entryPhase` of an accepted call (`¬ DeflateRefuses`, output
space) on a stream still in `INIT_STATE` or `GZIP_STATE`: nothing is refused, `last_flush` is
set, and pending output, if any, is flushed first.
-/

namespace Zlib.Deflate.Universal.Call
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Engine.Proofs
set_option autoImplicit false

/-- `RANK(f)` for the flush values and the two `last_flush` values before a header. -/
theorem rank_values (f : Int32) (lower : -2 ≤ f.toInt) (upper : f.toInt ≤ 5) :
    RANK f = pure (if f.toInt = 5 then 1 else Int32.ofInt (2 * f.toInt)) := by
  have values : f = -2 ∨ f = -1 ∨ f = 0 ∨ f = 1 ∨ f = 2 ∨ f = 3 ∨ f = 4 ∨ f = 5 := by
    have : f.toInt = -2 ∨ f.toInt = -1 ∨ f.toInt = 0 ∨ f.toInt = 1 ∨
        f.toInt = 2 ∨ f.toInt = 3 ∨ f.toInt = 4 ∨ f.toInt = 5 := by omega
    simp only [← Int32.toInt_inj]
    exact this
  rcases values with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals rfl

/-- Before the header, the duplicate-flush refusal never applies: `RANK(flush) > RANK(last_flush)`. -/
theorem rank_after_reset (flush old : Int32) (flushLow : 0 ≤ flush.toInt) (flushHigh : flush.toInt ≤ 5)
    (reset : old = -2 ∨ old = -1) :
    (do let a ← RANK flush; let b ← RANK old; pure (decide (a ≤ b)) : M Bool) = pure false := by
  rw [rank_values flush (by omega) flushHigh]
  rcases reset with rfl | rfl
  all_goals
    rw [rank_values _ (by decide) (by decide)]
    have values : flush = 0 ∨ flush = 1 ∨ flush = 2 ∨ flush = 3 ∨ flush = 4 ∨ flush = 5 := by
      have : flush.toInt = 0 ∨ flush.toInt = 1 ∨ flush.toInt = 2 ∨ flush.toInt = 3 ∨
          flush.toInt = 4 ∨ flush.toInt = 5 := by omega
      simp only [← Int32.toInt_inj]
      exact this
    rcases values with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals rfl

/-- **The entry phase of an accepted call with nothing pending, before the header.** Nothing
is refused; the phase sets `last_flush` and continues. -/
theorem entry_accepted_empty {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    {flush : Int32} (good : DGood h r ds z d) (pending : d.pending = 0)
    (accepted : ¬ DeflateRefuses z d flush) (room : z.avail_out ≠ 0)
    (status : d.status = INIT_STATE ∨ d.status = GZIP_STATE) (reset : d.last_flush = -2 ∨ d.last_flush = -1)
    (k : DeflateStatePtr → M Int32) :
    entryPhase (some r) flush k h = k (some (.tab ds)) (setD h ds { d with last_flush := flush }) := by
  unfold DeflateRefuses at accepted
  have flushLow : 0 ≤ flush.toInt := by omega
  have flushHigh : flush.toInt ≤ 5 := by omega
  have out : z.next_out ≠ .null := fun e => accepted (Or.inr (Or.inr (Or.inl e)))
  have inputs : (z.avail_in != 0 && z.next_in == .null) = false := by
    by_cases empty : z.avail_in = 0
    · simp [empty]
    · have : z.next_in ≠ .null := fun e => accepted (Or.inr (Or.inr (Or.inr (Or.inl ⟨e, empty⟩))))
      simp [this]
  have notFinish : (d.status == FINISH_STATE) = false := by
    rcases status with st | st <;> rw [st] <;> rfl
  have checked := stateCheck_live good.live
  have high : ¬ flush > Z_BLOCK := by
    intro bad
    have value : 5 < flush.toInt := Int32.lt_iff_toInt_lt.mp bad
    omega
  have low : ¬ flush < 0 := by rw [Int32.lt_iff_toInt_lt]; change ¬ flush.toInt < 0; omega
  have flushValues : flush = 0 ∨ flush = 1 ∨ flush = 2 ∨ flush = 3 ∨ flush = 4 ∨ flush = 5 := by
    have : flush.toInt = 0 ∨ flush.toInt = 1 ∨ flush.toInt = 2 ∨ flush.toInt = 3 ∨
        flush.toInt = 4 ∨ flush.toInt = 5 := by omega
    simp only [← Int32.toInt_inj]
    exact this
  unfold entryPhase
  simp only [bind_app, pure_app, checked, show ((0 : Int32) != 0) = false from rfl,
    high, low, decide_false, Bool.false_or, Bool.false_eq_true, ite_false,
    zrd_eq, good.live.hz, good.live.zst, castDeflateState,
    ldZStream_ok good.live.hz, ldDeflateState_tab good.live.hs,
    show (z.next_out == .null) = false from beq_eq_false_iff_ne.mpr out,
    inputs, Bool.or_false, notFinish, Bool.false_and,
    show (z.avail_out == 0) = false from beq_eq_false_iff_ne.mpr room,
    wrD_eq, good.live.hs, pending, show ((0 : UInt64) != 0) = false from rfl,
    rdD_eq, setD_dstates_same, ZStreamRef.get_setD]
  rcases reset with old | old <;> rw [old] <;>
    rcases flushValues with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [RANK, chk32, isub, Bool.and_false, Bool.false_eq_true, ite_false, bind_app, pure_app] <;>
    rcases status with st | st <;> simp [st, rdD_eq, setD_dstates_same, zrd_eq, ZStreamRef.get_setD, good.live.hz,
      (by decide : INIT_STATE ≠ FINISH_STATE), (by decide : GZIP_STATE ≠ FINISH_STATE)]

/-- Writing `last_flush` keeps the engine invariants, the caller buffers and every byte. -/
theorem last_flush_engine {h : Heap} {r : ZStreamRef} {ds pb : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8} (v : Int32)
    (good : DGood h r ds z d) (trees : Zlib.Trees.Proofs.Out.TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) :
    let result : DeflateState := { d with last_flush := v }
    DGood (setD h ds result) r ds z result ∧
      Zlib.Trees.Proofs.Out.TreesInvAt (setD h ds result) ds result pb buf ∧
      StreamBuffers (setD h ds result) r := by
  let result : DeflateState := { d with last_flush := v }
  have inv : DStInv h ds result :=
    { good.inv with blocks := good.inv.blocks_keys rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl }
  have goodA := good.setD' (d' := result) rfl good.live.status inv (by trkeep)
  have treesA := trees_at_buffer goodA trees.base.pbuf trees.base.bytes
  have sizes := block_record_sizes good.live.hs (show result.depth = d.depth from rfl)
  have owned := stream_owned_keys good goodA rfl rfl rfl rfl
  have buffersA := stream_buffers_sizes good.live.hz goodA.live.hz buffers sizes owned (stream_accounting_zero z)
  exact ⟨goodA, treesA, buffersA⟩

/-- **The entry phase of an accepted call with pending output, before the header.**
`flush_pending` delivers at least one byte. If that fills the output, the call returns `Z_OK`;
otherwise nothing is left pending and the phase continues. -/
theorem entry_accepted_pending {h : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream} {d : DeflateState}
    {buf : Array UInt8} {flush : Int32} (good : DGood h r ds z d)
    (trees : Zlib.Trees.Proofs.Out.TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (cursor : d.pending_out = d.pending_buf)
    (room : 8 * d.pending.toNat + d.bi_valid.toInt.toNat ≤ 8 * buf.size)
    (pending : d.pending ≠ 0) (accepted : ¬ DeflateRefuses z d flush) (avail : z.avail_out ≠ 0)
    (status : d.status = INIT_STATE ∨ d.status = GZIP_STATE) :
    ∃ (produced : Nat) (after : Heap) (z' : ZStream) (d' : DeflateState),
      DGood after r ds z' d' ∧ StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧
      1 ≤ produced ∧ d'.status = d.status ∧
      flush_pending (some r) (setD h ds { d with last_flush := flush }) = .ok ((), after) ∧
      ((z'.avail_out = 0 ∧ ∀ k, entryPhase (some r) flush k h =
          .ok (Z_OK, setD after ds { d' with last_flush := -1 })) ∨
       (d'.pending = 0 ∧ ∀ k, entryPhase (some r) flush k h = k (some (.tab ds)) after)) := by
  unfold DeflateRefuses at accepted
  have flushLow : 0 ≤ flush.toInt := by omega
  have flushHigh : flush.toInt ≤ 5 := by omega
  have out : z.next_out ≠ .null := fun e => accepted (Or.inr (Or.inr (Or.inl e)))
  have inputs : (z.avail_in != 0 && z.next_in == .null) = false := by
    by_cases empty : z.avail_in = 0
    · simp [empty]
    · have : z.next_in ≠ .null := fun e => accepted (Or.inr (Or.inr (Or.inr (Or.inl ⟨e, empty⟩))))
      simp [this]
  have notFinish : (d.status == FINISH_STATE) = false := by
    rcases status with st | st <;> rw [st] <;> rfl
  have checked := stateCheck_live good.live
  have high : ¬ flush > Z_BLOCK := by
    intro bad
    have value : 5 < flush.toInt := Int32.lt_iff_toInt_lt.mp bad
    omega
  have low : ¬ flush < 0 := by rw [Int32.lt_iff_toInt_lt]; change ¬ flush.toInt < 0; omega
  obtain ⟨good0, trees0, buffers0⟩ := last_flush_engine (pb := pb) (buf := buf) flush good trees buffers
  let d0 : DeflateState := { d with last_flush := flush }
  obtain ⟨ob, pointer⟩ := Block.output_pointer_cases good buffers out
  have pointer0 : (∃ oo, z.next_out = .ref (.blk ob) oo) ∨ (∃ oo, z.next_out = .ref (.dstate_depth ob) oo) :=
    pointer
  have published : ∃ (produced : Nat) (after : Heap) (z' : ZStream) (d' : DeflateState),
      flush_pending (some r) (setD h ds d0) = .ok ((), after) ∧ DGood after r ds z' d' ∧
      StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧
      produced = min (d0.pending.toNat + d0.bi_valid.toInt.toNat / 8) z.avail_out.toNat ∧
      d'.pending.toNat + produced = d0.pending.toNat + d0.bi_valid.toInt.toNat / 8 ∧
      d' = { d0 with
        pending := d'.pending, pending_out := d'.pending_out, bi_buf := d'.bi_buf,
        bi_valid := d'.bi_valid, bi_used := d'.bi_used } := by
    rcases pointer0 with ⟨oo, ptr⟩ | ⟨oo, ptr⟩
    · obtain ⟨produced, after, z', d', _w, _rem, run, goodA, buffersA, account, _s, _st, copied, left,
        _low, _valid, fields, _b, _p, _o⟩ := flush_pending_raw_bits good0 trees0 buffers0 ptr cursor room
      exact ⟨produced, after, z', d', run, goodA, buffersA, account, copied, left, fields⟩
    · obtain ⟨produced, after, z', d', _w, _rem, run, goodA, buffersA, account, _s, _st, copied, left,
        _low, _valid, fields, _b, _p, _o, _bf⟩ := flush_pending_foreign_bits_frame good0 trees0 buffers0 ptr cursor room
      exact ⟨produced, after, z', d', run, goodA, buffersA, account, copied, left, fields⟩
  obtain ⟨produced, after, z', d', run, goodA, buffersA, account, copied, left, fields⟩ := published
  simp only [d0] at copied left
  have pendingPos : 1 ≤ d.pending.toNat := by
    have : d.pending.toNat ≠ 0 := fun e => pending (UInt64.toNat_inj.mp (by simpa using e))
    omega
  have availPos : 1 ≤ z.avail_out.toNat := by
    have : z.avail_out.toNat ≠ 0 := fun e => avail (UInt32.toNat_inj.mp (by simpa using e))
    omega
  have one : 1 ≤ produced := by
    rw [copied]
    change 1 ≤ min (d.pending.toNat + _) _
    omega
  have statusA : d'.status = d.status := by rw [fields]
  have zAfter : r.get after = some z' := goodA.live.hz
  have dAfter := goodA.live.hs
  have availAcc : z'.avail_out.toNat + produced = z.avail_out.toNat := account.2.2.2.1
  have run' : flush_pending (some r) (setD h ds { d with last_flush := flush }) = .ok ((), after) := run
  refine ⟨produced, after, z', d', goodA, buffersA, account, one, statusA, run, ?_⟩
  unfold entryPhase
  simp only [bind_app, pure_app, checked, show ((0 : Int32) != 0) = false from rfl,
    high, low, decide_false, Bool.false_or, Bool.false_eq_true, ite_false,
    zrd_eq, good.live.hz, good.live.zst, castDeflateState,
    ldZStream_ok good.live.hz, ldDeflateState_tab good.live.hs,
    show (z.next_out == .null) = false from beq_eq_false_iff_ne.mpr out,
    inputs, Bool.or_false, notFinish, Bool.false_and,
    show (z.avail_out == 0) = false from beq_eq_false_iff_ne.mpr avail,
    wrD_eq, good.live.hs, show (d.pending != 0) = true from bne_iff_ne.mpr pending, ite_true, run']
  by_cases full : z'.avail_out = 0
  · left
    refine ⟨full, fun k => ?_⟩
    simp [zrd_eq, zAfter, full, wrD_eq, dAfter, bind_app]
  · right
    have lt : produced < z.avail_out.toNat := by
      have : z'.avail_out.toNat ≠ 0 := fun e => full (UInt32.toNat_inj.mp (by simpa using e))
      omega
    have zero : d'.pending = 0 := by
      have m : produced = d.pending.toNat + d.bi_valid.toInt.toNat / 8 := by
        rw [copied]; change min (d.pending.toNat + _) _ = _; omega
      have : d'.pending.toNat = 0 := by
        have l : d'.pending.toNat + produced = d.pending.toNat + d.bi_valid.toInt.toNat / 8 := left
        omega
      exact UInt64.toNat_inj.mp (by simpa using this)
    refine ⟨zero, fun k => ?_⟩
    have stA : ¬ d'.status = FINISH_STATE := by
      rw [statusA]; rcases status with st | st <;> rw [st] <;> decide
    simp [zrd_eq, zAfter, full, rdD_eq, dAfter, stA, bind_app]

end Zlib.Deflate.Universal.Call
