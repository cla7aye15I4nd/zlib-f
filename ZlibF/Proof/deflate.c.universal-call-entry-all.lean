import ZlibF.Proof.«deflate.c.universal-call-entry»
import ZlibF.Proof.«zutil.c»
import ZlibF.Spec.Public.Queries
import ZlibF.Spec.Functional.Api.Compress

/-!
# deflate.c: the entry phase of `deflate` for every status

Owner 2 of the deflate split (`deflate_call`). Batch C's entry lemmas
(`deflate.c.universal-call-entry`) cover an accepted call before the header. Here the entry phase
is stated for every status: the refusals with their message (`Z_STREAM_ERROR`), the full output
(`Z_BUF_ERROR`), and, with nothing pending, the repeated-flush refusal and the refusal of new
input after `Z_FINISH` (`Z_BUF_ERROR`), else the continuation with `last_flush` set.
-/

namespace Zlib.Deflate.Universal.Call
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Engine.Proofs
set_option autoImplicit false

/-! ## Messages -/

/-- A literal of the sources is a static string in every heap. -/
theorem static_of_table (h : Heap) {i : Nat} {text : String} (hi : strTable[i]? = some text) :
    StaticString h (.ref (.str i) 0) text := by
  have bound : i < strTable.size := (Array.getElem?_eq_some_iff.mp hi).1
  refine ⟨i, rfl, ?_, rfl⟩
  change staticStringBytes h i = some (strBytes text)
  rw [staticStringBytes, if_pos bound, hi]
  rfl

/-- `ERR_RETURN` stores the static text of the code in `msg` and returns the code. -/
theorem err_return_static {h : Heap} {r : ZStreamRef} {z : ZStream} (live : r.get h = some z) (err : Int32) :
    ∃ i, ERR_RETURN (some r) err h = .ok (err, r.put h { z with msg := .ref (.str i) 0 }) ∧
      strTable[i]? = some (Zlib.Zutil.Spec.errText err.toInt) := by
  obtain ⟨i, run, hi⟩ := Zlib.Zutil.Proofs.strLit_run h _ (Zlib.Zutil.Proofs.errText_lit err.toInt)
  refine ⟨i, ?_, hi⟩
  unfold ERR_RETURN ERR_MSG
  rw [Zlib.Zutil.Proofs.zError_eval]
  simp only [bind_app, run, Zlib.Zutil.Proofs.litHeap, zwr_eq, live, pure_app]

theorem stream_error_text : Zlib.Zutil.Spec.errText Z_STREAM_ERROR.toInt = errorText Z_STREAM_ERROR.toInt := by
  decide

theorem buf_error_text : Zlib.Zutil.Spec.errText Z_BUF_ERROR.toInt = errorText Z_BUF_ERROR.toInt := by
  decide

/-! ## `RANK` -/

/-- `RANK(f)` is `deflateRank f` for every value `last_flush` and an accepted flush take. -/
theorem rank_eq (f : Int32) (lower : -2 ≤ f.toInt) (upper : f.toInt ≤ 5) :
    RANK f = pure (Int32.ofInt (deflateRank f)) := by
  rw [rank_values f lower upper]
  by_cases five : f.toInt = 5
  · simp only [five, ite_true, deflateRank]
    rfl
  · have small : ¬ 4 < f.toInt ∨ f.toInt = 5 := by omega
    have notBig : ¬ 4 < f.toInt := by omega
    simp only [five, ite_false, deflateRank, notBig, Int.sub_zero, Int.mul_comm]

theorem rank_le_iff (f g : Int32) (fl : -2 ≤ f.toInt) (fu : f.toInt ≤ 5) (gl : -2 ≤ g.toInt) (gu : g.toInt ≤ 5) :
    (Int32.ofInt (deflateRank f) ≤ Int32.ofInt (deflateRank g)) ↔ deflateRank f ≤ deflateRank g := by
  have bf : -4 ≤ deflateRank f ∧ deflateRank f ≤ 10 := by unfold deflateRank; split <;> omega
  have bg : -4 ≤ deflateRank g ∧ deflateRank g ≤ 10 := by unfold deflateRank; split <;> omega
  rw [Int32.le_iff_toInt_le, Int32.toInt_ofInt_of_le (by omega) (by omega),
    Int32.toInt_ofInt_of_le (by omega) (by omega)]

/-! ## The refusals -/

/-- An invalid flush value: `Z_STREAM_ERROR`, nothing changed. -/
theorem entry_invalid {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    {flush : Int32} (good : DGood h r ds z d) (bad : flush.toInt < 0 ∨ 5 < flush.toInt)
    (k : DeflateStatePtr → M Int32) : entryPhase (some r) flush k h = .ok (Z_STREAM_ERROR, h) := by
  have checked := stateCheck_live good.live
  unfold entryPhase
  rcases bad with b | b
  · have low : flush < 0 := Int32.lt_iff_toInt_lt.mpr b
    simp [bind_app, pure_app, checked, low]
  · have high : flush > Z_BLOCK := Int32.lt_iff_toInt_lt.mpr b
    simp [bind_app, pure_app, checked, high]

/-- The common start of an accepted flush value. -/
theorem entry_valid_flags {flush : Int32} (lower : 0 ≤ flush.toInt) (upper : flush.toInt ≤ 5) :
    ¬ flush > Z_BLOCK ∧ ¬ flush < 0 := by
  constructor
  · intro bad
    have value : 5 < flush.toInt := Int32.lt_iff_toInt_lt.mp bad
    omega
  · rw [Int32.lt_iff_toInt_lt]; change ¬ flush.toInt < 0; omega

/-- A refused call with a valid flush value: `Z_STREAM_ERROR` with the message set. -/
theorem entry_refused {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    {flush : Int32} (good : DGood h r ds z d) (lower : 0 ≤ flush.toInt) (upper : flush.toInt ≤ 5)
    (refuses : DeflateRefuses z d flush) (k : DeflateStatePtr → M Int32) :
    ∃ i, entryPhase (some r) flush k h = .ok (Z_STREAM_ERROR, r.put h { z with msg := .ref (.str i) 0 }) ∧
      strTable[i]? = some (errorText Z_STREAM_ERROR.toInt) := by
  have checked := stateCheck_live good.live
  obtain ⟨high, low⟩ := entry_valid_flags lower upper
  obtain ⟨i, err, text⟩ := err_return_static good.live.hz Z_STREAM_ERROR
  refine ⟨i, ?_, text.trans (congrArg some stream_error_text)⟩
  have test : (z.next_out == .null || (z.avail_in != 0 && z.next_in == .null) ||
      (d.status == FINISH_STATE && flush != Z_FINISH)) = true := by
    unfold DeflateRefuses at refuses
    rcases refuses with b | b | b | ⟨null, pend⟩ | ⟨fin, ne⟩
    · omega
    · omega
    · simp [b]
    · simp [null, pend]
    · simp [fin, ne]
  unfold entryPhase
  simp only [bind_app, pure_app, checked, show ((0 : Int32) != 0) = false from rfl,
    high, low, decide_false, Bool.false_or, Bool.false_eq_true, ite_false,
    zrd_eq, good.live.hz, good.live.zst, castDeflateState,
    ldZStream_ok good.live.hz, ldDeflateState_tab good.live.hs, test, ite_true, err]

/-- An accepted call with a full output: `Z_BUF_ERROR` with the message set. -/
theorem entry_full {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    {flush : Int32} (good : DGood h r ds z d) (accepted : ¬ DeflateRefuses z d flush)
    (full : z.avail_out = 0) (k : DeflateStatePtr → M Int32) :
    ∃ i, entryPhase (some r) flush k h = .ok (Z_BUF_ERROR, r.put h { z with msg := .ref (.str i) 0 }) ∧
      strTable[i]? = some (errorText Z_BUF_ERROR.toInt) := by
  unfold DeflateRefuses at accepted
  have checked := stateCheck_live good.live
  obtain ⟨high, low⟩ := entry_valid_flags (flush := flush) (by omega) (by omega)
  obtain ⟨i, err, text⟩ := err_return_static good.live.hz Z_BUF_ERROR
  refine ⟨i, ?_, text.trans (congrArg some buf_error_text)⟩
  have test : (z.next_out == .null || (z.avail_in != 0 && z.next_in == .null) ||
      (d.status == FINISH_STATE && flush != Z_FINISH)) = false := by
    have out : z.next_out ≠ .null := fun e => accepted (Or.inr (Or.inr (Or.inl e)))
    have fin : ¬ (d.status = FINISH_STATE ∧ flush ≠ Z_FINISH) :=
      fun e => accepted (Or.inr (Or.inr (Or.inr (Or.inr e))))
    by_cases empty : z.avail_in = 0
    · by_cases st : d.status = FINISH_STATE
      · have : flush = Z_FINISH := Classical.byContradiction fun ne => fin ⟨st, ne⟩
        simp [out, empty, st, this]
      · simp [out, empty, st]
    · have inp : z.next_in ≠ .null := fun e => accepted (Or.inr (Or.inr (Or.inr (Or.inl ⟨e, empty⟩))))
      by_cases st : d.status = FINISH_STATE
      · have : flush = Z_FINISH := Classical.byContradiction fun ne => fin ⟨st, ne⟩
        simp [out, empty, inp, st, this]
      · simp [out, empty, inp, st]
  unfold entryPhase
  simp only [bind_app, pure_app, checked, show ((0 : Int32) != 0) = false from rfl,
    high, low, decide_false, Bool.false_or, Bool.false_eq_true, ite_false,
    zrd_eq, good.live.hz, good.live.zst, castDeflateState,
    ldZStream_ok good.live.hz, ldDeflateState_tab good.live.hs, test, full,
    show ((0 : UInt32) == 0) = true from rfl, ite_true, err]

/-! ## Nothing pending -/

/-- The no-progress refusals of an accepted call with output space and nothing pending. -/
def NoProgress (z : ZStream) (d : DeflateState) (flush : Int32) : Prop :=
  (z.avail_in = 0 ∧ deflateRank flush ≤ deflateRank d.last_flush ∧ flush ≠ Z_FINISH) ∨
    (d.status = FINISH_STATE ∧ z.avail_in ≠ 0)

/-- **The entry phase of an accepted call with output space and nothing pending**, for every
status: `Z_BUF_ERROR` with the message set exactly on `NoProgress`, else the rest of the call
with `last_flush := flush`. -/
theorem entry_empty_all {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    {flush : Int32} (good : DGood h r ds z d) (pending : d.pending = 0)
    (accepted : ¬ DeflateRefuses z d flush) (room : z.avail_out ≠ 0)
    (lastFlush : -2 ≤ d.last_flush.toInt ∧ d.last_flush.toInt ≤ 5) (k : DeflateStatePtr → M Int32) :
    (NoProgress z d flush → ∃ i, entryPhase (some r) flush k h =
        .ok (Z_BUF_ERROR, r.put (setD h ds { d with last_flush := flush }) { z with msg := .ref (.str i) 0 }) ∧
      strTable[i]? = some (errorText Z_BUF_ERROR.toInt)) ∧
    (¬ NoProgress z d flush →
      entryPhase (some r) flush k h = k (some (.tab ds)) (setD h ds { d with last_flush := flush })) := by
  unfold DeflateRefuses at accepted
  have flushLow : 0 ≤ flush.toInt := by omega
  have flushHigh : flush.toInt ≤ 5 := by omega
  have out : z.next_out ≠ .null := fun e => accepted (Or.inr (Or.inr (Or.inl e)))
  have fin : ¬ (d.status = FINISH_STATE ∧ flush ≠ Z_FINISH) :=
    fun e => accepted (Or.inr (Or.inr (Or.inr (Or.inr e))))
  have inputs : (z.avail_in != 0 && z.next_in == .null) = false := by
    by_cases empty : z.avail_in = 0
    · simp [empty]
    · have : z.next_in ≠ .null := fun e => accepted (Or.inr (Or.inr (Or.inr (Or.inl ⟨e, empty⟩))))
      simp [this]
  have finTest : (d.status == FINISH_STATE && flush != Z_FINISH) = false := by
    by_cases st : d.status = FINISH_STATE
    · have : flush = Z_FINISH := Classical.byContradiction fun ne => fin ⟨st, ne⟩
      simp [st, this]
    · simp [st]
  have checked := stateCheck_live good.live
  obtain ⟨high, low⟩ := entry_valid_flags flushLow flushHigh
  have h0 : r.get (setD h ds { d with last_flush := flush }) = some z := by
    rw [ZStreamRef.get_setD]; exact good.live.hz
  have rankF := rank_eq flush (by omega) flushHigh
  have rankO := rank_eq d.last_flush lastFlush.1 lastFlush.2
  have rankLe := rank_le_iff flush d.last_flush (by omega) flushHigh lastFlush.1 lastFlush.2
  obtain ⟨i, err, text⟩ := err_return_static h0 Z_BUF_ERROR
  have core : entryPhase (some r) flush k h =
      (if (z.avail_in == 0 && decide (deflateRank flush ≤ deflateRank d.last_flush) && flush != Z_FINISH) = true then
        .ok (Z_BUF_ERROR, r.put (setD h ds { d with last_flush := flush }) { z with msg := .ref (.str i) 0 })
      else if (d.status == FINISH_STATE && z.avail_in != 0) = true then
        .ok (Z_BUF_ERROR, r.put (setD h ds { d with last_flush := flush }) { z with msg := .ref (.str i) 0 })
      else k (some (.tab ds)) (setD h ds { d with last_flush := flush })) := by
    have err' := err
    simp only [pending, good.live.zst] at err'
    unfold entryPhase
    simp only [bind_app, pure_app, checked, show ((0 : Int32) != 0) = false from rfl,
      high, low, decide_false, Bool.false_or, Bool.false_eq_true, ite_false,
      zrd_eq, good.live.hz, good.live.zst, castDeflateState,
      ldZStream_ok good.live.hz, ldDeflateState_tab good.live.hs,
      show (z.next_out == .null) = false from beq_eq_false_iff_ne.mpr out,
      inputs, finTest, Bool.or_false,
      show (z.avail_out == 0) = false from beq_eq_false_iff_ne.mpr room,
      wrD_eq, good.live.hs, pending, show ((0 : UInt64) != 0) = false from rfl, rankF, rankO, rankLe]
    by_cases first : (z.avail_in == 0 && decide (deflateRank flush ≤ deflateRank d.last_flush) &&
        flush != Z_FINISH) = true
    · simp only [first, ite_true, err, err']
    · simp only [first, Bool.false_eq_true, ite_false, bind_app, pure_app, rdD_eq, setD_dstates_same, zrd_eq,
        ZStreamRef.get_setD, good.live.hz]
      by_cases second : (d.status == FINISH_STATE && z.avail_in != 0) = true
      · simp only [second, ite_true, err, err']
      · simp only [second, Bool.false_eq_true, ite_false]
  have text' := text.trans (congrArg some buf_error_text)
  constructor
  · intro np
    refine ⟨i, ?_, text'⟩
    rw [core]
    rcases np with ⟨e, le, ne⟩ | ⟨st, ne⟩
    · simp [e, le, ne]
    · by_cases first : (z.avail_in == 0 && decide (deflateRank flush ≤ deflateRank d.last_flush) &&
          flush != Z_FINISH) = true
      · simp only [first, ite_true]
      · simp [first, st, ne]
  · intro np
    rw [core]
    have first : (z.avail_in == 0 && decide (deflateRank flush ≤ deflateRank d.last_flush) &&
        flush != Z_FINISH) = false := by
      refine Bool.eq_false_iff.mpr fun yes => ?_
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne, ne_eq] at yes
      exact np (Or.inl ⟨yes.1.1, yes.1.2, yes.2⟩)
    have second : (d.status == FINISH_STATE && z.avail_in != 0) = false := by
      refine Bool.eq_false_iff.mpr fun yes => ?_
      simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at yes
      exact np (Or.inr ⟨yes.1, yes.2⟩)
    simp only [first, second, Bool.false_eq_true, ite_false]

/-- **The entry phase of an accepted call with pending output**, for every status (batch C's
`entry_accepted_pending` without its status premise). `flush_pending` delivers at least one
byte. If that fills the output, the call returns `Z_OK`; otherwise nothing is left pending, and
the call refuses new input after `Z_FINISH` (`Z_BUF_ERROR`) or continues. -/
theorem entry_pending_all {h : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream} {d : DeflateState}
    {buf : Array UInt8} {flush : Int32} (good : DGood h r ds z d)
    (trees : Zlib.Trees.Proofs.Out.TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (cursor : d.pending_out = d.pending_buf)
    (room : 8 * d.pending.toNat + d.bi_valid.toInt.toNat ≤ 8 * buf.size)
    (pending : d.pending ≠ 0) (accepted : ¬ DeflateRefuses z d flush) (avail : z.avail_out ≠ 0) :
    ∃ (produced : Nat) (after : Heap) (z' : ZStream) (d' : DeflateState),
      DGood after r ds z' d' ∧ StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧
      1 ≤ produced ∧ d'.status = d.status ∧
      flush_pending (some r) (setD h ds { d with last_flush := flush }) = .ok ((), after) ∧
      d' = { d with last_flush := flush, pending := d'.pending, pending_out := d'.pending_out,
                    bi_buf := d'.bi_buf, bi_valid := d'.bi_valid, bi_used := d'.bi_used } ∧
      ((z'.avail_out = 0 ∧ ∀ k, entryPhase (some r) flush k h =
          .ok (Z_OK, setD after ds { d' with last_flush := -1 })) ∨
       (d'.pending = 0 ∧
        (d.status = FINISH_STATE ∧ z.avail_in ≠ 0 → ∃ i, (∀ k, entryPhase (some r) flush k h =
          .ok (Z_BUF_ERROR, r.put after { z' with msg := .ref (.str i) 0 })) ∧
          strTable[i]? = some (errorText Z_BUF_ERROR.toInt)) ∧
        (¬ (d.status = FINISH_STATE ∧ z.avail_in ≠ 0) →
          ∀ k, entryPhase (some r) flush k h = k (some (.tab ds)) after))) := by
  unfold DeflateRefuses at accepted
  have flushLow : 0 ≤ flush.toInt := by omega
  have flushHigh : flush.toInt ≤ 5 := by omega
  have out : z.next_out ≠ .null := fun e => accepted (Or.inr (Or.inr (Or.inl e)))
  have inputs : (z.avail_in != 0 && z.next_in == .null) = false := by
    by_cases empty : z.avail_in = 0
    · simp [empty]
    · have : z.next_in ≠ .null := fun e => accepted (Or.inr (Or.inr (Or.inr (Or.inl ⟨e, empty⟩))))
      simp [this]
  have fin : ¬ (d.status = FINISH_STATE ∧ flush ≠ Z_FINISH) :=
    fun e => accepted (Or.inr (Or.inr (Or.inr (Or.inr e))))
  have finTest : (d.status == FINISH_STATE && flush != Z_FINISH) = false := by
    by_cases st : d.status = FINISH_STATE
    · have : flush = Z_FINISH := Classical.byContradiction fun ne => fin ⟨st, ne⟩
      simp [st, this]
    · simp [st]
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
  refine ⟨produced, after, z', d', goodA, buffersA, account, one, statusA, run, fields, ?_⟩
  unfold entryPhase
  simp only [bind_app, pure_app, checked, show ((0 : Int32) != 0) = false from rfl,
    high, low, decide_false, Bool.false_or, Bool.false_eq_true, ite_false,
    zrd_eq, good.live.hz, good.live.zst, castDeflateState,
    ldZStream_ok good.live.hz, ldDeflateState_tab good.live.hs,
    show (z.next_out == .null) = false from beq_eq_false_iff_ne.mpr out,
    inputs, Bool.or_false, finTest,
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
    have inA : z'.avail_in = z.avail_in :=
      UInt32.toNat_inj.mp (by have := account.2.2.1; omega)
    obtain ⟨i, err, text⟩ := err_return_static zAfter Z_BUF_ERROR
    have text' := text.trans (congrArg some buf_error_text)
    refine ⟨zero, fun bad => ⟨i, fun k => ?_, text'⟩, fun ok k => ?_⟩
    · simp [zrd_eq, zAfter, full, rdD_eq, dAfter, bind_app, statusA, inA, bad.1, bad.2, err]
    · simp [zrd_eq, zAfter, full, rdD_eq, dAfter, bind_app, statusA, inA]
      split
      · rename_i c
        exact absurd ⟨c.1, c.2⟩ ok
      · rfl

end Zlib.Deflate.Universal.Call
