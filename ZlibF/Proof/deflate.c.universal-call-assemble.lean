import ZlibF.Proof.«deflate.c.universal-call-contpend»
import ZlibF.Proof.«deflate.c.universal-call-bytes»
import ZlibF.Proof.«deflate.c.universal-call-entrykeep»
import ZlibF.Proof.«deflate.c.universal-ops-params-general»

/-!
# deflate.c: one `deflate` call, assembled

Owner 2 of the deflate split (`deflate_call`). The case split of `deflate` by its entry phase
(invalid flush, refusal, full output, no-progress refusal, nothing pending, output pending), each
case composed through the header, strategy and trailer phases, and the clauses of `Goal.deflate`
derived from the call segment, `KeepRel` and the return code.
-/

namespace Zlib.Deflate.Universal.Call
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Engine.Proofs
set_option autoImplicit false

/-- The clauses of an accepted call with output space that returns `Z_OK` or `Z_STREAM_END`. -/
theorem clauses_ok {h after : Heap} {r : ZStreamRef} {ds : Nat} {z z' : ZStream} {d d' : DeflateState}
    {flush rc : Int32} (inv : DInv h r ds z d) (buffers : StreamBuffers h r)
    (accepted : ¬ DeflateRefuses z d flush) (room : z.avail_out ≠ 0)
    (seg : Seg h after r ds d z z' d') (keep : Zlib.Deflate.Universal.Keep.KeepRel h after)
    (hz' : r.get after = some z') (rcs : rc = Z_OK ∨ rc = Z_STREAM_END)
    (endF : rc = Z_STREAM_END → flush = Z_FINISH ∧ d'.status = FINISH_STATE ∧ z'.avail_in = 0 ∧
      d'.pending = 0 ∧ d'.bi_valid = 0)
    (noBuf : ¬ (z.avail_in = 0 ∧ d.pending = 0 ∧ flush ≠ Z_FINISH ∧ deflateRank flush ≤ deflateRank d.last_flush))
    (progress : flush = Z_FINISH → ¬ (d.status = FINISH_STATE ∧ z.avail_in ≠ 0) →
      rc = Z_STREAM_END ∨ z'.avail_in ≠ z.avail_in ∨ z'.avail_out ≠ z.avail_out) :
    ∃ used out, DispatchCallClauses h r ds z d flush rc after z' d' used out ∧
      (∀ b, DeflateOwned ds d b ↔ DeflateOwned ds d' b) := by
  obtain ⟨u, p, ⟨⟨acc, tin, tout, bframe, live, nalloc⟩, _⟩, own⟩ := seg
  have out : z.next_out ≠ .null := fun e => accepted (by unfold DeflateRefuses; exact Or.inr (Or.inr (Or.inl e)))
  obtain ⟨xs, len, bytes⟩ := bytes_out buffers inv.good.live.hz acc bframe out
  subst len
  obtain ⟨z2, get2, msg2, data2⟩ := keep.stream r z inv.good.live.hz
  have same : z2 = z' := Option.some.inj (get2.symm.trans hz')
  subst same
  have ne1 : rc ≠ Z_STREAM_ERROR := by rcases rcs with e | e <;> rw [e] <;> decide
  have ne2 : rc ≠ Z_BUF_ERROR := by rcases rcs with e | e <;> rw [e] <;> decide
  refine ⟨u, xs, ⟨acc, bytes, tin, tout, Or.elim rcs (fun e => Or.inl e) (fun e => Or.inr (Or.inl e)),
    ⟨fun e => absurd e ne1, fun rf => absurd rf accepted⟩,
    fun b => absurd (by unfold DeflateRefuses; rcases b with b | b; exact Or.inl b; exact Or.inr (Or.inl b)) accepted,
    endF, fun e => absurd e ne2, fun _ full => absurd full room,
    fun _ _ _ => ⟨fun e => absurd e ne2, fun c => absurd c noBuf⟩,
    fun f _ _ nf => ?_, fun _ => msg2, fun e => absurd e ne2, fun e => absurd e ne1, data2, bframe, live, nalloc⟩,
    fun b => (own b).symm⟩
  rcases progress f nf with e | e | e
  · exact Or.inl e
  · right; left
    intro u0; subst u0
    apply e
    exact UInt32.toNat_inj.mp (by have := acc.2.2.1; omega)
  · right; right
    intro x0
    apply e
    have : xs.length = 0 := by rw [x0]; rfl
    exact UInt32.toNat_inj.mp (by have := acc.2.2.2.1; omega)

/-- The store of `msg` as a call segment. -/
theorem seg_msg {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (good : DGood h r ds z d) (buffers : StreamBuffers h r) (m : BPtr) :
    Seg h (r.put h { z with msg := m }) r ds d z { z with msg := m } d := by
  obtain ⟨fr, views, lv, na⟩ := message_heap good.live.hz m
  obtain ⟨acc, _, tin, tout, _, bframe, live, nalloc⟩ :=
    early_frame (z' := { z with msg := m }) (changed := fun b => StreamRoot r b ∨ DeflateOwned ds d b) buffers
      good.live.hz (frame_mono fr (fun b e => Or.inl e)) views lv na rfl
  exact ⟨0, 0, ⟨⟨acc, tin, tout, bframe, live, nalloc⟩, shape_put good.live.hz _⟩, fun _ => Iff.rfl⟩

/-- **One `deflate` call** from `DInv`, `HeaderInv` and `CallFacts`: the run, the invariant, the
header facts and the between-calls facts afterwards, every clause of `Goal.deflate` and the owned
blocks kept. Hypothesis: `TinyOverlay` (memLevel 1 and 2). -/
theorem deflate_call_full (tiny : Block.TinyOverlay) {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState} (inv : DInv h r ds z d) (header : HeaderInv d) (facts : CallFacts d)
    (buffers : StreamBuffers h r) (active : ActiveHeader h r) (flush : Int32) :
    ∃ rc after z' d' used out, C.run (Zlib.Deflate.deflate (some r) flush) h = .ok (rc, after) ∧
      DInv after r ds z' d' ∧ HeaderInv d' ∧ CallFacts d' ∧
      DispatchCallClauses h r ds z d flush rc after z' d' used out ∧
      (∀ b, DeflateOwned ds d b ↔ DeflateOwned ds d' b) := by
  -- the early returns change nothing in the state record
  by_cases bad : flush.toInt < 0 ∨ 5 < flush.toInt
  · obtain ⟨run, inv', cl, own, _⟩ := call_invalid inv buffers bad
    exact ⟨_, _, _, _, _, _, run, inv', header, facts, cl, own⟩
  by_cases refuses : DeflateRefuses z d flush
  · obtain ⟨m, run, inv', cl, own, _⟩ := call_refused inv buffers (by omega) (by omega) refuses
    exact ⟨_, _, _, _, _, _, run, inv', header, facts, cl, own⟩
  by_cases full : z.avail_out = 0
  · obtain ⟨m, run, inv', cl, own, _⟩ := call_full inv buffers refuses full
    exact ⟨_, _, _, _, _, _, run, inv', header, facts, cl, own⟩
  have hs := inv.good.live.hs
  by_cases pend : d.pending = 0
  · by_cases np : NoProgress z d flush
    · have lfNot : flush ≠ -2 := by
        intro e; unfold DeflateRefuses at refuses; rw [e] at refuses; exact refuses (Or.inl (by decide))
      obtain ⟨m, run, inv', cl, own, _⟩ := call_noprogress inv buffers pend refuses full np
      exact ⟨_, _, _, _, _, _, run, inv', HeaderInv.lastFlush header flush,
        { fresh := fun e => absurd e lfNot,
          freshStart := fun e => absurd e lfNot,
          finishSym := facts.finishSym, finishLook := facts.finishLook, finishBits := facts.finishBits },
        cl, own⟩
    · obtain ⟨rc, after, z', d', run0, inv', header', facts', buffers', seg, rcs, endF, prog⟩ :=
        cont_empty tiny inv header facts buffers active pend refuses full np
      have entry := (entry_empty_all inv.good pend refuses full inv.shape.lastFlush
        (fun s => headerPhase (some r) s flush (strategyPhase (some r) s flush (trailerPhase (some r) s flush)))).2 np
      have run : C.run (Zlib.Deflate.deflate (some r) flush) h = .ok (rc, after) := by
        rw [C.run, deflate_phases, entry]; exact run0
      have keep : Zlib.Deflate.Universal.Keep.KeepRel h after :=
        (Zlib.Deflate.Universal.Keep.KeepRel.upd_state hs _).trans
          (Zlib.Deflate.Universal.Keep.keep_after_entry _ _ _ _ _ _ run0)
      obtain ⟨used, out, cl, own⟩ := clauses_ok inv buffers refuses full seg keep inv'.good.live.hz rcs endF
        (fun c => np (Or.inl ⟨c.1, c.2.2.2, c.2.2.1⟩)) (fun f _ => prog f full)
      exact ⟨rc, after, z', d', used, out, run, inv', header', facts', cl, own⟩
  · obtain ⟨after1, z1, d1, produced, run1, hz1, hs1, _, acc, seg1, stEq, fullK, finK, contK⟩ :=
      cont_pending tiny entry_keep_any inv header facts buffers active pend refuses full
    have entry := entry_pending_eval inv.good refuses full pend run1 hz1 hs1
      (fun s => headerPhase (some r) s flush (strategyPhase (some r) s flush (trailerPhase (some r) s flush)))
    have keep1 : Zlib.Deflate.Universal.Keep.KeepRel h after1 :=
      (Zlib.Deflate.Universal.Keep.KeepRel.upd_state hs _).trans
        (Zlib.Deflate.Universal.Keep.keep_flush_pending _ _ _ _ run1)
    have noBuf : ¬ (z.avail_in = 0 ∧ d.pending = 0 ∧ flush ≠ Z_FINISH ∧
        deflateRank flush ≤ deflateRank d.last_flush) := fun c => pend c.2.1
    by_cases full1 : z1.avail_out = 0
    · obtain ⟨inv2, header2, facts2, buffers2, seg2⟩ := fullK full1
      have run : C.run (Zlib.Deflate.deflate (some r) flush) h =
          .ok (Z_OK, setD after1 ds { d1 with status := d1.status, last_flush := -1 }) := by
        rw [C.run, deflate_phases, entry, if_pos full1]
      have keep : Zlib.Deflate.Universal.Keep.KeepRel h (setD after1 ds { d1 with status := d1.status, last_flush := -1 }) :=
        keep1.trans (Zlib.Deflate.Universal.Keep.KeepRel.upd_state hs1 _)
      have hz2 : r.get (setD after1 ds { d1 with status := d1.status, last_flush := -1 }) = some z1 := by
        rw [ZStreamRef.get_setD]; exact hz1
      obtain ⟨used, out, cl, own⟩ := clauses_ok inv buffers refuses full seg2 keep hz2 (Or.inl rfl)
        (fun e => absurd e (by decide)) noBuf
        (fun _ _ => Or.inr (changed_full full full1))
      exact ⟨_, _, _, _, used, out, run, inv2, header2, facts2, cl, own⟩
    by_cases finIn : d1.status = FINISH_STATE ∧ z1.avail_in ≠ 0
    · obtain ⟨inv1, header1, facts1, buffers1⟩ := finK finIn.1
      obtain ⟨i, err, text⟩ := err_return_static hz1 Z_BUF_ERROR
      have run : C.run (Zlib.Deflate.deflate (some r) flush) h =
          .ok (Z_BUF_ERROR, r.put after1 { z1 with msg := .ref (.str i) 0 }) := by
        rw [C.run, deflate_phases, entry, if_neg full1, if_pos finIn]; exact err
      have seg := seg1.trans (seg_msg inv1.good buffers1 (.ref (.str i) 0)) inv.good buffers
      obtain ⟨u, p, ⟨⟨acc2, tin, tout, bframe, live, nalloc⟩, _⟩, own⟩ := seg
      have out0 : z.next_out ≠ .null := fun e => refuses (by unfold DeflateRefuses; exact Or.inr (Or.inr (Or.inl e)))
      obtain ⟨xs, len, bytes⟩ := bytes_out buffers inv.good.live.hz acc2 bframe out0
      subst len
      obtain ⟨z2, get2, _, data2⟩ := keep1.stream r z inv.good.live.hz
      have same2 : z2 = z1 := Option.some.inj (get2.symm.trans hz1)
      subst same2
      have ain : z2.avail_in = z.avail_in := UInt32.toNat_inj.mp (by have := acc.2.2.1; omega)
      have stFin : d.status = FINISH_STATE := stEq ▸ finIn.1
      have ainNe : z.avail_in ≠ 0 := ain ▸ finIn.2
      have used0 : u = 0 := by have := acc2.2.2.1; change z2.avail_in.toNat + u = z.avail_in.toNat at this; rw [ain] at this; omega
      have b1 : Z_BUF_ERROR ≠ Z_STREAM_ERROR := by decide
      have b2 : Z_BUF_ERROR ≠ Z_STREAM_END := by decide
      have b3 : Z_BUF_ERROR ≠ Z_OK := by decide
      refine ⟨_, _, _, _, u, xs, run, inv1.message _, header1, facts1,
        ⟨acc2, bytes, tin, tout, Or.inr (Or.inr (Or.inr rfl)), ⟨fun e => absurd e b1, fun rf => absurd rf refuses⟩,
        fun b => absurd (by unfold DeflateRefuses; rcases b with b | b; exact Or.inl b; exact Or.inr (Or.inl b)) refuses,
        fun e => absurd e b2, fun _ => ⟨used0, Or.inr ⟨stFin, ainNe⟩⟩, fun _ f => absurd f full,
        fun _ _ nf => absurd ⟨stFin, ainNe⟩ nf, fun _ _ _ nf => absurd ⟨stFin, ainNe⟩ nf,
        fun e => by rcases e with e | e; exact absurd e b3; exact absurd e b2,
        fun _ => static_of_table _ (text.trans (congrArg some buf_error_text)), fun e => absurd e b1,
        data2, bframe, live, nalloc⟩, fun b => (own b).symm⟩
    · obtain ⟨rc, after, z', d', run0, inv', header', facts', buffers', seg2, rcs, endF, prog⟩ := contK full1 finIn
      have run : C.run (Zlib.Deflate.deflate (some r) flush) h = .ok (rc, after) := by
        rw [C.run, deflate_phases, entry, if_neg full1, if_neg finIn]; exact run0
      have keep : Zlib.Deflate.Universal.Keep.KeepRel h after :=
        keep1.trans (Zlib.Deflate.Universal.Keep.keep_after_entry _ _ _ _ _ _ run0)
      obtain ⟨used, out, cl, own⟩ := clauses_ok inv buffers refuses full seg2 keep inv'.good.live.hz rcs endF noBuf
        (fun f _ => prog f full)
      exact ⟨rc, after, z', d', used, out, run, inv', header', facts', cl, own⟩

/-- **`SequenceFacts.deflateCall`** from `deflate_call_full`. -/
theorem deflate_call_of (tiny : Block.TinyOverlay) : DeflateCallFact := by
  intro h r ds z d inv header facts buffers active flush
  obtain ⟨rc, after, z', d', used, out, run, inv', _, _, cl, own⟩ :=
    deflate_call_full tiny inv header facts buffers active flush
  exact ⟨rc, after, z', d', used, out, run, inv', cl, own⟩

/-- **`SequenceFacts.deflateCalls`** from `deflate_call_full`: the between-calls facts after a call. -/
theorem deflate_calls_of (tiny : Block.TinyOverlay) : DeflateCallsFact := by
  intro h after r ds ds' z z' d d' flush rc inv header facts buffers active run inv2
  obtain ⟨rc1, after1, z1, d1, _, _, run1, inv1, _, facts1, _, _⟩ :=
    deflate_call_full tiny inv header facts buffers active flush
  have e := Except.ok.inj (run1.symm.trans run)
  obtain ⟨_, rfl⟩ := Prod.mk.inj e
  obtain ⟨_, _, rfl⟩ := inv1.unique inv2.good
  exact facts1

/-- The header facts after a call (for batch C's `deflateHeader`). -/
theorem deflate_call_header (tiny : Block.TinyOverlay) {h after : Heap} {r : ZStreamRef}
    {ds ds' : Nat} {z z' : ZStream} {d d' : DeflateState} {flush rc : Int32}
    (inv : DInv h r ds z d) (header : HeaderInv d) (facts : CallFacts d) (buffers : StreamBuffers h r)
    (active : ActiveHeader h r) (run : C.run (Zlib.Deflate.deflate (some r) flush) h = .ok (rc, after))
    (inv2 : DInv after r ds' z' d') : HeaderInv d' := by
  obtain ⟨rc1, after1, z1, d1, _, _, run1, inv1, header1, _, _, _⟩ :=
    deflate_call_full tiny inv header facts buffers active flush
  have e := Except.ok.inj (run1.symm.trans run)
  obtain ⟨_, rfl⟩ := Prod.mk.inj e
  obtain ⟨_, _, rfl⟩ := inv1.unique inv2.good
  exact header1

end Zlib.Deflate.Universal.Call
