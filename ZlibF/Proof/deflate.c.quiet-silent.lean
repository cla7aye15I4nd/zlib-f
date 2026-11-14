import ZlibF.Proof.«deflate.c.universal-call-early»
import ZlibF.Proof.«deflate.c.universal-call-cont»
import ZlibF.Proof.«deflate.c.universal-call-strateval»
import ZlibF.Proof.«deflate.c.universal-history»
import ZlibF.Proof.«deflate.c.universal-sequence-safety»
import ZlibF.Proof.«deflate.c.universal-call-header-fact»
import ZlibF.Proof.«deflate.c.engine.overlay-header-ref»

/-!
# deflate.c: a quiet stream produces nothing (`DeflateQuiet`, clauses 3 and 4)

`gz_comp` calls `deflate` with no input and one flush value until a call produces nothing. The
potential `quietPhi` and the predicate `QuietD` read only the deflate state, so a rebuffering of the
stream (which keeps the state) keeps both. `QuietD flush d` holds when nothing is pending and the
last call already made this flush (`last_flush = flush`, not `Z_FINISH`), or the stream is finished
with its trailer written, or the state refuses this flush (`FINISH_STATE` with a flush other than
`Z_FINISH`). From such a state a call with no input moves no output byte (`quiet_silent`).
-/

namespace Zlib.Deflate.Universal.Quiet
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Engine.Proofs Zlib.Deflate.Universal.Call
set_option autoImplicit false

/-- The deflate state after a call with no input that ended with output room. -/
def QuietD (flush : Int32) (d : DeflateState) : Prop :=
  (d.pending = 0 ∧ ((d.last_flush = flush ∧ flush ≠ Z_FINISH) ∨
    (d.status = FINISH_STATE ∧ d.wrap.toInt ≤ 0))) ∨
  (d.status = FINISH_STATE ∧ flush ≠ Z_FINISH)

/-- The deflate state of a stream, if it has one. -/
def stateOf (h : Heap) (r : ZStreamRef) : Option DeflateState :=
  match r.get h with
  | some z => match z.state with
    | some (.deflate ds) => h.dstates ds
    | _ => none
  | none => none

theorem stateOf_eq {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) : stateOf h r = some d := by
  unfold stateOf
  rw [inv.good.live.hz]
  simp only [inv.good.live.zst]
  exact inv.good.live.hs

/-- `Quiet` of `DeflateQuiet`. -/
def QuietS (flush : Int32) (h : Heap) (r : ZStreamRef) : Prop :=
  ∃ d, stateOf h r = some d ∧ QuietD flush d

/-- Rebuffering keeps the state of a reachable stream. -/
theorem stateOf_rebuffer {h after : Heap} {r : ZStreamRef} (reach : StreamReachable .deflate h r)
    (edit : Rebuffer h after r) : stateOf after r = stateOf h r := by
  obtain ⟨ds, z, d, inv, _, _⟩ := reachable_inv_of (Call.sequence_facts_of tinyOverlay) reach
  obtain ⟨z', _, inv'⟩ := inv.rebuffer edit
  rw [stateOf_eq inv, stateOf_eq inv']

/-- **Clause 3 of `DeflateQuiet`** on the invariant: from a quiet state, a call with no input moves
no output byte. -/
theorem quiet_silent {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState} {flush : Int32}
    (inv : DInv h r ds z d) (facts : CallFacts d) (buffers : StreamBuffers h r)
    (q : QuietD flush d) (lower : 0 ≤ flush.toInt) (upper : flush.toInt ≤ 5) (empty : z.avail_in = 0) :
    ∃ rc after z', C.run (deflate (some r) flush) h = .ok (rc, after) ∧ r.get after = some z' ∧
      z'.avail_out = z.avail_out := by
  by_cases refused : DeflateRefuses z d flush
  · obtain ⟨m, run, _, _⟩ := call_refused inv buffers lower (by omega) refused
    exact ⟨_, _, { z with msg := m }, run, by rw [ZStreamRef.get_put, inv.good.live.hz]; rfl, rfl⟩
  by_cases full : z.avail_out = 0
  · obtain ⟨m, run, _, _⟩ := call_full inv buffers refused full
    exact ⟨_, _, { z with msg := m }, run, by rw [ZStreamRef.get_put, inv.good.live.hz]; rfl, rfl⟩
  rcases q with ⟨pend, ⟨lf, nf⟩ | ⟨fin, wrap⟩⟩ | ⟨fin, nf⟩
  · have np : NoProgress z d flush := Or.inl ⟨empty, by rw [lf]; exact Int.le_refl _, nf⟩
    obtain ⟨m, run, _, _⟩ := call_noprogress inv buffers pend refused full np
    exact ⟨_, _, { z with msg := m }, run,
      by rw [ZStreamRef.get_put, ZStreamRef.get_setD, inv.good.live.hz]; rfl, rfl⟩
  · have ff : flush = Z_FINISH := Classical.byContradiction fun ne =>
      refused (Or.inr (Or.inr (Or.inr (Or.inr ⟨fin, ne⟩))))
    have np : ¬ NoProgress z d flush := by
      rintro (⟨_, _, ne⟩ | ⟨_, ne⟩)
      · exact ne ff
      · exact ne empty
    let d1 : DeflateState := { d with last_flush := flush }
    have hs1 : (setD h ds d1).dstates ds = some d1 := setD_dstates_same _ _ _
    have hz1 : r.get (setD h ds d1) = some z := by rw [ZStreamRef.get_setD]; exact inv.good.live.hz
    have look : d.lookahead = 0 := facts.finishLook fin
    have np' : d1.wrap ≤ 0 := Int32.le_iff_toInt_le.mpr (by change d.wrap.toInt ≤ 0; exact wrap)
    have run : C.run (deflate (some r) flush) h = .ok (Z_STREAM_END, setD h ds d1) := by
      rw [C.run, deflate_phases, (entry_empty_all inv.good pend refused full inv.shape.lastFlush _).2 np,
        header_skip hs1 (Or.inr fin) flush, strategy_phase_eval hz1 hs1 flush]
      have cond : (z.avail_in != 0 || d1.lookahead != 0 || (flush != Z_NO_FLUSH && d1.status != FINISH_STATE)) =
          false := by
        simp [d1, empty, look, fin]
      rw [cond, ff]
      simp only [Bool.false_eq_true, ite_false]
      exact trailer_nonpos hs1 np'
    exact ⟨_, _, _, run, hz1, rfl⟩
  · exact absurd (Or.inr (Or.inr (Or.inr (Or.inr ⟨fin, nf⟩)))) refused

end Zlib.Deflate.Universal.Quiet

#print axioms Zlib.Deflate.Universal.Quiet.quiet_silent
#print axioms Zlib.Deflate.Universal.Quiet.stateOf_rebuffer
