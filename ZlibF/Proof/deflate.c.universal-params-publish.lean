import ZlibF.Proof.«deflate.c.universal-params-helpers»
import ZlibF.Proof.«deflate.c.universal-params-trees»

/-!
# deflate.c: the parameter frame for `flush_pending` and the block macros

Batch C of the deflate skeleton (`bound_before_output`). `flush_pending` loads the stream and the
state, copies the pending bytes and stores both records; the stores write records whose
parameters are those just loaded.
-/

namespace Zlib.Deflate.Universal.Params
open C Zlib.Deflate Zlib.Deflate.Spec
set_option autoImplicit false

/-- The part of `flush_pending` after `_tr_flush_bits`. -/
theorem exact_flush_publish (strm : ZStreamPtr) (s : DeflateStatePtr) :
    ExactM (do
      let z ← ldZStream strm
      let d ← ldDeflateState s
      let len : UInt32 := if d.pending > z.avail_out.toUInt64 then z.avail_out else d.pending.toUInt32
      if len == 0 then return
      memcpyB z.next_out d.pending_out len.toNat
      let no ← padd z.next_out len.toNat
      let po ← padd d.pending_out len.toNat
      stZStream strm { z with next_out := no, total_out := z.total_out + len.toUInt64, avail_out := z.avail_out - len }
      let pend := d.pending - len.toUInt64
      stDeflateState s { d with pending_out := po, pending := pend }
      if pend == 0 then wr s (fun d => { d with pending_out := d.pending_buf })) := by
  intro h value after run
  simp only [bind_app] at run
  cases strm with
  | none => cases run
  | some r =>
    cases getz : r.get h with
    | none => simp [ldZStream, getz] at run
    | some z =>
      simp only [ldZStream, getz] at run
      cases s with
      | none => cases run
      | some sr =>
        cases sr with
        | tab i =>
          cases getd : h.dstates i with
          | none => simp [ldDeflateState, DeflateStateRef.get, getd] at run
          | some d =>
            simp only [ldDeflateState, DeflateStateRef.get, getd] at run
            generalize (if d.pending > z.avail_out.toUInt64 then z.avail_out else d.pending.toUInt32) = len at run
            by_cases zero : (len == 0) = true
            · simp only [zero, ite_true, pure_app] at run
              cases run; exact ExactRel.refl h
            · simp only [zero, Bool.false_eq_true, ite_false, bind_app] at run
              cases e1 : Ptr.memcpy z.next_out d.pending_out len.toNat h with
              | error _ => simp [e1] at run
              | ok p1 =>
                rcases p1 with ⟨_, h1⟩
                simp only [e1] at run
                have rel1 := exact_ptr_memcpy _ _ _ h _ h1 e1
                cases e2 : padd z.next_out len.toNat h1 with
                | error _ => simp [e2] at run
                | ok p2 =>
                  rcases p2 with ⟨no, h2⟩
                  simp only [e2] at run
                  have rel2 := exact_padd _ _ h1 _ h2 e2
                  cases e3 : padd d.pending_out len.toNat h2 with
                  | error _ => simp [e3] at run
                  | ok p3 =>
                    rcases p3 with ⟨po, h3⟩
                    simp only [e3] at run
                    have rel3 := exact_padd _ _ h2 _ h3 e3
                    have rel13 := rel1.trans (rel2.trans rel3)
                    obtain ⟨z3, getz3, samez⟩ := rel13.2 r z getz
                    obtain ⟨d3, getd3, parsd⟩ := rel13.1 i d getd
                    have ro : r.isRo = false := by cases r <;> rfl
                    simp only [stZStream, getz3, ro, Bool.false_eq_true, ite_false] at run
                    have rel4 := exact_put_stream getz3
                      { z with next_out := no, total_out := z.total_out + len.toUInt64, avail_out := z.avail_out - len }
                      ⟨samez.state.symm, samez.zalloc.symm, samez.zfree.symm⟩
                    obtain ⟨d4, getd4, parsd4⟩ := rel4.1 i d3 getd3
                    simp only [stDeflateState, DeflateStateRef.get, getd4, DeflateStateRef.isRo] at run
                    rw [DeflateStateRef.put_tab getd4] at run
                    have rel5 := ExactRel.upd_state getd4 { d with pending_out := po, pending := d.pending - len.toUInt64 }
                      (by rw [parsd4, parsd]; rfl)
                    by_cases empty : (d.pending - len.toUInt64 == 0) = true
                    · simp only [empty, ite_true] at run
                      exact rel13.trans (rel4.trans (rel5.trans
                        (exact_wr _ (fun d => { d with pending_out := d.pending_buf }) (fun _ => rfl) _ _ _ run)))
                    · simp only [empty, Bool.false_eq_true, ite_false, pure_app] at run
                      cases run
                      exact rel13.trans (rel4.trans rel5)

theorem exact_flush_pending (strm : ZStreamPtr) : ExactM (flush_pending strm) := by
  unfold flush_pending
  refine ExactM.bind (exact_zrd _ _) (fun st => ExactM.bind (exact_castDeflateState st) (fun s => ?_))
  refine ExactM.bind (Zlib.Trees.ParamsProofs.exact__tr_flush_bits _) (fun _ => ?_)
  exact exact_flush_publish strm s

theorem exact_FLUSH_BLOCK_ONLY (s : DeflateStatePtr) (last : Int32) : ExactM (FLUSH_BLOCK_ONLY s last) := by
  unfold FLUSH_BLOCK_ONLY
  repeat' first
    | exact Zlib.Trees.ParamsProofs.exact__tr_flush_block _ _ _ _
    | exact exact_flush_pending _
    | x_step

theorem exact_FLUSH_BLOCK (s : DeflateStatePtr) (last : Int32) : ExactM (FLUSH_BLOCK s last) := by
  unfold FLUSH_BLOCK
  repeat' first
    | exact exact_FLUSH_BLOCK_ONLY _ _
    | x_step

theorem exact_finish_tail (s : DeflateStatePtr) (flush : Int32) : ExactM (finish_tail s flush) := by
  unfold finish_tail
  repeat' first
    | exact exact_FLUSH_BLOCK _ _
    | x_step

end Zlib.Deflate.Universal.Params
