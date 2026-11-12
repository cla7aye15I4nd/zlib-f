import ZlibF.Proof.«deflate.c.universal-call-keep-helpers»
import ZlibF.Proof.«deflate.c.universal-call-keep-trees»

/-!
# deflate.c: `KeepRel` for `flush_pending` and the block macros

Port of `deflate.c.universal-params-publish`. `flush_pending` loads the stream and the state, copies
the pending bytes and stores both records; the stream store keeps `msg` and `data_type` of the
record just loaded, which the copy before it does not change.
-/

namespace Zlib.Deflate.Universal.Keep
open C Zlib.Deflate Zlib.Deflate.Spec
set_option autoImplicit false

/-- A byte array change leaves every stream record as it is. -/
theorem stream_get_modify_B (h : Heap) (b : BRef) (f : Array UInt8 → Array UInt8) (r : ZStreamRef) :
    r.get (Space.modify h b f) = r.get h := by
  cases b <;> cases r <;> rfl

theorem stream_get_memcpy {dst src : BPtr} {n : Nat} {h h1 : Heap} {u : Unit}
    (run : Ptr.memcpy dst src n h = .ok (u, h1)) (r : ZStreamRef) : r.get h1 = r.get h := by
  unfold Ptr.memcpy at run
  repeat' first | split at run | (cases run; exact stream_get_modify_B _ _ _ _) | contradiction

theorem heap_padd {p q : BPtr} {n : Nat} {h h1 : Heap} (run : padd p n h = .ok (q, h1)) : h1 = h := by
  unfold padd Ptr.add at run
  repeat' first | split at run | (cases run; rfl) | contradiction

/-- The part of `flush_pending` after `_tr_flush_bits`. -/
theorem keep_flush_publish (strm : ZStreamPtr) (s : DeflateStatePtr) :
    KeepM (do
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
              cases run; exact KeepRel.refl h
            · simp only [zero, Bool.false_eq_true, ite_false, bind_app] at run
              cases e1 : Ptr.memcpy z.next_out d.pending_out len.toNat h with
              | error _ => simp [e1] at run
              | ok p1 =>
                rcases p1 with ⟨u1, h1⟩
                simp only [e1] at run
                have rel1 := keep_ptr_memcpy _ _ _ h _ h1 e1
                have getz1 : r.get h1 = some z := (stream_get_memcpy e1 r).trans getz
                cases e2 : padd z.next_out len.toNat h1 with
                | error _ => simp [e2] at run
                | ok p2 =>
                  rcases p2 with ⟨no, h2⟩
                  simp only [e2] at run
                  have h2eq := heap_padd e2
                  rw [h2eq] at run
                  cases e3 : padd d.pending_out len.toNat h1 with
                  | error _ => simp [e3] at run
                  | ok p3 =>
                    rcases p3 with ⟨po, h3⟩
                    simp only [e3] at run
                    have h3eq := heap_padd e3
                    rw [h3eq] at run
                    have ro : r.isRo = false := by cases r <;> rfl
                    simp only [stZStream, getz1, ro, Bool.false_eq_true, ite_false] at run
                    generalize hzn : ({ z with next_out := no, total_out := z.total_out + len.toUInt64, avail_out := z.avail_out - len } : ZStream) = zn at run
                    have rel4 : KeepRel h1 (r.put h1 zn) := by
                      rw [← hzn]
                      exact keep_put_stream getz1 _ ⟨rfl, rfl, rfl⟩
                    have dsEq : (r.put h1 zn).dstates = h1.dstates := by
                      cases r <;> simp only [ZStreamRef.put] <;> split <;> rfl
                    cases getd1 : h1.dstates i with
                    | none => simp [stDeflateState, DeflateStateRef.get, getd1, dsEq] at run
                    | some d4 =>
                      have getd4 : (r.put h1 zn).dstates i = some d4 := by rw [dsEq]; exact getd1
                      simp only [stDeflateState, DeflateStateRef.get, getd1, getd4, dsEq, DeflateStateRef.isRo,
                        Bool.false_eq_true, ite_false] at run
                      rw [DeflateStateRef.put_tab getd4] at run
                      have rel5 := KeepRel.upd_state getd4 { d with pending_out := po, pending := d.pending - len.toUInt64 }
                        ((rel1.trans rel4).gz_eq getd getd4).symm
                      by_cases empty : (d.pending - len.toUInt64 == 0) = true
                      · simp only [empty, ite_true] at run
                        exact rel1.trans (rel4.trans (rel5.trans
                          (keep_wr _ (fun d => { d with pending_out := d.pending_buf }) (fun _ => rfl) _ _ _ run)))
                      · simp only [empty, Bool.false_eq_true, ite_false, pure_app] at run
                        cases run
                        exact rel1.trans (rel4.trans rel5)

theorem keep_flush_pending (strm : ZStreamPtr) : KeepM (flush_pending strm) := by
  unfold flush_pending
  refine KeepM.bind (keep_zrd _ _) (fun st => KeepM.bind (keep_castDeflateState st) (fun s => ?_))
  refine KeepM.bind (Zlib.Trees.KeepProofs.keep__tr_flush_bits _) (fun _ => ?_)
  exact keep_flush_publish strm s

theorem keep_FLUSH_BLOCK_ONLY (s : DeflateStatePtr) (last : Int32) : KeepM (FLUSH_BLOCK_ONLY s last) := by
  unfold FLUSH_BLOCK_ONLY
  repeat' first
    | exact Zlib.Trees.KeepProofs.keep__tr_flush_block _ _ _ _
    | exact keep_flush_pending _
    | k_step

theorem keep_FLUSH_BLOCK (s : DeflateStatePtr) (last : Int32) : KeepM (FLUSH_BLOCK s last) := by
  unfold FLUSH_BLOCK
  repeat' first
    | exact keep_FLUSH_BLOCK_ONLY _ _
    | k_step

theorem keep_finish_tail (s : DeflateStatePtr) (flush : Int32) : KeepM (finish_tail s flush) := by
  unfold finish_tail
  repeat' first
    | exact keep_FLUSH_BLOCK _ _
    | k_step

end Zlib.Deflate.Universal.Keep
